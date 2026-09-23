#!/usr/bin/env python3
"""
The ELF writer: a koit object as the relocatable file libbpf loads.

    tools/elf.py UNIT.json -o UNIT.o

reads the document `koitc emit --json` wrote and writes an ELF64
relocatable for the BPF machine with what libbpf reads and nothing
more: one section per program kind holding its programs' words, each
program a function symbol; a relocation section per program section
with an entry against a map symbol for every map reference; `.maps`
as a BTF data section, one variable per map whose BTF type spells
out the map's type, key, value, and entries; `.BTF` with the key and
value types, `bpf_spin_lock` as the struct libbpf recognizes by
name; `license`; no `.BTF.ext`, since no line information is
claimed.

A map the compiler reads by direct value access, `array[1]` in the
source, has no `.maps` form: libbpf turns a relocation against a
`.maps` symbol into a map descriptor load, never a value pointer. It
is what libbpf does for global data, so such a map is a variable of
`.bss`, sized as its value, and the reference is relocated against
that variable as clang relocates a global: libbpf makes one internal
array map of the section and rewrites the load to the value pointer
at the variable's offset plus the offset the compiler put in the
instruction. The kernel then executes the same instruction the
loader over the system call gives it, with one map for all such
variables instead of one per name.

A kfunc call is an extern function in `.BTF` and a call relocation
against it; no declaration of the interface calls one yet, so a document with
a kfunc relocation is refused here, saying so.
"""

import argparse
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import koitobj  # noqa: E402

# ELF64 constants, include/uapi/linux/elf.h
EM_BPF = 247
ET_REL = 1
SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHT_STRTAB = 3
SHT_NOBITS = 8
SHT_REL = 9
SHF_WRITE = 1
SHF_ALLOC = 2
SHF_EXECINSTR = 4
STB_LOCAL = 0
STB_GLOBAL = 1
STT_NOTYPE = 0
STT_OBJECT = 1
STT_FUNC = 2
STT_SECTION = 3
R_BPF_64_64 = 1
R_BPF_64_32 = 10
BTF_FUNC_EXTERN = 2
BPF_PSEUDO_MAP_FD = 1


class Elf:
    """An ELF64 relocatable under construction: sections by index,
    symbols by index, and the string tables."""

    def __init__(self):
        self.sections = [{"name": "", "type": 0, "flags": 0, "data": b"", "link": 0, "info": 0,
                          "align": 0, "entsize": 0}]
        self.symbols = [{"name": "", "value": 0, "size": 0, "info": 0, "shndx": 0}]
        self.strtab = bytearray(b"\0")

    def string(self, s):
        if not s:
            return 0
        off = len(self.strtab)
        self.strtab += s.encode() + b"\0"
        return off

    def section(self, name, type_, flags, data, link=0, info=0, align=1, entsize=0):
        self.sections.append({"name": name, "type": type_, "flags": flags, "data": data,
                              "link": link, "info": info, "align": align, "entsize": entsize})
        return len(self.sections) - 1

    def index(self, name):
        for i, s in enumerate(self.sections):
            if s["name"] == name:
                return i
        raise KeyError(name)

    def symbol(self, name, value, size, bind, type_, shndx):
        self.symbols.append({"name": name, "value": value, "size": size,
                             "info": (bind << 4) | type_, "shndx": shndx})
        return len(self.symbols) - 1

    def build(self):
        # local symbols first, as the format requires
        order = sorted(range(len(self.symbols)), key=lambda i: (i != 0, self.symbols[i]["info"] >> 4 != STB_LOCAL, i))
        renumber = {old: new for new, old in enumerate(order)}
        symbols = [self.symbols[i] for i in order]
        first_global = next((i for i, s in enumerate(symbols) if s["info"] >> 4 != STB_LOCAL), len(symbols))
        # relocation entries were recorded with the old symbol numbers
        for s in self.sections:
            if s["type"] == SHT_REL:
                out = bytearray()
                for off in range(0, len(s["data"]), 16):
                    r_offset, r_info = struct.unpack_from("<QQ", s["data"], off)
                    sym, typ = r_info >> 32, r_info & 0xFFFFFFFF
                    out += struct.pack("<QQ", r_offset, (renumber[sym] << 32) | typ)
                s["data"] = bytes(out)
        symtab = b"".join(struct.pack("<IBBHQQ", self.string(s["name"]), s["info"], 0, s["shndx"],
                                      s["value"], s["size"]) for s in symbols)
        symtab_index = self.section(".symtab", SHT_SYMTAB, 0, symtab, link=0, info=first_global,
                                    align=8, entsize=24)
        strtab_index = self.section(".strtab", SHT_STRTAB, 0, bytes(self.strtab))
        self.sections[symtab_index]["link"] = strtab_index
        for s in self.sections:
            if s["type"] == SHT_REL:
                s["link"] = symtab_index
        shstrtab = bytearray(b"\0")
        name_off = {}
        for s in self.sections + [{"name": ".shstrtab"}]:
            if s["name"] and s["name"] not in name_off:
                name_off[s["name"]] = len(shstrtab)
                shstrtab += s["name"].encode() + b"\0"
        self.section(".shstrtab", SHT_STRTAB, 0, bytes(shstrtab))
        # lay the section contents out after the header
        ehdr_size, shdr_size = 64, 64
        pos = ehdr_size
        offsets = []
        body = bytearray()
        for s in self.sections:
            align = max(s["align"], 1)
            while (pos + len(body)) % align:
                body += b"\0"
            offsets.append(pos + len(body))
            if s["type"] != SHT_NOBITS:
                body += s["data"]
        while (pos + len(body)) % 8:
            body += b"\0"
        shoff = pos + len(body)
        shdrs = bytearray()
        for s, off in zip(self.sections, offsets):
            shdrs += struct.pack("<IIQQQQIIQQ", name_off.get(s["name"], 0), s["type"], s["flags"], 0,
                                 off if s["type"] != 0 else 0, len(s["data"]), s["link"], s["info"],
                                 s["align"], s["entsize"])
        ident = b"\x7fELF" + bytes([2, 1, 1, 0]) + bytes(8)
        ehdr = ident + struct.pack("<HHIQQQIHHHHHH", ET_REL, EM_BPF, 1, 0, 0, shoff, 0, ehdr_size, 0, 0,
                                   shdr_size, len(self.sections), self.index(".shstrtab"))
        return bytes(ehdr) + bytes(body) + bytes(shdrs)


def map_definition(btf, types, m):
    """The BTF type of a map's `.maps` variable: an anonymous struct
    whose members' pointed-to types carry the definition, the way
    libbpf reads a BTF-defined map."""
    u32 = btf.int("int", 4, signed=True)
    members = []
    off = 0

    def add(name, target):
        nonlocal off
        members.append((name, btf.ptr(target), off))
        off += 8
    add("type", btf.array(u32, m["type_id"]))
    if m["kind"] != "ringbuf":
        add("key", btf.of_type(types, m["key"], m["key"].get("name")))
        add("value", btf.of_type(types, m["value"], m["value"].get("name")))
    add("max_entries", btf.array(u32, m["entries"]))
    if m.get("flags"):
        add("map_flags", btf.array(u32, m["flags"]))
    values_off = None
    if m["kind"] == "prog_array":
        # the entries: an array of pointers to a function prototype,
        # which libbpf fills from the relocations against the programs
        proto = btf.func_proto(u32, [("ctx", btf.ptr(0))])
        slot = btf.ptr(proto)
        values_off = off
        members.append(("values", btf.array(slot, m["entries"]), off))
        off += 8 * m["entries"]
    return btf.struct("", off, members), off, values_off


def write(unit):
    elf = Elf()
    btf = koitobj.Btf()

    # the kfuncs called: an extern function each in BTF, listed in the
    # `.ksyms` data section, and an undefined symbol the calls relocate
    # against; libbpf resolves the name in the kernel's BTF and matches
    # the prototype by kind
    kfuncs = {}
    for p in unit.programs:
        for r in p["relocs"]:
            if r["kind"] == "kfunc" and r["name"] not in kfuncs:
                if "ret" not in r:
                    raise SystemExit(f"elf: {unit.name}: kfunc {r['name']} has no prototype in the document")
                kfuncs[r["name"]] = r
    kfunc_symbol = {}
    ksyms = []
    for name, r in kfuncs.items():
        try:
            proto = btf.func_proto(btf.ctype(r["ret"]), [(a, btf.ctype(t)) for t, a in r["args"]])
        except ValueError as e:
            raise SystemExit(f"elf: {unit.name}: kfunc {name}: {e}")
        ksyms.append(btf.func(name, proto, BTF_FUNC_EXTERN))
    if ksyms:
        btf.datasec(".ksyms", 0, [(f, 0, 0) for f in ksyms])

    # .maps: the declared maps; the direct ones are global data, in
    # `.rodata` when read-only, `.data` when initialized, `.bss` otherwise,
    # which libbpf turns into one map each with the flags of the section
    declared = [m for m in unit.maps if not m["direct"]]
    direct = [m for m in unit.maps if m["direct"]]
    maps_data = bytearray()
    maps_vars = []
    prog_slots = []   # (offset in .maps of the slot, program name)
    for m in declared:
        if m.get("data"):
            raise SystemExit(f"elf: {unit.name}: map {m['name']} has an initializer but is not "
                             "global data; libbpf cannot fill it from the object, the koit loader can")
        tid, size, values_off = map_definition(btf, unit.types, m)
        var = btf.var(m["name"], tid)
        maps_vars.append((var, len(maps_data), size, m["name"]))
        if values_off is not None:
            for slot, pname in enumerate(m.get("programs", [])):
                prog_slots.append((len(maps_data) + values_off + 8 * slot, pname))
        maps_data += bytes(size)
    if maps_vars:
        btf.datasec(".maps", len(maps_data), [(v, off, sz) for v, off, sz, _ in maps_vars])

    map_symbol = {}
    maps_idx = None
    if maps_vars:
        maps_idx = elf.section(".maps", SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, bytes(maps_data), align=8)
        for _, off, size, name in maps_vars:
            map_symbol[name] = elf.symbol(name, off, size, STB_GLOBAL, STT_OBJECT, maps_idx)

    def data_section(name, members, flags, nobits):
        """One global-data section: its variables laid out in order, the
        BTF data section naming them, and a symbol each."""
        if not members:
            return
        blob = bytearray()
        vars_ = []
        for m in members:
            align = max(unit.types.align(m["value"]), 8)
            while len(blob) % align:
                blob += b"\0"
            tid = btf.of_type(unit.types, m["value"], m["value"].get("name"))
            var = btf.var(m["name"], tid)
            size = m["value_size"] * m["entries"]
            contents = bytes.fromhex(m["data"]) if m.get("data") else b""
            if len(contents) > size:
                raise SystemExit(f"elf: {unit.name}: map {m['name']} has {len(contents)} bytes of "
                                 f"contents for {size}")
            vars_.append((var, len(blob), size, m["name"]))
            blob += contents + bytes(size - len(contents))
        btf.datasec(name, len(blob), [(v, off, sz) for v, off, sz, _ in vars_])
        idx = elf.section(name, SHT_NOBITS if nobits else SHT_PROGBITS, flags, bytes(blob), align=8)
        for _, off, size, mname in vars_:
            map_symbol[mname] = elf.symbol(mname, off, size, STB_GLOBAL, STT_OBJECT, idx)

    for m in direct:
        if m.get("access") == "wo":
            raise SystemExit(f"elf: {unit.name}: map {m['name']} is write-only global data, which "
                             "no section expresses; give it more than one entry")
    data_section(".rodata", [m for m in direct if m.get("access") == "ro"], SHF_ALLOC, False)
    data_section(".data", [m for m in direct if m.get("access") != "ro" and m.get("data")],
                 SHF_ALLOC | SHF_WRITE, False)
    data_section(".bss", [m for m in direct if m.get("access") != "ro" and not m.get("data")],
                 SHF_ALLOC | SHF_WRITE, True)

    # the programs, by section
    by_section = {}
    for p in unit.programs:
        by_section.setdefault(p["section"], []).append(p)
    for sec, progs in by_section.items():
        text = bytearray()
        rels = bytearray()
        for p in progs:
            base = len(text)
            words = koitobj.words_of(p)
            for r in p["relocs"]:
                i = r["index"]
                w = words[i]
                if r["kind"] == "kfunc":
                    # the words already hold clang's form, a pseudo call
                    # with an immediate of -1; the relocation names the
                    # extern, and libbpf rewrites the instruction
                    if r["name"] not in kfunc_symbol:
                        kfunc_symbol[r["name"]] = elf.symbol(r["name"], 0, 0, STB_GLOBAL, STT_NOTYPE, 0)
                    rels += struct.pack("<QQ", base + i * 8, (kfunc_symbol[r["name"]] << 32) | R_BPF_64_32)
                    continue
                if r["kind"] == "map_fd":
                    # libbpf sets the pseudo register and the descriptor
                    words[i] = w & 0xFFFFFFFF & ~(0xF << 12) | (BPF_PSEUDO_MAP_FD << 12)
                else:
                    # a direct value: the offset where libbpf reads an
                    # addend, the second word's immediate left to it
                    words[i] = (w & 0xFFFFFFFF & ~(0xF << 12)) | ((r["offset"] & 0xFFFFFFFF) << 32)
                    words[i + 1] = words[i + 1] & 0xFFFFFFFF
                rels += struct.pack("<QQ", base + i * 8, (map_symbol[r["map"]] << 32) | R_BPF_64_64)
            text += koitobj.insns_bytes(words)
            elf.symbol(p["name"], base, len(words) * 8, STB_GLOBAL, STT_FUNC, len(elf.sections))
        idx = elf.section(sec, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, bytes(text), align=8)
        if rels:
            elf.section(".rel" + sec, SHT_REL, 0, bytes(rels), info=idx, align=8, entsize=16)

    # a program array's entries: relocations in `.maps` against the
    # programs' symbols, which libbpf turns into descriptors at load
    if prog_slots:
        prog_symbol = {}
        for i, sym in enumerate(elf.symbols):
            prog_symbol[sym["name"]] = i
        rels = bytearray()
        for off, pname in prog_slots:
            if pname not in prog_symbol:
                raise SystemExit(f"elf: {unit.name}: program array names `{pname}`, which is not a program here")
            rels += struct.pack("<QQ", off, (prog_symbol[pname] << 32) | R_BPF_64_64)
        elf.section(".rel.maps", SHT_REL, 0, bytes(rels), info=maps_idx, align=8, entsize=16)

    # the function information: every function of a section in BTF, the
    # program static at instruction 0 and each global function at its
    # entry with its prototype, references non-null; `.BTF.ext` names
    # them per section, which the verifier needs for a global function
    funcs = {f["name"]: f for f in getattr(unit, "fns", [])}
    ext_secs = []
    for sec, progs in by_section.items():
        recs = []
        base = 0
        for p in progs:
            words = koitobj.words_of(p)
            main_proto = btf.func_proto(btf.int("int", 4, signed=True), [("ctx", btf.ptr(0))])
            recs.append((base, btf.func(p["name"], main_proto, 0)))
            for sp in p.get("subprograms", []):
                f = funcs.get(sp["name"])
                if f is None:
                    raise SystemExit(f"elf: {unit.name}: subprogram {sp['name']} has no prototype")
                params = []
                tags = []
                for i, prm in enumerate(f["params"]):
                    if prm["kind"] == "ref":
                        t = btf.ptr(btf.of_type(unit.types, prm["type"], prm["type"].get("name")))
                        tags.append(i)
                    else:
                        t = btf.of_type(unit.types, prm["type"], prm["type"].get("name"))
                    params.append((prm["name"], t))
                ret = btf.of_type(unit.types, f["ret"], f["ret"].get("name")) if f.get("ret") else 0
                proto = btf.func_proto(ret, params)
                fid = btf.func(sp["name"], proto, 1)
                for i in tags:
                    btf.decl_tag("arg:nonnull", fid, i)
                recs.append((base + 8 * sp["insn"], fid))
            base += 8 * len(words)
        ext_secs.append((sec, recs))
    if any(p.get("subprograms") for p in unit.programs):
        elf.section(".BTF.ext", SHT_PROGBITS, 0, btf.ext_blob(ext_secs), align=4)

    lic = unit.license.encode() + b"\0"
    idx = elf.section("license", SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, lic, align=1)
    elf.symbol("_license", 0, len(lic), STB_GLOBAL, STT_OBJECT, idx)
    elf.section(".BTF", SHT_PROGBITS, 0, btf.blob(), align=4)
    return elf.build()


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("object", help="the document koitc emit --json wrote")
    ap.add_argument("-o", "--output", help="the object file (default: UNIT.o beside the document)")
    a = ap.parse_args()
    unit = koitobj.Unit.load(a.object)
    out = a.output or os.path.splitext(a.object)[0] + ".o"
    with open(out, "wb") as f:
        f.write(write(unit))
    print(f"elf: {unit.name}: {len(unit.programs)} program(s), {len(unit.maps)} map(s) -> {out}")


if __name__ == "__main__":
    main()
