"""
The reader of koitc's interchange form, `koitc emit --json`, shared by
the loader, the ELF writer, and the runner's kernel stage: the
document, its types with their layouts, a BTF encoder for them, the
relocation patcher that puts map descriptors and kfunc ids into the
words, the report printer that prints a map's contents the way
`koitc run` does, and a reader of the running kernel's own BTF for
kfunc ids.

Nothing here reads Lean or the interface: every number a tool needs
is in the document.
"""

import json
import struct

BPF_PSEUDO_MAP_FD = 1
BPF_PSEUDO_MAP_VALUE = 2
BPF_PSEUDO_KFUNC_CALL = 2

# ------------------------------------------------------------ document

class Unit:
    def __init__(self, doc):
        if doc.get("koit") != 1:
            raise ValueError("not a koit object document (koit != 1)")
        self.doc = doc
        self.kernel = doc["kernel"]
        self.cpu = doc["cpu"]
        self.name = doc["unit"]
        self.license = doc["license"] or "GPL"
        self.types = Types(doc["types"])
        self.maps = doc["maps"]
        self.programs = doc["programs"]

    @staticmethod
    def load(path):
        with open(path) as f:
            return Unit(json.load(f))

    def map(self, name):
        for m in self.maps:
            if m["name"] == name:
                return m
        raise KeyError(f"no map {name}")


# ---------------------------------------------------------------- types

class Types:
    """The named types of a document, and the layout of any type
    description in it."""

    def __init__(self, decls):
        self.named = {d["name"]: d["type"] for d in decls}

    def resolve(self, t):
        while t["kind"] == "named":
            t = self.named[t["name"]]
        return t

    def size(self, t):
        t = self.resolve(t)
        k = t["kind"]
        if k == "int" or k == "be":
            return t["bits"] // 8
        if k == "bool":
            return 1
        return t["size"]

    def align(self, t):
        t = self.resolve(t)
        k = t["kind"]
        if k == "int" or k == "be":
            return t["bits"] // 8
        if k == "bool":
            return 1
        return t["align"]

    # the report printer of `koitc run`: structs by field, byte arrays
    # as hex, other arrays element by element, a slot as its name
    def format(self, t, bs, depth=32):
        if depth == 0:
            return "..."
        t = self.resolve(t)
        k = t["kind"]
        if k == "struct":
            parts = []
            for f in t["fields"]:
                n = self.size(f["type"])
                parts.append(f"{f['name']}: {self.format(f['type'], bs[f['offset']:f['offset'] + n], depth - 1)}")
            return "{ " + ", ".join(parts) + " }"
        if k == "array":
            elem = self.resolve(t["elem"])
            if elem["kind"] == "int" and not elem["signed"] and elem["bits"] == 8:
                shown = bs[:32].hex()
                more = f"... ({len(bs)} bytes)" if len(bs) > 32 else ""
                return "0x" + shown + more
            esz = self.size(elem)
            count = min(t["len"], 16)
            parts = [self.format(elem, bs[i * esz:(i + 1) * esz], depth - 1) for i in range(count)]
            return "[" + ", ".join(parts) + (", ..." if t["len"] > 16 else "") + "]"
        if k == "slot":
            return t["name"]
        if k == "be":
            return "0x" + bytes(bs).hex()
        if k == "bool":
            return "true" if bs[0] else "false"
        if k == "int":
            return str(int.from_bytes(bytes(bs), "little", signed=t["signed"]))
        return "?"


# ------------------------------------------------------------------ BTF

BTF_MAGIC = 0xEB9F
BTF_KIND_INT = 1
BTF_KIND_PTR = 2
BTF_KIND_ARRAY = 3
BTF_KIND_STRUCT = 4
BTF_KIND_FWD = 7
BTF_KIND_FUNC = 12
BTF_KIND_FUNC_PROTO = 13
BTF_KIND_VAR = 14
BTF_KIND_DATASEC = 15
BTF_INT_SIGNED = 1 << 24
BTF_INT_BOOL = 1 << 26


class Btf:
    """A BTF blob under construction: types by id from 1, and the
    string table. Named types are added once."""

    def __init__(self):
        self.types = []          # list of (bytes of btf_type, bytes of extra)
        self.strings = bytearray(b"\0")
        self.by_key = {}

    def string(self, s):
        if not s:
            return 0
        b = s.encode() + b"\0"
        i = self.strings.find(b)
        if i >= 0 and (i == 0 or self.strings[i - 1] == 0):
            return i
        off = len(self.strings)
        self.strings += b
        return off

    def add(self, name, kind, vlen, size_or_type, extra=b"", kind_flag=0):
        info = (kind << 24) | (vlen & 0xffff) | (kind_flag << 31)
        self.types.append((struct.pack("<III", self.string(name), info, size_or_type), extra))
        return len(self.types)

    def int(self, name, size, signed=False, boolean=False):
        key = ("int", name)
        if key in self.by_key:
            return self.by_key[key]
        enc = (BTF_INT_SIGNED if signed else 0) | (BTF_INT_BOOL if boolean else 0) | (size * 8)
        self.by_key[key] = self.add(name, BTF_KIND_INT, 0, size, struct.pack("<I", enc))
        return self.by_key[key]

    def array(self, elem, n):
        idx = self.int("__ARRAY_SIZE_TYPE__", 4)
        return self.add("", BTF_KIND_ARRAY, 0, 0, struct.pack("<III", elem, idx, n))

    def struct(self, name, size, members):
        """members: (name, type id, byte offset)."""
        extra = b"".join(struct.pack("<III", self.string(n), t, off * 8) for n, t, off in members)
        return self.add(name, BTF_KIND_STRUCT, len(members), size, extra)

    def ptr(self, t):
        return self.add("", BTF_KIND_PTR, 0, t)

    def fwd(self, name, union=False):
        key = ("fwd", name)
        if key not in self.by_key:
            self.by_key[key] = self.add(name, BTF_KIND_FWD, 0, 0, kind_flag=1 if union else 0)
        return self.by_key[key]

    def func_proto(self, ret, params):
        """params: (name, type id)."""
        extra = b"".join(struct.pack("<II", self.string(n), t) for n, t in params)
        return self.add("", BTF_KIND_FUNC_PROTO, len(params), ret, extra)

    def func(self, name, proto, linkage=0):
        """A function; the linkage, static, global, or extern, is where
        a struct member count would be."""
        return self.add(name, BTF_KIND_FUNC, linkage, proto)

    def ctype(self, s):
        """The BTF id of a C type as the kernel side spells it: a
        scalar, `void`, or a pointer to one of those or to a struct or
        union named by a forward declaration. libbpf compares a kfunc
        extern's prototype with the kernel's by kind and pointee, so
        this much is what the match needs."""
        s = s.strip()
        stars = 0
        while s.endswith("*"):
            stars += 1
            s = s[:-1].strip()
        words = [w for w in s.split() if w not in ("const", "volatile", "__restrict", "restrict")]
        s = " ".join(words)
        if s == "void":
            t = 0
        elif s.startswith("struct ") or s.startswith("union "):
            t = self.fwd(s.split(None, 1)[1], union=s.startswith("union "))
        elif s.startswith("enum "):
            t = self.int("int", 4, signed=True)
        elif s in ("bool", "_Bool"):
            t = self.int("bool", 1, boolean=True)
        else:
            sizes = {"char": 1, "short": 2, "int": 4, "long": 8, "long long": 8, "size_t": 8,
                     "u8": 1, "u16": 2, "u32": 4, "u64": 8, "s8": 1, "s16": 2, "s32": 4, "s64": 8,
                     "__u8": 1, "__u16": 2, "__u32": 4, "__u64": 8, "__s8": 1, "__s16": 2, "__s32": 4, "__s64": 8,
                     "unsigned char": 1, "unsigned short": 2, "unsigned int": 4, "unsigned long": 8,
                     "unsigned long long": 8, "unsigned": 4, "uintptr_t": 8, "intptr_t": 8, "ssize_t": 8}
            if s not in sizes:
                raise ValueError(f"no BTF for the C type `{s}`")
            signed = not (s.startswith("u") or s.startswith("__u") or s.startswith("unsigned") or s == "size_t")
            t = self.int(s.replace(" ", "_"), sizes[s], signed)
        for _ in range(stars):
            t = self.ptr(t)
        return t

    def var(self, name, t, linkage=1):
        return self.add(name, BTF_KIND_VAR, 0, t, struct.pack("<I", linkage))

    def datasec(self, name, size, vars_):
        """vars_: (var type id, offset, size)."""
        extra = b"".join(struct.pack("<III", v, off, sz) for v, off, sz in vars_)
        return self.add(name, BTF_KIND_DATASEC, len(vars_), size, extra)

    def of_type(self, types, t, name=None):
        """The BTF id of a koit type description."""
        t0 = t
        if t["kind"] == "named":
            name = t["name"]
            key = ("named", name)
            if key in self.by_key:
                return self.by_key[key]
            t = types.resolve(t)
        k = t["kind"]
        if k == "int":
            n = ("s" if t["signed"] else "u") + str(t["bits"])
            return self.int(n, t["bits"] // 8, t["signed"])
        if k == "be":
            return self.int("u" + str(t["bits"]), t["bits"] // 8)
        if k == "bool":
            return self.int("bool", 1, boolean=True)
        if k == "array":
            return self.array(self.of_type(types, t["elem"]), t["len"])
        if k == "slot":
            key = ("slot", t["kernel"])
            if key not in self.by_key:
                # the kernel recognizes `struct bpf_spin_lock { u32 val; }` by name
                self.by_key[key] = self.struct(t["kernel"], t["size"], [("val", self.int("u32", 4), 0)])
            return self.by_key[key]
        if k == "struct":
            members = [(f["name"], self.of_type(types, f["type"]), f["offset"]) for f in t["fields"]]
            tid = self.struct(name or "", t["size"], members)
            if name:
                self.by_key[("named", name)] = tid
            return tid
        raise ValueError(f"no BTF for {t0}")

    def blob(self):
        types = b"".join(t + e for t, e in self.types)
        hdr = struct.pack("<HBBIIIII", BTF_MAGIC, 1, 0, 24, 0, len(types), len(types), len(self.strings))
        return hdr + types + bytes(self.strings)


def read_btf(blob):
    """The types of a BTF blob as (kind, name, vlen, size_or_type,
    extra bytes), by id from 1; enough to find a function by name."""
    magic, version, flags, hdr_len, type_off, type_len, str_off, str_len = struct.unpack_from("<HBBIIIII", blob, 0)
    if magic != BTF_MAGIC:
        raise ValueError("not BTF")
    types_start = hdr_len + type_off
    strings = blob[hdr_len + str_off:hdr_len + str_off + str_len]
    out = [None]
    pos = types_start
    end = types_start + type_len
    while pos < end:
        name_off, info, size_or_type = struct.unpack_from("<III", blob, pos)
        pos += 12
        kind = (info >> 24) & 0x1f
        vlen = info & 0xffff
        extra = {BTF_KIND_INT: 4, BTF_KIND_ARRAY: 12, BTF_KIND_STRUCT: vlen * 12, 5: vlen * 12,
                 6: vlen * 8, 13: vlen * 8, BTF_KIND_VAR: 4, BTF_KIND_DATASEC: vlen * 12,
                 17: 4, 19: vlen * 12}.get(kind, 0)
        e = strings.find(b"\0", name_off)
        name = strings[name_off:e].decode() if name_off else ""
        out.append((kind, name, vlen, size_or_type, blob[pos:pos + extra]))
        pos += extra
    return out


def kfunc_id(vmlinux_types, name):
    for i, t in enumerate(vmlinux_types):
        if t and t[0] == BTF_KIND_FUNC and t[1] == name:
            return i
    return None


# ----------------------------------------------------------- relocation

def words_of(program):
    return [int(w, 16) for w in program["words"]]


def patch(words, relocs, map_fds, kfunc_ids):
    """The words with the map descriptors and kfunc ids in place: a map
    reference is `lddw` with the pseudo source register and the
    descriptor as its immediate, a value reference the same with the
    offset in the second word, a kfunc call its BTF id as the
    immediate."""
    words = list(words)
    for r in relocs:
        i = r["index"]
        w = words[i]
        if r["kind"] in ("map_fd", "map_value"):
            fd = map_fds[r["map"]]
            src = BPF_PSEUDO_MAP_FD if r["kind"] == "map_fd" else BPF_PSEUDO_MAP_VALUE
            w = (w & ~(0xF << 12) & 0xFFFFFFFF) | (src << 12) | ((fd & 0xFFFFFFFF) << 32)
            words[i] = w
            if r["kind"] == "map_value":
                words[i + 1] = (words[i + 1] & 0xFFFFFFFF) | ((r["offset"] & 0xFFFFFFFF) << 32)
        elif r["kind"] == "kfunc":
            kid = kfunc_ids[r["name"]]
            words[i] = (w & 0xFFFF0FFF) | (BPF_PSEUDO_KFUNC_CALL << 12) | ((kid & 0xFFFFFFFF) << 32)
        else:
            raise ValueError(f"unknown relocation kind {r['kind']}")
    return words


def insns_bytes(words):
    return b"".join(struct.pack("<Q", w) for w in words)


# --------------------------------------------------------------- report

def verdict_name(program, retval):
    """The verdict as `koitc run` prints it: the kind's name for the
    value, or the number, signed for an `i32` result."""
    if program["result"].startswith("i"):
        bits = int(program["result"][1:])
        v = retval & ((1 << bits) - 1)
        if v >= 1 << (bits - 1):
            v -= 1 << bits
    else:
        v = retval
    for name, value in program["verdicts"].items():
        if value == v:
            return name
    return str(v)


def report_map(types, m, contents):
    """One map's report lines as `koitc run` prints them. `contents`:
    for an array kind a list of (index, bytes) in index order; for a
    hash a list of (key bytes, value bytes); for a ring buffer a list
    of record bytes."""
    name = m["name"]
    if m["kind"] == "ringbuf":
        lines = [f"map {name}: {len(contents)} record(s)"]
        lines += [f"  0x{bytes(r).hex()}" for r in contents]
        return lines
    if m["kind"] == "hash":
        if not contents:
            return [f"map {name}: empty"]
        lines = [f"map {name}:"]
        for k, v in sorted(contents, key=lambda kv: list(kv[0])):
            lines.append(f"  {types.format(m['key'], k)} => {types.format(m['value'], v)}")
        return lines
    live = [(i, b) for i, b in contents if any(b)]
    if not live:
        return [f"map {name}: all zero"]
    lines = [f"map {name}:"]
    for i, b in live:
        lines.append(f"  [{i}] = {types.format(m['value'], b)}")
    return lines


def map_btf(types, m):
    """The BTF a map needs at creation: its key and value types; the
    ids of both, and the blob. The kernel finds the spin lock by the
    struct's name in the value type."""
    btf = Btf()
    key = btf.of_type(types, m["key"], m["key"].get("name"))
    value = btf.of_type(types, m["value"], m["value"].get("name"))
    return btf.blob(), key, value
