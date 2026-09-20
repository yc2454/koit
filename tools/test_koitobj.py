#!/usr/bin/env python3
"""
Checks on the interchange reader that need no kernel: the layouts and
the report printer against a document koitc wrote, the BTF encoder
read back by the BTF reader, the relocation patcher, and the verdict
names. Run as

    python3 tools/test_koitobj.py UNIT.json

with the document of tests/run/picker-vlan.ko; the runner's emit
stage does so when python3 is present.
"""

import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import koitobj  # noqa: E402


def check(cond, what):
    if not cond:
        raise SystemExit(f"test_koitobj: {what}")


def test_document(path):
    u = koitobj.Unit.load(path)
    check(u.kernel.startswith("v"), "kernel tag")
    policy = u.map("policy")
    check(policy["key_size"] == 4 and policy["value_size"] == 4, "policy sizes")
    check(policy["direct"], "policy is direct")
    check(u.types.format(policy["value"], bytes([1, 0, 0, 0])) == "{ cur: 1 }", "format of policy")
    backends = u.map("backends")
    check(backends["value_size"] == 128, "backends value size")
    row = bytes([10, 0, 0, 1, 3, 0, 0, 0]) + bytes(120)
    got = u.types.format(backends["value"], row)
    check(got.startswith("[{ ip: 0x0a000001, ifindex: 3 }, { ip: 0x00000000, ifindex: 0 }"), f"format of backends: {got}")
    check(koitobj.report_map(u.types, backends, [(0, bytes(128))]) == ["map backends: all zero"], "all zero")
    check(koitobj.report_map(u.types, policy, [(0, bytes([1, 0, 0, 0]))]) == ["map policy:", "  [0] = { cur: 1 }"],
          "policy report")
    pick = [p for p in u.programs if p["name"] == "pick"][0]
    check(koitobj.verdict_name(pick, 4) == "REDIRECT", "verdict name")
    check(koitobj.verdict_name(pick, 9) == "9", "verdict number")
    words = koitobj.words_of(pick)
    check(len(words) == len(pick["words"]) and all(0 <= w < 1 << 64 for w in words), "words")
    # every map relocation sits on an lddw with the pseudo register
    for r in pick["relocs"]:
        w = words[r["index"]]
        check(w & 0xFF == 0x18, "reloc on lddw")
        check((w >> 12) & 0xF in (1, 2), "pseudo source register")


def test_patch():
    lddw_value = 0x18 | (1 << 8) | (2 << 12)
    words = [lddw_value, 0x10 << 32, 0x85 | (2 << 12)]
    relocs = [{"index": 0, "kind": "map_value", "map": "m", "offset": 0x10},
              {"index": 2, "kind": "kfunc", "name": "f"}]
    out = koitobj.patch(words, relocs, {"m": 7}, {"f": 1234})
    check(out[0] >> 32 == 7 and (out[0] >> 12) & 0xF == 2, "map value fd")
    check(out[1] >> 32 == 0x10, "map value offset")
    check(out[2] >> 32 == 1234 and (out[2] >> 12) & 0xF == 2, "kfunc id")
    fdw = koitobj.patch([0x18 | (1 << 12), 0], [{"index": 0, "kind": "map_fd", "map": "m"}], {"m": 9}, {})
    check(fdw[0] >> 32 == 9 and (fdw[0] >> 12) & 0xF == 1, "map fd")
    check(len(koitobj.insns_bytes(out)) == 24, "insn bytes")


def test_btf():
    types = koitobj.Types([
        {"name": "V", "type": {"kind": "struct", "size": 8, "align": 4, "fields": [
            {"name": "lk", "offset": 0, "type": {"kind": "slot", "name": "spinlock", "kernel": "bpf_spin_lock",
                                                  "size": 4, "align": 4}},
            {"name": "n", "offset": 4, "type": {"kind": "int", "signed": False, "bits": 32}}]}}])
    m = {"name": "t", "kind": "hash", "key": {"kind": "int", "signed": False, "bits": 32},
         "value": {"kind": "named", "name": "V"}}
    blob, key_id, value_id = koitobj.map_btf(types, m)
    ts = koitobj.read_btf(blob)
    check(ts[key_id][0] == koitobj.BTF_KIND_INT and ts[key_id][1] == "u32", "key int")
    check(ts[value_id][0] == koitobj.BTF_KIND_STRUCT and ts[value_id][1] == "V", "value struct")
    check(ts[value_id][2] == 2 and ts[value_id][3] == 8, "value members and size")
    lk_name, lk_type, lk_off = struct.unpack_from("<III", ts[value_id][4], 0)
    check(ts[lk_type][1] == "bpf_spin_lock" and lk_off == 0, "spin lock member")
    n_name, n_type, n_off = struct.unpack_from("<III", ts[value_id][4], 12)
    check(ts[n_type][1] == "u32" and n_off == 32, "n member at bit 32")
    # an array of a named struct, and a be field, in one value
    types2 = koitobj.Types([{"name": "E", "type": {"kind": "struct", "size": 6, "align": 2, "fields": [
        {"name": "p", "offset": 0, "type": {"kind": "be", "bits": 16}},
        {"name": "q", "offset": 2, "type": {"kind": "array", "elem": {"kind": "int", "signed": True, "bits": 8},
                                             "len": 4, "size": 4, "align": 1}}]}}])
    b = koitobj.Btf()
    tid = b.of_type(types2, {"kind": "array", "elem": {"kind": "named", "name": "E"}, "len": 3, "size": 18, "align": 2})
    ts2 = koitobj.read_btf(b.blob())
    check(ts2[tid][0] == koitobj.BTF_KIND_ARRAY, "outer array")
    elem, idx, n = struct.unpack_from("<III", ts2[tid][4], 0)
    check(ts2[elem][1] == "E" and n == 3, "array of E")
    check(koitobj.kfunc_id(ts2, "nothing") is None, "no kfunc")


def test_elf(path):
    """The object file of the document read back: the section headers,
    the symbols, the relocations on `lddw` words, and the BTF."""
    import elf as elfw
    u = koitobj.Unit.load(path)
    data = elfw.write(u)
    check(data[:4] == b"\x7fELF" and data[4] == 2 and data[5] == 1, "ELF64 little-endian")
    e_type, e_machine = struct.unpack_from("<HH", data, 16)
    check(e_type == 1 and e_machine == 247, "relocatable for BPF")
    shoff = struct.unpack_from("<Q", data, 0x28)[0]
    shnum, shstrndx = struct.unpack_from("<HH", data, 0x3c)
    headers = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * 64) for i in range(shnum)]
    names_off = headers[shstrndx][4]

    def name(o):
        return data[names_off + o:data.index(b"\0", names_off + o)].decode()
    by_name = {name(h[0]): h for h in headers}
    for s in [".symtab", ".strtab", ".BTF", "license"] + [p["section"] for p in u.programs]:
        check(s in by_name, f"section {s}")
    for p in u.programs:
        sec = by_name[p["section"]]
        check(sec[5] >= len(p["words"]) * 8, f"section {p['section']} holds {p['name']}")
        rel = by_name.get(".rel" + p["section"])
        if p["relocs"]:
            check(rel is not None and rel[5] // 16 >= len(p["relocs"]), f"relocations of {p['name']}")
    symtab, strtab = by_name[".symtab"], by_name[".strtab"]
    symbols = {}
    for off in range(0, symtab[5], 24):
        st_name, st_info, _, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", data, symtab[4] + off)
        n = data[strtab[4] + st_name:data.index(b"\0", strtab[4] + st_name)].decode()
        symbols[n] = (st_info, st_shndx, st_value, st_size)
    for p in u.programs:
        check(p["name"] in symbols and symbols[p["name"]][0] & 0xF == 2, f"function symbol {p['name']}")
        check(symbols[p["name"]][3] == len(p["words"]) * 8, f"size of {p['name']}")
    for m in u.maps:
        check(m["name"] in symbols and symbols[m["name"]][0] & 0xF == 1, f"map symbol {m['name']}")
    btf = by_name[".BTF"]
    ts = koitobj.read_btf(data[btf[4]:btf[4] + btf[5]])
    vars_ = {t[1] for t in ts if t and t[0] == koitobj.BTF_KIND_VAR}
    check(all(m["name"] in vars_ for m in u.maps), "a BTF variable per map")
    secs = {t[1] for t in ts if t and t[0] == koitobj.BTF_KIND_DATASEC}
    check((".maps" in secs) == any(not m["direct"] for m in u.maps), ".maps data section")
    check((".bss" in secs) == any(m["direct"] for m in u.maps), ".bss data section")
    # a relocated lddw keeps its opcode and carries the value offset
    for p in u.programs:
        sec = by_name[p["section"]]
        base = sec[4] + symbols[p["name"]][2]
        for r in p["relocs"]:
            w = struct.unpack_from("<Q", data, base + r["index"] * 8)[0]
            check(w & 0xFF == 0x18, "relocated lddw")
            if r["kind"] == "map_value":
                check(w >> 32 == r["offset"], "value offset in the first word")


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    test_document(sys.argv[1])
    test_patch()
    test_btf()
    test_elf(sys.argv[1])
    print("test_koitobj: ok")


if __name__ == "__main__":
    main()
