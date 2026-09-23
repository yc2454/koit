#!/usr/bin/env python3
"""
The loader: a koit object into a Linux kernel over the bpf system
call, and its programs run under BPF_PROG_TEST_RUN.

    tools/load.py UNIT.json --packet HEX [--program NAME] [--log-dir D]

reads the document `koitc emit --json` wrote, checks that the running
kernel is the one the document was compiled for, creates the maps,
with BTF for a value that holds a spin lock, patches the map
descriptors into the words, loads each program with the kind's
program type, runs it on the packet, reads every map back, and
prints what `koitc run` prints: a verdict per program, then the
maps. The verifier's log of every load is written whole to the log
directory, and printed on a rejection. Nothing here decides
anything: it is the kernel's answer, formatted.

Only Linux: the system call and its attribute layouts are those of
include/uapi/linux/bpf.h, transcribed by hand below with the
structure each comes from.
"""

import argparse
import ctypes
import mmap
import os
import platform
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import koitobj  # noqa: E402

# enum bpf_cmd
BPF_MAP_CREATE = 0
BPF_MAP_LOOKUP_ELEM = 1
BPF_MAP_GET_NEXT_KEY = 4
BPF_MAP_UPDATE_ELEM = 2
BPF_MAP_FREEZE = 22
BPF_PROG_LOAD = 5
BPF_PROG_TEST_RUN = 10
BPF_BTF_LOAD = 18

# __NR_bpf per architecture
SYSCALL_NR = {"x86_64": 321, "aarch64": 280, "arm64": 280}

libc = ctypes.CDLL(None, use_errno=True)
libc.syscall.restype = ctypes.c_long


def bpf(cmd, attr):
    nr = SYSCALL_NR.get(platform.machine())
    if nr is None:
        raise SystemExit(f"load: no bpf system call number for {platform.machine()}")
    buf = ctypes.create_string_buffer(bytes(attr), len(attr))
    r = libc.syscall(nr, cmd, buf, len(attr))
    if r < 0:
        e = ctypes.get_errno()
        raise OSError(e, os.strerror(e))
    return r, buf.raw


def u64_of(buf):
    return ctypes.addressof(buf)


# ------------------------------------------------------------ attributes
# Each is the union member of `union bpf_attr` the command reads, laid
# out as the header declares it; the kernel zero-fills what the size
# leaves out.

def attr_map_create(map_type, key_size, value_size, entries, flags, name, btf_fd=0, btf_key=0, btf_value=0):
    # struct { __u32 map_type; __u32 key_size; __u32 value_size;
    #          __u32 max_entries; __u32 map_flags; __u32 inner_map_fd;
    #          __u32 numa_node; char map_name[16]; __u32 map_ifindex;
    #          __u32 btf_fd; __u32 btf_key_type_id; __u32 btf_value_type_id; ... }
    return struct.pack("<IIIIIII16sIIII", map_type, key_size, value_size, entries, flags, 0, 0,
                       name.encode()[:15], 0, btf_fd, btf_key, btf_value)


def attr_map_elem(fd, key_buf, value_buf, flags=0):
    # struct { __u32 map_fd; __u64 key; union { __u64 value; __u64 next_key; }; __u64 flags; }
    return struct.pack("<IIQQQ", fd, 0, u64_of(key_buf), u64_of(value_buf), flags)


def attr_prog_load(prog_type, insns_buf, insn_cnt, license_buf, log_buf, name):
    # struct { __u32 prog_type; __u32 insn_cnt; __u64 insns; __u64 license;
    #          __u32 log_level; __u32 log_size; __u64 log_buf; __u32 kern_version;
    #          __u32 prog_flags; char prog_name[16]; __u32 prog_ifindex;
    #          __u32 expected_attach_type; ... }
    return struct.pack("<IIQQIIQII16sII", prog_type, insn_cnt, u64_of(insns_buf), u64_of(license_buf),
                       1, len(log_buf), u64_of(log_buf), 0, 0, name.encode()[:15], 0, 0)


def attr_test_run(prog_fd, data_in, data_out, ctx_in, ctx_out):
    # struct { __u32 prog_fd; __u32 retval; __u32 data_size_in; __u32 data_size_out;
    #          __u64 data_in; __u64 data_out; __u32 repeat; __u32 duration;
    #          __u32 ctx_size_in; __u32 ctx_size_out; __u64 ctx_in; __u64 ctx_out;
    #          __u32 flags; __u32 cpu; __u32 batch_size; }
    return struct.pack("<IIIIQQIIIIQQIII", prog_fd, 0,
                       len(data_in) if data_in is not None else 0,
                       len(data_out) if data_out is not None else 0,
                       u64_of(data_in) if data_in is not None else 0,
                       u64_of(data_out) if data_out is not None else 0,
                       1, 0,
                       len(ctx_in) if ctx_in is not None else 0,
                       len(ctx_out) if ctx_out is not None else 0,
                       u64_of(ctx_in) if ctx_in is not None else 0,
                       u64_of(ctx_out) if ctx_out is not None else 0,
                       0, 0, 0)


def attr_btf_load(btf_buf, log_buf):
    # struct { __u64 btf; __u64 btf_log_buf; __u32 btf_size; __u32 btf_log_size; __u32 btf_log_level; }
    return struct.pack("<QQIII", u64_of(btf_buf), u64_of(log_buf), len(btf_buf), len(log_buf), 1)


# --------------------------------------------------------------- kernel

def running_kernel():
    return platform.release()


def check_version(tag, release, override):
    """The tag's major.minor against the running kernel's."""
    want = tag.lstrip("v").split("-")[0]
    have = ".".join(release.split(".")[:2])
    if want.count(".") >= 1:
        want = ".".join(want.split(".")[:2])
    if want != have and not override:
        raise SystemExit(f"load: the object is for kernel {tag}, this machine runs {release}; "
                         f"pass --any-kernel to load anyway")


def vmlinux_btf():
    try:
        with open("/sys/kernel/btf/vmlinux", "rb") as f:
            return koitobj.read_btf(f.read())
    except FileNotFoundError:
        return None


# ----------------------------------------------------------------- maps

def create_map(unit, m, log_dir):
    btf_fd, key_id, value_id = 0, 0, 0
    if m.get("spin_lock") is not None:
        blob, key_id, value_id = koitobj.map_btf(unit.types, m)
        btf_buf = ctypes.create_string_buffer(blob, len(blob))
        log = ctypes.create_string_buffer(1 << 16)
        try:
            btf_fd, _ = bpf(BPF_BTF_LOAD, attr_btf_load(btf_buf, log))
        except OSError as e:
            sys.stderr.write(log.value.decode(errors="replace"))
            raise SystemExit(f"load: BTF for map {m['name']} refused: {e}")
    entries = m["entries"]
    fd, _ = bpf(BPF_MAP_CREATE, attr_map_create(m["type_id"], m["key_size"], m["value_size"], entries,
                                                m["flags"], m["name"], btf_fd, key_id, value_id))
    # the contents the object holds, entry by entry, then the freeze
    # that makes a read-only map's contents final, as libbpf does
    if m.get("data"):
        contents = bytes.fromhex(m["data"])
        vs = m["value_size"]
        for i in range(entries):
            chunk = contents[i * vs:(i + 1) * vs]
            if not chunk:
                break
            kb = ctypes.create_string_buffer(struct.pack("<I", i), 4)
            vb = ctypes.create_string_buffer(chunk + bytes(vs - len(chunk)), vs)
            bpf(BPF_MAP_UPDATE_ELEM, attr_map_elem(fd, kb, vb))
    if m.get("access") == "ro":
        bpf(BPF_MAP_FREEZE, struct.pack("<I", fd))
    return fd


def lookup(fd, key, value_size):
    kb = ctypes.create_string_buffer(bytes(key), len(key))
    vb = ctypes.create_string_buffer(value_size)
    try:
        bpf(BPF_MAP_LOOKUP_ELEM, attr_map_elem(fd, kb, vb))
    except OSError as e:
        if e.errno == 2:  # ENOENT
            return None
        raise
    return vb.raw


def keys(fd, key_size):
    """Every key of a hash map, by BPF_MAP_GET_NEXT_KEY from no key."""
    out = []
    kb = ctypes.create_string_buffer(key_size)
    nb = ctypes.create_string_buffer(key_size)
    attr = struct.pack("<IIQQQ", fd, 0, 0, u64_of(nb), 0)
    try:
        bpf(BPF_MAP_GET_NEXT_KEY, attr)
    except OSError as e:
        if e.errno == 2:
            return out
        raise
    while True:
        out.append(nb.raw)
        kb = ctypes.create_string_buffer(nb.raw, key_size)
        nb = ctypes.create_string_buffer(key_size)
        try:
            bpf(BPF_MAP_GET_NEXT_KEY, struct.pack("<IIQQQ", fd, 0, u64_of(kb), u64_of(nb), 0))
        except OSError as e:
            if e.errno == 2:
                return out
            raise


def read_map(m, fd):
    if m["kind"] == "ringbuf":
        return ringbuf_records(fd, m["entries"])
    if m["kind"] == "hash":
        return [(k, lookup(fd, k, m["value_size"])) for k in keys(fd, m["key_size"])]
    out = []
    for i in range(m["entries"]):
        v = lookup(fd, struct.pack("<I", i), m["value_size"])
        out.append((i, v if v is not None else bytes(m["value_size"])))
    return out


def ringbuf_records(fd, size):
    """The submitted records of a ring buffer: the consumer page, the
    producer page, and the data pages mapped as libbpf maps them;
    each record a length word with the busy and discard bits, a
    page offset, and the data, eight-aligned."""
    page = mmap.PAGESIZE
    cons = mmap.mmap(fd, page, mmap.MAP_SHARED, mmap.PROT_READ | mmap.PROT_WRITE, offset=0)
    data = mmap.mmap(fd, page + 2 * size, mmap.MAP_SHARED, mmap.PROT_READ, offset=page)
    prod_pos = struct.unpack_from("<Q", data, 0)[0]
    cons_pos = struct.unpack_from("<Q", cons, 0)[0]
    out = []
    while cons_pos < prod_pos:
        off = cons_pos % size
        hdr = struct.unpack_from("<I", data, page + off)[0]
        if hdr & (1 << 31):
            break
        length = hdr & ~((1 << 31) | (1 << 30)) & 0xFFFFFFFF
        if not hdr & (1 << 30):
            out.append(bytes(data[page + off + 8:page + off + 8 + length]))
        cons_pos += (8 + length + 7) // 8 * 8
    struct.pack_into("<Q", cons, 0, cons_pos)
    return out


# ------------------------------------------------------------- programs

def load_program(unit, p, map_fds, kfunc_ids, log_dir):
    words = koitobj.patch(koitobj.words_of(p), p["relocs"], map_fds, kfunc_ids)
    insns = koitobj.insns_bytes(words)
    ib = ctypes.create_string_buffer(insns, len(insns))
    lic = ctypes.create_string_buffer(unit.license.encode() + b"\0")
    log = ctypes.create_string_buffer(1 << 22)
    try:
        fd, _ = bpf(BPF_PROG_LOAD, attr_prog_load(p["prog_type_id"], ib, len(words), lic, log, p["name"]))
        err = None
    except OSError as e:
        fd, err = None, e
    text = log.value.decode(errors="replace")
    if log_dir:
        os.makedirs(log_dir, exist_ok=True)
        with open(os.path.join(log_dir, f"{unit.name}.{p['name']}.log"), "w") as f:
            f.write(text)
    if err is not None:
        sys.stderr.write(text)
        raise SystemExit(f"load: {unit.name}: program {p['name']} refused by kernel {running_kernel()}: {err}")
    return fd


def test_run(p, fd, packet):
    if p["kind"] == "syscall":
        ctx_in = ctypes.create_string_buffer(0)
        attr = attr_test_run(fd, None, None, None, None)
    else:
        data_in = ctypes.create_string_buffer(packet, len(packet))
        data_out = ctypes.create_string_buffer(max(len(packet) + 256, 4096))
        attr = attr_test_run(fd, data_in, data_out, None, None)
    _, raw = bpf(BPF_PROG_TEST_RUN, attr)
    prog_fd, retval, size_in, size_out = struct.unpack_from("<IIII", raw, 0)
    out = bytes(data_out.raw[:size_out]) if p["kind"] != "syscall" else b""
    return retval, out


# ----------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("object", help="the document koitc emit --json wrote")
    ap.add_argument("--packet", default="", help="the input packet in hex")
    ap.add_argument("--program", help="this program only")
    ap.add_argument("--ctx", action="append", default=[], help="unsupported here")
    ap.add_argument("--log-dir", help="where the verifier's logs go")
    ap.add_argument("--any-kernel", action="store_true", help="load on a kernel other than the object's")
    ap.add_argument("--show-packet", action="store_true", help="print the packet after each program")
    a = ap.parse_args()
    if a.ctx:
        raise SystemExit("load: --ctx is not supported: the context is zero")
    unit = koitobj.Unit.load(a.object)
    check_version(unit.kernel, running_kernel(), a.any_kernel)
    packet = bytes.fromhex(a.packet)

    programs = [p for p in unit.programs if a.program is None or p["name"] == a.program]
    if a.program is not None and not programs:
        raise SystemExit(f"load: no program {a.program} in {unit.name}")

    kfunc_names = sorted({r["name"] for p in programs for r in p["relocs"] if r["kind"] == "kfunc"})
    kfunc_ids = {}
    if kfunc_names:
        vm = vmlinux_btf()
        if vm is None:
            raise SystemExit("load: /sys/kernel/btf/vmlinux is needed for kfunc calls")
        for n in kfunc_names:
            kid = koitobj.kfunc_id(vm, n)
            if kid is None:
                raise SystemExit(f"load: kernel {running_kernel()} has no kfunc {n}")
            kfunc_ids[n] = kid

    map_fds = {m["name"]: create_map(unit, m, a.log_dir) for m in unit.maps}
    # every program loads before any runs, so that the program arrays
    # can hold their descriptors first
    prog_fds = {}
    for p in programs:
        prog_fds[p["name"]] = load_program(unit, p, map_fds, kfunc_ids, a.log_dir)
    for m in unit.maps:
        for slot, pname in enumerate(m.get("programs") or []):
            if pname not in prog_fds:
                raise SystemExit(f"load: program array {m['name']} names `{pname}`, which did not load")
            kb = ctypes.create_string_buffer(struct.pack("<I", slot), 4)
            vb = ctypes.create_string_buffer(struct.pack("<I", prog_fds[pname]), 4)
            bpf(BPF_MAP_UPDATE_ELEM, attr_map_elem(map_fds[m["name"]], kb, vb))
    for p in programs:
        fd = prog_fds[p["name"]]
        retval, out = test_run(p, fd, packet)
        print(f"{p['name']}: {koitobj.verdict_name(p, retval)}")
        if a.show_packet and p["kind"] != "syscall":
            print(f"{p['name']}: packet: 0x{out.hex()}")
        os.close(fd)
    for m in unit.maps:
        for line in koitobj.report_map(unit.types, m, read_map(m, map_fds[m["name"]])):
            print(line)


if __name__ == "__main__":
    main()
