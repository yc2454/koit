#!/usr/bin/env python3
"""
Transcribe the kernel side of koit's interface from a Linux tree.

    tools/transcribe/transcribe.py --tree ~/linux-stable --tag v6.8

reads the tree at the tag through `git show`, never touching the
checkout, and writes `Koit/Interface/Kernel/V6_8.lean`, a value of
`Koit.Interface.Kernel.Side`. Nothing here decides anything: every
value is copied from where the kernel states it, and the header of the
written file says from which tree and commit.

What is read, and from where:

  helpers        the FN list of include/uapi/linux/bpf.h for the
                 numbers, and its documentation comment for the C
                 prototypes, through the kernel's own scripts/bpf_doc.py
  protos         every `struct bpf_func_proto` definition: the C
                 function, gpl_only, the return kind, the argument kinds
  protoFns       every `*_func_proto(enum bpf_func_id ...)` function:
                 the helper each case returns a proto for, and the
                 function the default case falls back to
  progTypes      include/linux/bpf_types.h for the enum name, the
                 verifier ops prefix, and the context struct; the ops
                 struct for its get_func_proto; the uapi enum for the
                 number; libbpf's section_defs for the section names;
                 register_btf_kfunc_id_set for the kfunc sets
  mapTypes       the uapi enum
  kfuncs         the BTF_ID_FLAGS sets and the __bpf_kfunc definitions
  ctx            the uapi context structs, laid out by C's rules
  values         xdp_action, TC_ACT_*, IPPROTO_*, ETH_P_*, ETH_ALEN,
                 and the map-update and netns flags
  changesPkt     bpf_helper_changes_pkt_data, as helper names
  spinLockSize   struct bpf_spin_lock
"""

import argparse
import importlib.util
import os
import re
import subprocess
import sys
import tempfile


# ---------------------------------------------------------------- git

class Tree:
    def __init__(self, path, tag):
        self.path = path
        self.tag = tag
        self.cache = {}

    def git(self, *args):
        return subprocess.run(["git", "-C", self.path, *args], check=True,
                              capture_output=True, text=True).stdout

    def commit(self):
        return self.git("rev-parse", self.tag).strip()

    def show(self, path):
        if path not in self.cache:
            self.cache[path] = self.git("show", f"{self.tag}:{path}")
        return self.cache[path]

    def grep_files(self, pattern, *globs):
        try:
            out = self.git("grep", "-l", "-E", pattern, self.tag, "--", *globs)
        except subprocess.CalledProcessError:
            return []
        return [line.split(":", 1)[1] for line in out.splitlines()]


# ------------------------------------------------------------ helpers

def parse_helper_numbers(bpf_h):
    return {m.group(1): int(m.group(2))
            for m in re.finditer(r"FN\((\w+), (\d+), ##ctx\)", bpf_h)}


def parse_helper_protos(tree):
    """The C prototypes of the documentation comment, through the
    kernel's own parser."""
    with tempfile.TemporaryDirectory() as d:
        doc = os.path.join(d, "bpf_doc.py")
        hdr = os.path.join(d, "bpf.h")
        # the classes only: the script's own main runs at module level
        src = tree.show("scripts/bpf_doc.py")
        src = src[:src.index("\nargParser")]
        with open(doc, "w") as f:
            f.write(src)
        with open(hdr, "w") as f:
            f.write(tree.show("include/uapi/linux/bpf.h"))
        spec = importlib.util.spec_from_file_location("bpf_doc", doc)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        parser = mod.HeaderParser(hdr)
        parser.run()
        protos = {}
        for h in parser.helpers:
            b = h.proto_break_down()
            ret = b["ret_type"] + (" *" if b["ret_star"] else "")
            args = []
            for a in b["args"]:
                if a["type"] == "..." or a["name"] == "...":
                    args.append(("...", ""))
                elif a["type"] == "void" and not a["name"]:
                    continue
                else:
                    args.append((a["type"] + (" *" if a["star"] else ""),
                                 a["name"]))
            name = b["name"]
            if name.startswith("bpf_"):
                name = name[4:]
            protos[name] = (ret, args)
        return protos


def parse_func_protos(tree):
    """Every bpf_func_proto definition in the tree."""
    protos = []
    for path in tree.grep_files(r"struct bpf_func_proto [A-Za-z_0-9]+ = *\{", "*.c"):
        src = tree.show(path)
        for m in re.finditer(
                r"struct bpf_func_proto (\w+) =\s*\{(.*?)\};", src, re.S):
            name, body = m.group(1), m.group(2)
            func = re.search(r"\.func\s*=\s*(\w+)", body)
            gpl = re.search(r"\.gpl_only\s*=\s*(true|false)", body)
            ret = re.search(r"\.ret_type\s*=\s*([^,]+?)\s*,", body)
            args = {}
            for a in re.finditer(r"\.arg(\d)_type\s*=\s*([^,]+?)\s*,", body):
                args[int(a.group(1))] = " ".join(a.group(2).split())
            changes = re.search(r"\.changes_pkt_data\s*=\s*true", body)
            protos.append({
                "name": name,
                "func": func.group(1) if func else "",
                "gplOnly": bool(gpl and gpl.group(1) == "true"),
                "ret": " ".join(ret.group(1).split()) if ret else "",
                "args": [args[i] for i in sorted(args)],
                "changesPkt": bool(changes),
                "path": path,
            })
    return protos


def function_body(src, name):
    """The body of the C function `name`, from its opening brace to the
    closing brace in column 0."""
    m = re.search(r"^(?:[\w\s\*]+?[\s\*])?" + re.escape(name)
                  + r"\s*\([^)]*\)\s*\n?\{", src, re.M)
    if not m:
        return None
    end = src.find("\n}\n", m.end())
    return src[m.end():end]


def parse_proto_getters(tree):
    """The functions of no argument that return a proto, such as
    `bpf_get_trace_printk_proto`, by the proto they return."""
    getters = {}
    for path in tree.grep_files(r"struct bpf_func_proto \*[A-Za-z_0-9]+\(void\)", "*.c"):
        src = tree.show(path)
        for m in re.finditer(r"struct bpf_func_proto \*\s*(\w+)\(void\)\s*\n?\{(.*?)^\}",
                             src, re.M | re.S):
            p = re.search(r"&(\w+_proto)\b", m.group(2))
            if p:
                getters[m.group(1)] = p.group(1)
    return getters


def parse_proto_fns(tree):
    """Every get_func_proto function: the proto each case returns and
    the default's fallback."""
    fns = {}
    getters = parse_proto_getters(tree)
    files = tree.grep_files(r"^[A-Za-z_0-9]+_func_proto\(enum bpf_func_id func_id", "*.c")
    for path in files:
        src = tree.show(path)
        for m in re.finditer(r"^(\w+_func_proto)\(enum bpf_func_id func_id", src, re.M):
            name = m.group(1)
            body = function_body(src, name)
            if body is None:
                continue
            cases, fallback = [], None
            labels = list(re.finditer(r"^\s*(case BPF_FUNC_(\w+):|default:)", body, re.M))
            pending = []
            for i, lab in enumerate(labels):
                nxt = labels[i + 1].start() if i + 1 < len(labels) else len(body)
                text = body[lab.end():nxt]
                if lab.group(1) == "default:":
                    fb = re.search(r"\b(\w+_func_proto)\s*\(", text)
                    if fb:
                        fallback = fb.group(1)
                    pending = []
                    continue
                pending.append(lab.group(2))
                p = re.search(r"&(\w+_proto)\b", text)
                if not p:
                    g = re.search(r"\b(\w+_proto)\s*\(\)", text)
                    proto = getters.get(g.group(1)) if g else None
                else:
                    proto = p.group(1)
                if proto:
                    for h in pending:
                        cases.append((h, proto))
                    pending = []
                elif re.search(r"\breturn\b", text):
                    pending = []
            fns[name] = {"name": name, "cases": cases, "fallback": fallback}
    return fns


# ---------------------------------------------------------- enums etc.

def parse_enum(src, enum_name):
    m = re.search(r"^enum " + enum_name + r" \{(.*?)^\};", src, re.M | re.S)
    if not m:
        raise SystemExit(f"enum {enum_name} not found")
    body = re.sub(r"/\*.*?\*/", "", m.group(1), flags=re.S)
    body = re.sub(r"^\s*#.*$", "", body, flags=re.M)
    values, nxt = [], 0
    for item in body.split(","):
        item = item.strip()
        if not item:
            continue
        if "=" in item:
            name, val = [s.strip() for s in item.split("=", 1)]
            known = dict(values)
            if val in known:
                v = known[val]
            else:
                v = int(val, 0)
        else:
            name, v = item, nxt
        values.append((name, v))
        nxt = v + 1
    return values


def parse_prog_types(tree):
    src = tree.show("include/linux/bpf_types.h")
    out = []
    for m in re.finditer(r"BPF_PROG_TYPE\((BPF_PROG_TYPE_\w+),\s*(\w+),\s*(struct \w+|void)",
                         src):
        out.append({"name": m.group(1), "ops": m.group(2) + "_verifier_ops",
                    "ctx": None if m.group(3) == "void" else m.group(3)})
    return out


def parse_verifier_ops(tree):
    ops = {}
    for path in tree.grep_files(r"_verifier_ops = \{", "*.c"):
        src = tree.show(path)
        for m in re.finditer(r"struct bpf_verifier_ops (\w+_verifier_ops) = \{(.*?)\};",
                             src, re.S):
            g = re.search(r"\.get_func_proto\s*=\s*(\w+)", m.group(2))
            ops[m.group(1)] = g.group(1) if g else None
    return ops


def parse_sections(tree):
    src = tree.show("tools/lib/bpf/libbpf.c")
    secs = {}
    for m in re.finditer(r'SEC_DEF\("([^"]+)",\s*(\w+),', src):
        secs.setdefault("BPF_PROG_TYPE_" + m.group(2), []).append(m.group(1))
    return secs


def parse_kfunc_registrations(tree):
    """Program type -> kfunc set names, through the id_set variables."""
    regs = {}
    for path in tree.grep_files(r"register_btf_kfunc_id_set\(", "*.c"):
        src = tree.show(path)
        var_to_set = {}
        for m in re.finditer(r"struct btf_kfunc_id_set (\w+) = \{(.*?)\};", src, re.S):
            s = re.search(r"\.set\s*=\s*&(\w+)", m.group(2))
            if s:
                var_to_set[m.group(1)] = s.group(1)
        for m in re.finditer(r"register_btf_kfunc_id_set\((BPF_PROG_TYPE_\w+),\s*&(\w+)\)", src):
            if m.group(2) in var_to_set:
                regs.setdefault(m.group(1), []).append(var_to_set[m.group(2)])
    return regs


def parse_kfunc_sets(tree):
    sets = []
    for path in tree.grep_files(r"BTF_ID_FLAGS\(func,", "*.c"):
        src = tree.show(path)
        for m in re.finditer(
                r"(?:BTF_SET8_START|BTF_KFUNCS_START)\((\w+)\)(.*?)(?:BTF_SET8_END|BTF_KFUNCS_END)\(\1\)",
                src, re.S):
            for f in re.finditer(r"BTF_ID_FLAGS\(func,\s*(\w+)(?:,\s*([^)]+))?\)", m.group(2)):
                flags = [x.strip() for x in (f.group(2) or "").split("|") if x.strip()]
                sets.append({"name": f.group(1), "set": m.group(1), "flags": flags})
    return sets


def parse_kfunc_defs(tree):
    defs = {}
    for path in tree.grep_files(r"^__bpf_kfunc ", "*.c"):
        src = tree.show(path)
        for m in re.finditer(
                r"^__bpf_kfunc\s+([\w\s\*]+?)\s*\b(\w+)\s*\(([^)]*)\)\s*\n?\{", src, re.M | re.S):
            ret = " ".join(m.group(1).split())
            for kw in ("static", "inline", "__always_inline"):
                ret = re.sub(r"\b" + kw + r"\b", "", ret).strip()
            args = []
            for a in m.group(3).split(","):
                a = " ".join(a.split())
                if not a or a == "void":
                    continue
                am = re.match(r"(.+?)\s*(\**)\s*(\w+)$", a)
                if am:
                    args.append((am.group(1) + (" " + am.group(2) if am.group(2) else ""),
                                 am.group(3)))
                else:
                    args.append((a, ""))
            defs.setdefault(m.group(2), (ret, args))
    return defs


# ------------------------------------------------------- context structs

SIZES = {"__u8": 1, "__s8": 1, "__u16": 2, "__s16": 2, "__u32": 4, "__s32": 4,
         "__u64": 8, "__s64": 8, "__be16": 2, "__be32": 4, "__be64": 8}


def layout_struct(bpf_h, name):
    m = re.search(r"^" + re.escape(name) + r" \{(.*?)^\};", bpf_h, re.M | re.S)
    if not m:
        raise SystemExit(f"{name} not found")
    body = re.sub(r"/\*.*?\*/", "", m.group(1), flags=re.S)
    fields, off, align_max = [], 0, 1
    for line in body.splitlines():
        line = line.strip()
        if not line:
            continue
        mm = re.match(r"__bpf_md_ptr\([^,]+,\s*(\w+)\);", line)
        if mm:
            size, align, fname = 8, 8, mm.group(1)
        else:
            mm = re.match(r"(__(?:u|s|be)(?:8|16|32|64))\s+(\w+)?(?:\[(\d+)\])?\s*(?::\s*(\d+))?;", line)
            if not mm:
                raise SystemExit(f"{name}: cannot lay out `{line}`")
            base = SIZES[mm.group(1)]
            fname = mm.group(2) or ""
            if mm.group(4):
                if fname:
                    raise SystemExit(f"{name}: a named bit-field `{line}`")
                # an unnamed bit-field: padding of its bits, unaligned
                size, align = (int(mm.group(4)) + 7) // 8, 1
            else:
                size = base * (int(mm.group(3)) if mm.group(3) else 1)
                align = base
        off = (off + align - 1) // align * align
        fields.append({"name": fname, "offset": off, "size": size})
        off += size
        align_max = max(align_max, align)
    total = (off + align_max - 1) // align_max * align_max
    return {"name": name, "size": total, "fields": fields}


# ------------------------------------------------------------- values

def parse_defines(src, prefix_re):
    out = []
    for m in re.finditer(r"^#define\s+(" + prefix_re + r")\s+(\(?-?0x[0-9a-fA-F]+\)?|\(?-?\d+\)?)",
                         src, re.M):
        out.append((m.group(1), int(m.group(2).strip("()"), 0)))
    return out


def parse_values(tree, bpf_h):
    values = []
    values += parse_enum(bpf_h, "xdp_action")
    values += parse_defines(tree.show("include/uapi/linux/pkt_cls.h"), r"TC_ACT_\w+")
    in_h = tree.show("include/uapi/linux/in.h")
    for m in re.finditer(r"^\s*(IPPROTO_\w+)\s*=\s*(\d+)", in_h, re.M):
        values.append((m.group(1), int(m.group(2))))
    values += parse_defines(tree.show("include/uapi/linux/in6.h"), r"IPPROTO_\w+")
    values += parse_defines(tree.show("include/uapi/linux/if_ether.h"), r"ETH_P_\w+|ETH_ALEN")
    for flag in ("BPF_ANY", "BPF_NOEXIST", "BPF_EXIST", "BPF_F_LOCK"):
        m = re.search(r"\b" + flag + r"\s*=\s*(\d+)", bpf_h)
        if m:
            values.append((flag, int(m.group(1))))
    m = re.search(r"BPF_F_CURRENT_NETNS\s*=\s*\(?(-?\d+)L?\)?", bpf_h)
    if m:
        values.append(("BPF_F_CURRENT_NETNS", int(m.group(1))))
    seen, out = set(), []
    for k, v in values:
        if k not in seen:
            seen.add(k)
            out.append((k, v))
    return out


def parse_changes_pkt(tree, protos, fns):
    """The helpers that change the packet, by helper name: older
    kernels compare C functions, newer ones switch on helper ids."""
    src = tree.show("net/core/filter.c")
    body = function_body(src, "bpf_helper_changes_pkt_data")
    names = set()
    if body is not None:
        names |= set(re.findall(r"case BPF_FUNC_(\w+):", body))
        funcs = set(re.findall(r"func == (\w+)", body))
        by_proto = {p["name"]: p["func"] for p in protos}
        for f in fns.values():
            for helper, proto in f["cases"]:
                if by_proto.get(proto) in funcs:
                    names.add(helper)
    return sorted(names)


# --------------------------------------------------------------- lean

def lstr(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lbool(b):
    return "true" if b else "false"


def lint(n):
    return f"({n})" if n < 0 else str(n)


def lopt(s):
    return f"some {lstr(s)}" if s is not None else "none"


def llist(items, indent):
    if not items:
        return "[]"
    pad = " " * indent
    return "[\n" + ",\n".join(pad + x for x in items) + "\n" + " " * (indent - 2) + "]"


def lean_name(tag):
    return "v" + re.sub(r"[^A-Za-z0-9]", "_", tag.lstrip("v"))


def file_name(tag):
    return "V" + re.sub(r"[^A-Za-z0-9]", "_", tag.lstrip("v")) + ".lean"


def emit(side, name):
    out = []
    out.append("import Koit.Interface.Kernel\n")
    out.append("/-!\nThe kernel side of the interface for " + side["tag"] +
               ", transcribed by\n`tools/transcribe/transcribe.py` from " +
               side["tree"] + " at " + side["tag"] + "\n(" + side["commit"] +
               "). Do not edit: rerun the transcriber.\n-/\n")
    out.append("namespace Koit.Interface.Kernel\n")
    helpers = [f"{{ name := {lstr(h['name'])}, id := {h['id']}, ret := {lstr(h['ret'])}, "
               f"args := [{', '.join(f'({lstr(t)}, {lstr(n)})' for t, n in h['args'])}] }}"
               for h in side["helpers"]]
    out.append(f"def {name}.helpers : List Helper := {llist(helpers, 2)}\n")
    protos = [f"{{ name := {lstr(p['name'])}, func := {lstr(p['func'])}, gplOnly := {lbool(p['gplOnly'])}, "
              f"ret := {lstr(p['ret'])}, args := [{', '.join(lstr(a) for a in p['args'])}] }}"
              for p in side["protos"]]
    out.append(f"def {name}.protos : List Proto := {llist(protos, 2)}\n")
    fns = [f"{{ name := {lstr(f['name'])}, fallback := {lopt(f['fallback'])},\n    cases := "
           f"[{', '.join(f'({lstr(h)}, {lstr(p)})' for h, p in f['cases'])}] }}"
           for f in side["protoFns"]]
    out.append(f"def {name}.protoFns : List ProtoFn := {llist(fns, 2)}\n")
    pts = [f"{{ name := {lstr(t['name'])}, id := {t['id']}, protoFn := {lopt(t['protoFn'])}, "
           f"ctx := {lopt(t['ctx'])},\n    sections := [{', '.join(lstr(s) for s in t['sections'])}], "
           f"kfuncSets := [{', '.join(lstr(s) for s in t['kfuncSets'])}] }}"
           for t in side["progTypes"]]
    out.append(f"def {name}.progTypes : List ProgType := {llist(pts, 2)}\n")
    mts = [f"({lstr(k)}, {v})" for k, v in side["mapTypes"]]
    out.append(f"def {name}.mapTypes : List (String × Nat) := {llist(mts, 2)}\n")
    kfs = [f"{{ name := {lstr(k['name'])}, set := {lstr(k['set'])}, flags := [{', '.join(lstr(f) for f in k['flags'])}], "
           f"ret := {lstr(k['ret'])}, args := [{', '.join(f'({lstr(t)}, {lstr(n)})' for t, n in k['args'])}] }}"
           for k in side["kfuncs"]]
    out.append(f"def {name}.kfuncs : List Kfunc := {llist(kfs, 2)}\n")
    def cfield(f):
        return f"⟨{lstr(f['name'])}, {f['offset']}, {f['size']}⟩"
    ctxs = [f"{{ name := {lstr(c['name'])}, size := {c['size']},\n    fields := "
            f"[{', '.join(cfield(f) for f in c['fields'])}] }}"
            for c in side["ctx"]]
    out.append(f"def {name}.ctx : List CtxStruct := {llist(ctxs, 2)}\n")
    vals = [f"({lstr(k)}, {lint(v)})" for k, v in side["values"]]
    out.append(f"def {name}.values : List (String × Int) := {llist(vals, 2)}\n")
    out.append(f"/-- The kernel side of {side['tag']}. -/\n")
    out.append(f"def {name} : Side :=\n  {{ tag := {lstr(side['tag'])}, tree := {lstr(side['tree'])}, "
               f"commit := {lstr(side['commit'])},\n    helpers := {name}.helpers, protos := {name}.protos, "
               f"protoFns := {name}.protoFns,\n    progTypes := {name}.progTypes, mapTypes := {name}.mapTypes, "
               f"kfuncs := {name}.kfuncs,\n    ctx := {name}.ctx, values := {name}.values,\n    "
               f"changesPkt := [{', '.join(lstr(f) for f in side['changesPkt'])}],\n    "
               f"spinLockSize := {side['spinLockSize']} }}\n")
    out.append("\nend Koit.Interface.Kernel\n")
    return "\n".join(out)


# --------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--tree", required=True, help="a git checkout of Linux")
    ap.add_argument("--tag", required=True, help="the tag or commit to read")
    ap.add_argument("--out", help="the Lean file to write (default: Koit/Interface/Kernel/<Tag>.lean)")
    a = ap.parse_args()
    tree = Tree(a.tree, a.tag)
    bpf_h = tree.show("include/uapi/linux/bpf.h")

    numbers = parse_helper_numbers(bpf_h)
    cprotos = parse_helper_protos(tree)
    helpers = []
    for name, num in sorted(numbers.items(), key=lambda kv: kv[1]):
        if name not in cprotos:
            print(f"transcribe: helper {name} has no documented prototype", file=sys.stderr)
            continue
        ret, args = cprotos[name]
        helpers.append({"name": name, "id": num, "ret": ret, "args": args})

    protos = parse_func_protos(tree)
    seen = {}
    for p in protos:
        if p["name"] in seen and seen[p["name"]] != (p["func"], p["args"]):
            print(f"transcribe: two definitions of {p['name']} differ "
                  f"({seen[p['name']]} vs {p['path']})", file=sys.stderr)
        seen.setdefault(p["name"], (p["func"], p["args"]))
    uniq, names = [], set()
    for p in protos:
        if p["name"] not in names:
            names.add(p["name"])
            uniq.append(p)
    protos = uniq

    fns = parse_proto_fns(tree)
    known = set(p["name"] for p in protos)
    for f in fns.values():
        for h, p in f["cases"]:
            if p not in known:
                print(f"transcribe: {f['name']} returns {p}, which no definition names",
                      file=sys.stderr)
        if f["fallback"] and f["fallback"] not in fns:
            print(f"transcribe: {f['name']} falls back to {f['fallback']}, not found",
                  file=sys.stderr)

    types = parse_prog_types(tree)
    ops = parse_verifier_ops(tree)
    ids = dict(parse_enum(bpf_h, "bpf_prog_type"))
    secs = parse_sections(tree)
    regs = parse_kfunc_registrations(tree)
    prog_types = []
    for t in types:
        fn = ops.get(t["ops"])
        if t["ops"] not in ops:
            print(f"transcribe: {t['ops']} not found for {t['name']}", file=sys.stderr)
        if fn and fn not in fns:
            print(f"transcribe: {fn} of {t['name']} not parsed", file=sys.stderr)
            fn = None
        prog_types.append({"name": t["name"], "id": ids[t["name"]], "protoFn": fn,
                           "ctx": t["ctx"], "sections": secs.get(t["name"], []),
                           "kfuncSets": regs.get(t["name"], [])})
    if "BPF_PROG_TYPE_UNSPEC" in regs:
        prog_types.insert(0, {"name": "BPF_PROG_TYPE_UNSPEC", "id": ids["BPF_PROG_TYPE_UNSPEC"],
                              "protoFn": None, "ctx": None, "sections": [],
                              "kfuncSets": regs["BPF_PROG_TYPE_UNSPEC"]})

    kdefs = parse_kfunc_defs(tree)
    kfuncs = []
    for k in parse_kfunc_sets(tree):
        ret, args = kdefs.get(k["name"], ("", []))
        kfuncs.append({**k, "ret": ret, "args": args})

    ctx_names = sorted({t["ctx"] for t in types if t["ctx"]})
    ctx = []
    for c in ctx_names:
        try:
            ctx.append(layout_struct(bpf_h, c))
        except SystemExit as e:
            print(f"transcribe: {e}", file=sys.stderr)

    side = {
        "tag": a.tag, "tree": os.path.abspath(a.tree), "commit": tree.commit(),
        "helpers": helpers, "protos": protos, "protoFns": sorted(fns.values(), key=lambda f: f["name"]),
        "progTypes": prog_types, "mapTypes": parse_enum(bpf_h, "bpf_map_type"),
        "kfuncs": kfuncs, "ctx": ctx, "values": parse_values(tree, bpf_h),
        "changesPkt": parse_changes_pkt(tree, protos, fns),
        "spinLockSize": layout_struct(bpf_h, "struct bpf_spin_lock")["size"],
    }
    name = lean_name(a.tag)
    out = a.out or os.path.join(os.path.dirname(__file__), "..", "..", "Koit", "Interface",
                                "Kernel", file_name(a.tag))
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        f.write(emit(side, name))
    print(f"transcribe: {len(helpers)} helpers, {len(protos)} protos, {len(fns)} proto functions, "
          f"{len(prog_types)} program types, {len(kfuncs)} kfuncs, {len(ctx)} context structs, "
          f"{len(side['values'])} values -> {os.path.relpath(out)}")


if __name__ == "__main__":
    main()
