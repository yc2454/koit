#!/bin/sh
# Builds koitc and runs it over the corpus.
#
#   tests/ok/*.ko     must parse and desugar; at the check stage, must
#                     also check
#   tests/demo/*.ko   the programs the language is shown with; held to
#                     everything tests/ok is held to, at every stage
#   tests/err/*.ko    must parse and desugar; at the check stage,
#                     `koitc check` must reject the file with a
#                     diagnostic containing the text after
#                     `// expect: ` on line 1
#
# At the check stage `koitc check --json` must agree with the text
# form on every file, so that the object an editor reads never says
# a unit was accepted when the text form says it was not.
#   tests/parse/*.ko  must parse and desugar; nothing is claimed about
#                     typing
#   tests/corpus/*.ko ports of the coverage cases, named by case id;
#                     rejected like tests/err, with the recorded reason
#
# Every file that parses must also round-trip: printing it as source
# and parsing and printing that again must give the same text.
#
# tests/run/*.ko    a unit with a `// run: OPTIONS` line first, whose
#                   `koitc run` output must be the rest of that comment
#                   block, each expected line after `// `
# tests/selftests/*.ko  the kernel's own selftests written in koit,
#                   one unit per test, named `<rule>-<kernel test
#                   name>`, with a `// selftest: ...` line naming the
#                   test, its crawl id, and its rule. Line 1 picks the
#                   shape: `// expect: TEXT` is held to what tests/err
#                   is, `// run: OPTIONS` to what tests/run is, and any
#                   other first line to what tests/ok is. Two more:
#                   `// refused: REASON` is a legal program koit cannot
#                   write; it must fail to check, is counted rather
#                   than passed, and is reported if it ever checks, so
#                   that the header is rewritten. `// pending: ENTRY`
#                   is a unit written before its ISSUES entry landed;
#                   it is skipped and counted until the line comes off.
#
# KOIT_STAGE=lex, parse (the default), check, run, lower, shape, or
# emit selects how far the run goes; each stage includes the ones before
# it. The err files in LATER, empty since session 5, are skipped at
# the check stage. At the run stage every ok file must also run to a
# verdict on an empty packet. At the lower stage every ok and run
# unit must lower, with and without inlining, `koitc run --lir` must
# print what `koitc run` prints, before and after inlining, and
# `koitc run --bir` must print it too on the flattened unit under cpu
# v4, and under v3 unless the unit needs v4's signed division, and
# `koitc run --bytecode` on the allocated unit under v4. At the
# shape stage `koitc shape` must pass on every ok and run unit:
# every test a conditional jump, every cast an instruction of the
# table, every packet access and index under a test on its path. At
# the emit stage every ok and run unit must emit C and, when clang
# with the BPF target is present, that C must build; and when
# llvm-mc is present, the words must disassemble to the bytecode
# printed in LLVM's syntax, and that text must assemble back to the
# words, under cpu v3 and v4. Both tools are optional: absent, the
# stage notes it and checks the rest. Every ok and run unit must also
# emit its object as JSON; when python3 is present, tools/elf.py must
# write the object file from it, llvm-readelf, when present, must
# read that back, and the reader under tools/ must pass its self-test
# on the picker's document, which parses the object file too.
#
# KOIT_STAGE=kernel runs each run unit on a real kernel, when
# KOIT_KERNEL_HOST names an ssh host (user@node) with python3 and
# root through sudo: the object is emitted here, copied there with
# tools/, loaded and run by tools/load.py, and its report compared
# with the unit's expected block and with `koitc run --bytecode`
# minus printk lines. A unit whose header has `// kernel: verdict
# only` compares verdicts alone; one with `// kernel: rejected TEXT`
# passes when the kernel refuses it with TEXT in the verifier's log.
# Without a host the stage is skipped, and it never builds Lean on
# the node. KOIT_KERNEL_DIR names the directory used there.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$HOME/.elan/bin:$PATH"
lake build koitc >/dev/null || { echo "build failed"; exit 2; }
KOITC=.lake/build/bin/koitc
STAGE=${KOIT_STAGE:-parse}
CLANG=${KOIT_CLANG:-/opt/homebrew/opt/llvm/bin/clang}
LLVM_MC=${KOIT_LLVM_MC:-/opt/homebrew/opt/llvm/bin/llvm-mc}
LLVM_READELF=${KOIT_LLVM_READELF:-/opt/homebrew/opt/llvm/bin/llvm-readelf}
LLVM_OBJCOPY=${KOIT_LLVM_OBJCOPY:-/opt/homebrew/opt/llvm/bin/llvm-objcopy}
# the stages in order, so that a stage includes the ones before it
rank() {
  case "$1" in
    lex) echo 0 ;; parse) echo 1 ;; check) echo 2 ;; run) echo 3 ;;
    lower) echo 4 ;; shape) echo 5 ;; emit) echo 6 ;; kernel) echo 7 ;; *) echo 1 ;;
  esac
}
RANK=$(rank "$STAGE")
at_least() { [ "$RANK" -ge "$(rank "$1")" ]; }
LATER=""
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
pass=0
fail=0
skipped=0
pending=0
refused=0

# tests/selftests: line 1 sorts each unit into the shape it is held to
SELF_OK=""
SELF_ERR=""
SELF_RUN=""
SELF_REFUSED=""
for f in tests/selftests/*.ko; do
  [ -e "$f" ] || continue
  case "$(sed -n 1p "$f")" in
    "// pending:"*) pending=$((pending + 1)) ;;
    "// expect:"*) SELF_ERR="$SELF_ERR $f" ;;
    "// run:"*) SELF_RUN="$SELF_RUN $f" ;;
    "// refused:"*) SELF_REFUSED="$SELF_REFUSED $f" ;;
    *) SELF_OK="$SELF_OK $f" ;;
  esac
done

failed() {
  echo "FAIL $1 $2"
  [ -s "$TMP/out" ] && sed 's/^/    /' "$TMP/out"
  fail=$((fail + 1))
}

later() {
  for l in $LATER; do
    [ "$l" = "$1" ] && return 0
  done
  return 1
}

for f in tests/ok/*.ko tests/demo/*.ko tests/err/*.ko tests/parse/*.ko \
         tests/corpus/*.ko tests/run/*.ko $SELF_OK $SELF_ERR $SELF_RUN; do
  [ -e "$f" ] || continue
  if ! "$KOITC" lex "$f" >/dev/null 2>"$TMP/out"; then
    failed lex "$f"
    continue
  fi
  if [ "$STAGE" = lex ]; then
    pass=$((pass + 1))
    continue
  fi
  if ! "$KOITC" parse "$f" >"$TMP/out" 2>&1; then
    failed parse "$f"
    continue
  fi
  "$KOITC" print "$f" >"$TMP/a.ko" 2>"$TMP/out" &&
    "$KOITC" print "$TMP/a.ko" >"$TMP/b.ko" 2>"$TMP/out" &&
    cmp -s "$TMP/a.ko" "$TMP/b.ko" || { failed round-trip "$f"; continue; }
  if ! "$KOITC" desugar "$f" >/dev/null 2>"$TMP/out"; then
    failed desugar "$f"
    continue
  fi
  pass=$((pass + 1))
done

if at_least check; then
  for f in tests/ok/*.ko tests/demo/*.ko $SELF_OK; do
    if ! "$KOITC" check "$f" >"$TMP/out" 2>&1; then
      failed check "$f"
    elif ! "$KOITC" check --json "$f" 2>/dev/null | grep -qF '"ok": true'; then
      failed check-json "$f"
    else
      pass=$((pass + 1))
    fi
  done
  for f in tests/err/*.ko tests/corpus/*.ko $SELF_ERR; do
    [ -e "$f" ] || continue
    name=$(basename "$f" .ko)
    if later "$name"; then
      echo "skip $f (later)"
      skipped=$((skipped + 1))
      continue
    fi
    expect=$(sed -n '1s|^// expect: ||p' "$f")
    if "$KOITC" check "$f" >"$TMP/out" 2>&1; then
      failed accepted "$f"
    elif ! grep -qF -- "$expect" "$TMP/out"; then
      echo "    expected: $expect"
      failed diagnostic "$f"
    elif ! "$KOITC" check --json "$f" 2>/dev/null | grep -qF '"ok": false'; then
      failed check-json "$f"
    else
      pass=$((pass + 1))
    fi
  done
  # a refused unit is a legal program koit cannot write: it must not
  # check, and it is counted rather than passed
  for f in $SELF_REFUSED; do
    if "$KOITC" check "$f" >"$TMP/out" 2>&1; then
      echo "    the refusal is lifted; rewrite the header"
      failed refusal-lifted "$f"
    else
      refused=$((refused + 1))
    fi
  done
fi

if at_least run; then
  for f in tests/ok/*.ko tests/demo/*.ko $SELF_OK; do
    if "$KOITC" run "$f" >"$TMP/out" 2>&1; then
      pass=$((pass + 1))
    else
      failed run "$f"
    fi
  done
  for f in tests/run/*.ko $SELF_RUN; do
    [ -e "$f" ] || continue
    opts=$(sed -n '1s|^// run: ||p' "$f")
    sed -n '2,/^$/{s|^// ||p;}' "$f" >"$TMP/want"
    # shellcheck disable=SC2086
    if ! "$KOITC" run $opts "$f" >"$TMP/out" 2>&1; then
      failed run "$f"
    elif ! cmp -s "$TMP/out" "$TMP/want"; then
      echo "    expected:"; sed 's/^/      /' "$TMP/want"
      failed output "$f"
    else
      pass=$((pass + 1))
    fi
  done
fi

# the lowering: `lower` and `lower --inline` succeed, and the LIR
# runs print what the Core run prints
if at_least lower; then
  for f in tests/ok/*.ko tests/demo/*.ko tests/run/*.ko $SELF_OK $SELF_RUN; do
    [ -e "$f" ] || continue
    opts=$(sed -n '1s|^// run: ||p' "$f")
    if ! "$KOITC" lower "$f" >"$TMP/out" 2>&1; then
      failed lower "$f"; continue
    fi
    if ! "$KOITC" lower --inline "$f" >"$TMP/out" 2>&1; then
      failed inline "$f"; continue
    fi
    # shellcheck disable=SC2086
    "$KOITC" run $opts "$f" >"$TMP/core" 2>&1
    # shellcheck disable=SC2086
    if ! "$KOITC" run --lir $opts "$f" >"$TMP/out" 2>&1; then
      failed run-lir "$f"; continue
    fi
    if ! cmp -s "$TMP/core" "$TMP/out"; then
      echo "    core:"; sed 's/^/      /' "$TMP/core"
      failed lir-differs "$f"; continue
    fi
    # shellcheck disable=SC2086
    if ! "$KOITC" run --lir --inline $opts "$f" >"$TMP/out" 2>&1; then
      failed run-inlined "$f"; continue
    fi
    if ! cmp -s "$TMP/core" "$TMP/out"; then
      echo "    core:"; sed 's/^/      /' "$TMP/core"
      failed inlined-differs "$f"; continue
    fi
    # the machine on the flattened unit: v4 must agree; v3 must agree
    # or report the signed division the target lacks
    # shellcheck disable=SC2086
    if ! "$KOITC" run --bir --cpu v4 $opts "$f" >"$TMP/out" 2>&1; then
      failed run-bir "$f"; continue
    fi
    if ! cmp -s "$TMP/core" "$TMP/out"; then
      echo "    core:"; sed 's/^/      /' "$TMP/core"
      failed bir-differs "$f"; continue
    fi
    # shellcheck disable=SC2086
    if "$KOITC" run --bir --cpu v3 $opts "$f" >"$TMP/out" 2>&1; then
      if ! cmp -s "$TMP/core" "$TMP/out"; then
        echo "    core:"; sed 's/^/      /' "$TMP/core"
        failed bir-v3-differs "$f"; continue
      fi
    elif ! grep -q "need cpu v4" "$TMP/out"; then
      failed run-bir-v3 "$f"; continue
    fi
    # the allocated unit, under the bytecode convention
    # shellcheck disable=SC2086
    if ! "$KOITC" run --bytecode --cpu v4 $opts "$f" >"$TMP/out" 2>&1; then
      failed run-bytecode "$f"; continue
    fi
    if ! cmp -s "$TMP/core" "$TMP/out"; then
      echo "    core:"; sed 's/^/      /' "$TMP/core"
      failed bytecode-differs "$f"; continue
    fi
    pass=$((pass + 1))
  done
fi

# the shape of the compiled code: the syntactic part of Lemma L on
# every program
if at_least shape; then
  for f in tests/ok/*.ko tests/demo/*.ko tests/run/*.ko $SELF_OK $SELF_RUN; do
    [ -e "$f" ] || continue
    if "$KOITC" shape "$f" >"$TMP/out" 2>&1; then
      pass=$((pass + 1))
    else
      failed shape "$f"
    fi
  done
fi

# the C: every unit emits, and clang builds it for the BPF target
if at_least emit; then
  if [ -x "$CLANG" ] && "$CLANG" -target bpf -x c -c /dev/null -o /dev/null 2>/dev/null; then
    HAVE_CLANG=1
  else
    HAVE_CLANG=""
    echo "note: no clang with the BPF target at $CLANG; emitted C is not built"
  fi
  if [ -x "$LLVM_MC" ] && echo exit | "$LLVM_MC" --triple=bpf >/dev/null 2>&1; then
    HAVE_MC=1
  else
    HAVE_MC=""
    echo "note: no llvm-mc with the BPF target at $LLVM_MC; words are not disassembled"
  fi
  # one token per line, for comparing texts and byte streams
  norm() { sed 's/#.*$//; s/[[:space:]][[:space:]]*/ /g; s/^ //; s/ $//' | grep -v '^$'; }
  bytes() { grep -v '^#' | tr ', ' '\n\n' | grep -v '^$'; }
  for f in tests/ok/*.ko tests/demo/*.ko tests/run/*.ko $SELF_OK $SELF_RUN; do
    [ -e "$f" ] || continue
    if ! "$KOITC" emit "$f" >"$TMP/unit.c" 2>"$TMP/out"; then
      failed emit "$f"; continue
    fi
    if ! "$KOITC" emit --bytecode "$f" >"$TMP/words" 2>"$TMP/out"; then
      failed emit-bytecode "$f"; continue
    fi
    if ! "$KOITC" emit --json "$f" >"$TMP/unit.json" 2>"$TMP/out"; then
      failed emit-json "$f"; continue
    fi
    if command -v python3 >/dev/null 2>&1; then
      # the object file libbpf loads, from the document; readelf,
      # when present, must read it back
      if ! python3 tools/elf.py "$TMP/unit.json" -o "$TMP/unit.elf" >"$TMP/out" 2>&1; then
        failed elf "$f"; continue
      elif [ -x "$LLVM_READELF" ] && ! "$LLVM_READELF" -S -s -r "$TMP/unit.elf" >"$TMP/out" 2>&1; then
        failed readelf "$f"; continue
      fi
      if [ "$f" = tests/run/picker-vlan.ko ] &&
          ! python3 tools/test_koitobj.py "$TMP/unit.json" >"$TMP/out" 2>&1; then
        failed koitobj "$f"; continue
      fi
    fi
    if [ -n "$HAVE_MC" ]; then
      ok=1
      for cpu in v3 v4; do
        # a unit that needs v4's signed division has no v3 words
        if ! "$KOITC" emit --words --cpu $cpu "$f" >"$TMP/words" 2>"$TMP/out"; then
          grep -q "need cpu v4" "$TMP/out" && continue
          ok=""; break
        fi
        "$KOITC" emit --asm --cpu $cpu "$f" >"$TMP/asm" 2>"$TMP/out" || { ok=""; break; }
        # our words through LLVM's disassembler read as our text; the
        # disassembler knows no symbol, so a kfunc call reads as the
        # pseudo call it is, `call -1`
        "$LLVM_MC" --disassemble --triple=bpf -mcpu=$cpu <"$TMP/words" 2>"$TMP/out" | norm >"$TMP/dis"
        norm <"$TMP/asm" | sed 's/^call [A-Za-z_][A-Za-z_0-9]*$/call -1/' >"$TMP/ours"
        if ! cmp -s "$TMP/dis" "$TMP/ours"; then
          diff "$TMP/ours" "$TMP/dis" | head -20 >>"$TMP/out"; ok=""; break
        fi
        # our text through LLVM's assembler encodes as our words: the
        # text section of the object it writes, since a call to a
        # symbol has no encoding before the object is laid out
        "$LLVM_MC" --triple=bpf -mcpu=$cpu -filetype=obj -o "$TMP/mc.o" <"$TMP/asm" 2>"$TMP/out" &&
          "$LLVM_OBJCOPY" -O binary --only-section=.text "$TMP/mc.o" "$TMP/mc.bin" 2>>"$TMP/out" ||
          { ok=""; break; }
        od -An -v -tx1 "$TMP/mc.bin" | tr -s ' ' '\n' | grep -v '^$' | sed 's/^/0x/' >"$TMP/enc"
        bytes <"$TMP/words" >"$TMP/want"
        if ! cmp -s "$TMP/enc" "$TMP/want"; then
          diff "$TMP/want" "$TMP/enc" | head -20 >>"$TMP/out"; ok=""; break
        fi
      done
      [ -n "$ok" ] || { failed llvm-mc "$f"; continue; }
    fi
    if [ -n "$HAVE_CLANG" ]; then
      # -fno-builtin keeps clang from turning a byte loop into a memset
      # call, which the BPF backend has no way to emit
      if ! "$CLANG" -O2 -g -target bpf -fno-builtin -Wall -Wno-unused-label \
          -Wno-unused-variable -Wno-unused-but-set-variable -Werror -I tests/emit \
          -c "$TMP/unit.c" -o "$TMP/unit.o" >"$TMP/out" 2>&1; then
        failed clang "$f"; continue
      fi
    fi
    pass=$((pass + 1))
  done
fi

# the kernel: each run unit loaded and run on the host, its report
# against the expected block and against the model
if at_least kernel; then
  HOST=${KOIT_KERNEL_HOST:-}
  RDIR=${KOIT_KERNEL_DIR:-koit-kernel}
  if [ -z "$HOST" ]; then
    echo "note: KOIT_KERNEL_HOST is not set; nothing is run on a kernel"
  else
    ssh "$HOST" "mkdir -p $RDIR/logs" && scp -q tools/koitobj.py tools/load.py "$HOST:$RDIR/" ||
      { echo "cannot reach $HOST"; fail=$((fail + 1)); }
    for f in tests/run/*.ko $SELF_RUN; do
      [ -e "$f" ] || continue
      opts=$(sed -n '1s|^// run: ||p' "$f")
      mark=$(sed -n 's|^// kernel: ||p' "$f" | head -1)
      sed -n '2,/^$/{s|^// ||p;}' "$f" | grep -v '^kernel: ' >"$TMP/want"
      if ! "$KOITC" emit --json "$f" >"$TMP/unit.json" 2>"$TMP/out"; then
        failed emit-json "$f"; continue
      fi
      # shellcheck disable=SC2086
      "$KOITC" run --bytecode $opts "$f" 2>&1 | grep -v ': printk: ' >"$TMP/model"
      scp -q "$TMP/unit.json" "$HOST:$RDIR/unit.json" || { failed copy "$f"; continue; }
      # shellcheck disable=SC2086
      ssh "$HOST" "cd $RDIR && sudo python3 load.py unit.json $opts --log-dir logs" >"$TMP/out" 2>"$TMP/err"
      status=$?
      case "$mark" in
        rejected*)
          text=${mark#rejected }
          if [ "$status" -eq 0 ]; then
            echo "    the kernel accepted a unit marked rejected"; failed kernel "$f"
          elif ! grep -qF -- "$text" "$TMP/err"; then
            cat "$TMP/err" >>"$TMP/out"; failed kernel-cause "$f"
          else
            pass=$((pass + 1))
          fi
          continue ;;
      esac
      if [ "$status" -ne 0 ]; then
        cat "$TMP/err" >>"$TMP/out"; failed kernel "$f"; continue
      fi
      if [ "$mark" = "verdict only" ]; then
        grep -v '^map ' "$TMP/out" | grep -v '^  ' >"$TMP/got"
        grep -v '^map ' "$TMP/want" | grep -v '^  ' >"$TMP/w2"
        grep -v '^map ' "$TMP/model" | grep -v '^  ' >"$TMP/m2"
      else
        cp "$TMP/out" "$TMP/got"; cp "$TMP/want" "$TMP/w2"; cp "$TMP/model" "$TMP/m2"
      fi
      if ! cmp -s "$TMP/got" "$TMP/w2"; then
        echo "    expected:"; sed 's/^/      /' "$TMP/w2"; cp "$TMP/got" "$TMP/out"
        failed kernel-output "$f"
      elif ! cmp -s "$TMP/got" "$TMP/m2"; then
        echo "    model:"; sed 's/^/      /' "$TMP/m2"; cp "$TMP/got" "$TMP/out"
        failed kernel-differs "$f"
      else
        pass=$((pass + 1))
      fi
    done
  fi
fi

echo "$pass passed, $fail failed, $skipped skipped, $pending pending, $refused refused"
[ "$fail" -eq 0 ]
