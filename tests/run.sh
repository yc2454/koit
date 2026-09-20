#!/bin/sh
# Builds koitc and runs it over the corpus.
#
#   tests/ok/*.ko     must parse and desugar; at the check stage, must
#                     also check
#   tests/err/*.ko    must parse and desugar; at the check stage,
#                     `koitc check` must reject the file with a
#                     diagnostic containing the text after
#                     `// expect: ` on line 1
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
# stage notes it and checks the rest.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$HOME/.elan/bin:$PATH"
lake build koitc >/dev/null || { echo "build failed"; exit 2; }
KOITC=.lake/build/bin/koitc
STAGE=${KOIT_STAGE:-parse}
CLANG=${KOIT_CLANG:-/opt/homebrew/opt/llvm/bin/clang}
LLVM_MC=${KOIT_LLVM_MC:-/opt/homebrew/opt/llvm/bin/llvm-mc}
# the stages in order, so that a stage includes the ones before it
rank() {
  case "$1" in
    lex) echo 0 ;; parse) echo 1 ;; check) echo 2 ;; run) echo 3 ;;
    lower) echo 4 ;; shape) echo 5 ;; emit) echo 6 ;; *) echo 1 ;;
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

for f in tests/ok/*.ko tests/err/*.ko tests/parse/*.ko tests/corpus/*.ko tests/run/*.ko; do
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
  for f in tests/ok/*.ko; do
    if "$KOITC" check "$f" >"$TMP/out" 2>&1; then
      pass=$((pass + 1))
    else
      failed check "$f"
    fi
  done
  for f in tests/err/*.ko tests/corpus/*.ko; do
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
    else
      pass=$((pass + 1))
    fi
  done
fi

if at_least run; then
  for f in tests/ok/*.ko; do
    if "$KOITC" run "$f" >"$TMP/out" 2>&1; then
      pass=$((pass + 1))
    else
      failed run "$f"
    fi
  done
  for f in tests/run/*.ko; do
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
  for f in tests/ok/*.ko tests/run/*.ko; do
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
  for f in tests/ok/*.ko tests/run/*.ko; do
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
  for f in tests/ok/*.ko tests/run/*.ko; do
    [ -e "$f" ] || continue
    if ! "$KOITC" emit "$f" >"$TMP/unit.c" 2>"$TMP/out"; then
      failed emit "$f"; continue
    fi
    if ! "$KOITC" emit --bytecode "$f" >"$TMP/words" 2>"$TMP/out"; then
      failed emit-bytecode "$f"; continue
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
        # our words through LLVM's disassembler read as our text
        "$LLVM_MC" --disassemble --triple=bpf -mcpu=$cpu <"$TMP/words" 2>"$TMP/out" | norm >"$TMP/dis"
        norm <"$TMP/asm" >"$TMP/ours"
        if ! cmp -s "$TMP/dis" "$TMP/ours"; then
          diff "$TMP/ours" "$TMP/dis" | head -20 >>"$TMP/out"; ok=""; break
        fi
        # our text through LLVM's assembler encodes as our words
        "$LLVM_MC" --triple=bpf -mcpu=$cpu -show-encoding <"$TMP/asm" 2>"$TMP/out" |
          sed -n 's/.*encoding: \[\(.*\)\].*/\1/p' | bytes >"$TMP/enc"
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

echo "$pass passed, $fail failed, $skipped skipped"
[ "$fail" -eq 0 ]
