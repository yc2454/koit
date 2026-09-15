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
# KOIT_STAGE=lex, parse (the default), or check selects how far the run
# goes. The err files in LATER need effects, guards, or `move`, which
# session 5 delivers; the check stage skips them until then.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$HOME/.elan/bin:$PATH"
lake build koitc >/dev/null || { echo "build failed"; exit 2; }
KOITC=.lake/build/bin/koitc
STAGE=${KOIT_STAGE:-parse}
LATER="call-under-lock move-join view-invalidated"
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

for f in tests/ok/*.ko tests/err/*.ko tests/parse/*.ko tests/corpus/*.ko; do
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

if [ "$STAGE" = check ]; then
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
      echo "skip $f (session 5)"
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

echo "$pass passed, $fail failed, $skipped skipped"
[ "$fail" -eq 0 ]
