#!/bin/sh
# Builds koitc and runs it over the corpus.
#
#   tests/ok/*.ko     must parse; from session 2 on, must also check
#   tests/err/*.ko    must parse; from session 2 on, `koitc check` must
#                     reject the file with a diagnostic containing the
#                     text after `// expect: ` on line 1
#   tests/parse/*.ko  must parse; nothing is claimed about typing
#
# Every file that parses must also round-trip: printing it as source
# and parsing and printing that again must give the same text.
#
# KOIT_STAGE=lex, parse (the default), or check selects how far the run
# goes.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$HOME/.elan/bin:$PATH"
lake build koitc >/dev/null || { echo "build failed"; exit 2; }
KOITC=.lake/build/bin/koitc
STAGE=${KOIT_STAGE:-parse}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
pass=0
fail=0

failed() {
  echo "FAIL $1 $2"
  [ -s "$TMP/out" ] && sed 's/^/    /' "$TMP/out"
  fail=$((fail + 1))
}

for f in tests/ok/*.ko tests/err/*.ko tests/parse/*.ko; do
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
  for f in tests/err/*.ko; do
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

echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
