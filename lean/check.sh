#!/bin/sh
# Check every generated verification file; prints one line per file.
pass=0; fail=0
for f in generated/*.lean; do
  if out=$(lake env lean "$f" 2>&1 | grep -E "error" | head -3) && [ -z "$out" ]; then pass=$((pass+1)); echo "ok   $f"; else fail=$((fail+1)); echo "FAIL $f"; echo "$out"; fi
done
echo "$pass passed, $fail failed"
