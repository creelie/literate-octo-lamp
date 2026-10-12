#!/usr/bin/env bash
# run_all.sh -- re-run every check of "Distinct abelian squares in binary circular words".
#
#   C       verification/c/circsq.c            every binary word of length n <= 22: the minimum
#                                              floor((n-1)/2) and the list of words attaining it
#   C++     verification/cpp/necklaces.cpp     one word per necklace, n <= 28, Conjecture 0.6 (a)
#                                              and the failure of the uniqueness in (b)
#   Shell   verification/shell/check_small.sh  bash integer arithmetic only, n <= 10
#   Python  verification/python/verify_simpson.py  from the definitions (all rotations, all
#                                              splits, Parikh vectors), n <= 12
#   Julia   verification/julia/verify_lemmas.jl    every lemma of the proof, n <= 16
#                                              (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean                  the theorems for every n, over Mathlib v4.34.1
#                                              (if lake is on PATH; LEAN=0 skips it)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/circsq" "$V/c/circsq.c" || fail "compile circsq.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/necklaces" "$V/cpp/necklaces.cpp" || fail "compile necklaces.cpp"
"$BUILD/circsq" > "$BUILD/c.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/c.txt" \
  && ok "C: every binary circular word of length n <= 22" || fail "C (see build/c.txt)"
"$BUILD/necklaces" > "$BUILD/cpp.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/cpp.txt" \
  && ok "C++: every necklace of length n <= 28" || fail "C++ (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_small.sh" > "$BUILD/sh.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh.txt" \
  && ok "check_small.sh" || fail "check_small.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_simpson.py" > "$BUILD/py.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py.txt" \
  && ok "verify_simpson.py" || fail "verify_simpson.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_lemmas.jl" > "$BUILD/jl.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl.txt" \
    && ok "verify_lemmas.jl" || fail "verify_lemmas.jl (see build/jl.txt)"
fi

echo "== Lean"
if [ "${LEAN:-1}" = 0 ]; then echo "Lean skipped (LEAN=0)";
elif ! command -v lake > /dev/null; then echo "lake not found: skipping (install elan)"; else
  if grep -rqE '\bsorry\b|\badmit\b|native_decide|^axiom ' "$V/lean/Circ" "$V/lean/Circ.lean"; then
    fail "Lean sources contain sorry, admit, native_decide or an axiom"
  fi
  out=$(cd "$V/lean" && { lake exe cache get > /dev/null 2>&1 || true; } && lake build 2>&1 \
        && lake env lean Axioms.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out")
  if [ $st -eq 0 ] && ! grep -q "error\|sorryAx" <<< "$out" && [ "$n" = 6 ]; then
    ok "Lean: six theorems, axioms propext, Classical.choice, Quot.sound only"
  else fail "Lean (see build/lean.txt)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
