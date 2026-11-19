#!/bin/bash
# Locked checker for the N = 10 trial. Usage, on mpro: check.sh <lane repo clone> <base commit>
# Pass = the lane changed no tracked file except lean/Packing.lean and lean/Audit.lean,
# no lean file uses sorry or native_decide, Check10.lean compiles, and the axiom line is the
# three standard axioms.
set -u
export PATH="$HOME/.elan/bin:$PATH"
repo=$1
base=$2
here=$(cd "$(dirname "$0")" && pwd)
fail() { echo "FAIL: $*"; exit 1; }

changed=$(git -C "$repo" diff --name-only --diff-filter=a "$base" -- . | grep -v -x -e lean/Packing.lean -e lean/Audit.lean)
[ -z "$changed" ] || fail "tracked files changed: $changed"

if grep -rn -E '\bsorry\b|native_decide' "$repo/lean/Packing" --include='*.lean'; then
  fail "sorry or native_decide present"
fi

out=$(cd "$repo/lean" && lake env lean "$here/Check10.lean" 2>&1)
rc=$?
echo "$out"
[ $rc -eq 0 ] || fail "Check10.lean did not compile (rc $rc)"
echo "$out" | grep -q -F "'Packing.Cube.isMaxMinDist_ten' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  || fail "axiom line is not the three standard axioms"
echo PASS
