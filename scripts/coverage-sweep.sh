#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="${CPPVERIFY_BUILD:-$ROOT/build}"
COV_DIR="$BUILD/coverage-verify"
PROFDATA="$COV_DIR/verify.profdata"
SUITE="$ROOT/clang/test/Verify/suite"
LEAN="$COV_DIR/lean.lean"

export LLVM_PROFILE_FILE="$COV_DIR/p_%p.profraw"

merge_profiles() {
  shopt -s nullglob
  local files=("$COV_DIR"/p_*.profraw "$COV_DIR"/clang_*.profraw)
  shopt -u nullglob
  [[ ${#files[@]} -eq 0 ]] && return 0
  if [[ -f "$PROFDATA" ]]; then
    "$BUILD/bin/llvm-profdata" merge -sparse "$PROFDATA" "${files[@]}" -o "$PROFDATA.new"
    mv "$PROFDATA.new" "$PROFDATA"
  else
    "$BUILD/bin/llvm-profdata" merge -sparse "${files[@]}" -o "$PROFDATA"
  fi
  rm -f "${files[@]}"
}

n=0
for f in "$SUITE"/*.cpp; do
  "$BUILD/bin/cpp-verify" "$f" >/dev/null 2>&1 || true
  "$BUILD/bin/cpp-verify" --backend=bmc --unroll=3 "$f" >/dev/null 2>&1 || true
  "$BUILD/bin/cpp-verify" --backend=bmc --unroll=0 "$f" >/dev/null 2>&1 || true
  "$BUILD/bin/cpp-verify" --backend=lean "--lean-out=$LEAN" "$f" >/dev/null 2>&1 || true
  "$BUILD/bin/cpp-verify" --dump-ir=all "$f" >/dev/null 2>&1 || true
  n=$((n + 1))
  if (( n % 12 == 0 )); then
    merge_profiles
  fi
done
merge_profiles

if [[ -x "$BUILD/bin/clang" ]]; then
  export LLVM_PROFILE_FILE="$COV_DIR/clang_%p.profraw"
  for f in "$ROOT/clang/test/Verify/compile_with_verify.cpp" \
           "$SUITE"/cov_mega_sweep.cpp; do
    [[ -f "$f" ]] || continue
    "$BUILD/bin/clang" -std=c++17 -fverify-contracts -c "$f" \
      -o "$COV_DIR/$(basename "$f").o" >/dev/null 2>&1 || true
  done
  merge_profiles
fi

OBJ_DIR="$BUILD/tools/clang/lib/Verify/CMakeFiles/obj.clangVerify.dir"
"$BUILD/bin/llvm-cov" report "$BUILD/bin/cpp-verify" "$BUILD/bin/clang" \
  -instr-profile="$PROFDATA" "$OBJ_DIR"/*/*.o 2>/dev/null \
  | awk '/clang\/lib\/Verify/{reg+=$2; miss+=$3} END{
      if (reg>0) printf "TOTAL Verify regions: %.2f%% (%d/%d)\n", 100*(reg-miss)/reg, reg-miss, reg;
    }'