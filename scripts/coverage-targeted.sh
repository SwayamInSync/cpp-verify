#!/usr/bin/env bash
# Fast incremental coverage sweep (no cmake reconfigure). Merges after each batch.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="${CPPVERIFY_BUILD:-$ROOT/build}"
COV_DIR="$BUILD/coverage-verify"
PROFDATA="$COV_DIR/verify.profdata"
THRESHOLD="${CPPVERIFY_COV_THRESHOLD:-90}"
SUITE="$ROOT/clang/test/Verify/suite"

LLVM_COV="$BUILD/bin/llvm-cov"
LLVM_PROFDATA="$BUILD/bin/llvm-profdata"
mkdir -p "$COV_DIR"
export LLVM_PROFILE_FILE="$COV_DIR/tgt_%p.profraw"

merge_profiles() {
  shopt -s nullglob
  local files=("$COV_DIR"/tgt_*.profraw)
  shopt -u nullglob
  [[ ${#files[@]} -eq 0 ]] && return 0
  if [[ -f "$PROFDATA" ]]; then
    "$LLVM_PROFDATA" merge -sparse "$PROFDATA" "${files[@]}" -o "$PROFDATA.new"
    mv "$PROFDATA.new" "$PROFDATA"
  else
    "$LLVM_PROFDATA" merge -sparse "${files[@]}" -o "$PROFDATA"
  fi
  rm -f "${files[@]}"
}

run() {
  "$BUILD/bin/cpp-verify" "$@" >/dev/null 2>&1 || true
  merge_profiles
}

LEAN="$COV_DIR/lean.lean"
TESTS=(
  cov_mega_sweep.cpp cov_spec_advanced.cpp cov_bmc_body_stmts.cpp
  cov_proof_decreases.cpp cov_dump_full.cpp cov_multi_spec_z3.cpp
  cov_spec_lean_inline.cpp cov_spec_bmc_inline.cpp cov_loop_nested_bmc.cpp
  cov_lean_heap.cpp cov_lean_quant.cpp cov_exists.cpp cov_constexpr_spec.cpp
  cov_recommends_fail.cpp z3_modular_chained.cpp z3_hide_reveal_fuel.cpp
  z3_heap_swap.cpp z3_spec_proof_axioms.cpp bmc_loop_sum.cpp spec_inline_simple.cpp
  dump_ir_layers.cpp compile_with_verify.cpp
)

for t in "${TESTS[@]}"; do
  f="$SUITE/$t"
  [[ -f "$f" ]] || f="$ROOT/clang/test/Verify/$t"
  [[ -f "$f" ]] || continue
  run "$f"
  case "$t" in
    *bmc*|bmc_*) run --backend=bmc --unroll=3 "$f"
      run --backend=bmc --unroll=0 "$f" ;;
    *lean*) run --backend=lean "--lean-out=$LEAN" "$f" ;;
    *dump*) run --dump-ir=all "$f" ;;
  esac
done

if [[ -x "$BUILD/bin/clang" ]]; then
  export LLVM_PROFILE_FILE="$COV_DIR/clang_%p.profraw"
  for f in "$ROOT/clang/test/Verify/compile_with_verify.cpp" "$SUITE"/cov_mega_sweep.cpp; do
    [[ -f "$f" ]] || continue
    "$BUILD/bin/clang" -std=c++17 -fverify-contracts -c "$f" -o "$COV_DIR/$(basename "$f").o" >/dev/null 2>&1 || true
  done
  shopt -s nullglob
  clang_files=("$COV_DIR"/clang_*.profraw)
  shopt -u nullglob
  if [[ ${#clang_files[@]} -gt 0 ]]; then
    "$LLVM_PROFDATA" merge -sparse "$PROFDATA" "${clang_files[@]}" -o "$PROFDATA.new"
    mv "$PROFDATA.new" "$PROFDATA"
    rm -f "${clang_files[@]}"
  fi
fi

OBJ_DIR="$BUILD/tools/clang/lib/Verify/CMakeFiles/obj.clangVerify.dir"
OBJ_FILES=("$OBJ_DIR"/*/*.o)
REPORT="$COV_DIR/report-targeted.txt"
"$LLVM_COV" report "$BUILD/bin/cpp-verify" "$BUILD/bin/clang" \
  -instr-profile="$PROFDATA" "${OBJ_FILES[@]}" >"$REPORT" 2>/dev/null

grep 'clang/lib/Verify' "$REPORT" | awk '{reg+=$2; miss+=$3} END {
  if (reg>0) printf "TOTAL Verify regions: %.2f%% (%d/%d)\n", 100*(reg-miss)/reg, reg-miss, reg;
}'
REGIONS="$(grep 'clang/lib/Verify' "$REPORT" | awk '{reg+=$2; miss+=$3} END {
  if (reg>0) printf "%.2f", 100*(reg-miss)/reg; else print "0"
}')"
echo "=== TOTAL regions: ${REGIONS}% (threshold ${THRESHOLD}%) ==="
python3 - <<PY
import sys
sys.exit(0 if float("${REGIONS}") >= float("${THRESHOLD}") else 1)
PY