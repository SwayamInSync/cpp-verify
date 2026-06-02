#!/usr/bin/env bash
# Build cpp-verify with LLVM coverage instrumentation and report clangVerify line coverage.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="${CPPVERIFY_BUILD:-$ROOT/build}"
COV_DIR="$BUILD/coverage-verify"
PROFDATA="$COV_DIR/verify.profdata"
PROFILE_RAW="$COV_DIR/profile-%m.profraw"
THRESHOLD="${CPPVERIFY_COV_THRESHOLD:-90}"

REPO="$ROOT"
CMAKE="$BUILD/bin/llvm-cmake" 2>/dev/null || true
LLVM_COV="${LLVM_COV:-$(command -v llvm-cov 2>/dev/null || true)}"
LLVM_PROFDATA="${LLVM_PROFDATA:-$(command -v llvm-profdata 2>/dev/null || true)}"
if [[ -x "$BUILD/bin/llvm-cov" ]]; then
  LLVM_COV="$BUILD/bin/llvm-cov"
fi
if [[ -x "$BUILD/bin/llvm-profdata" ]]; then
  LLVM_PROFDATA="$BUILD/bin/llvm-profdata"
fi
if [[ -z "$LLVM_COV" || -z "$LLVM_PROFDATA" ]]; then
  echo "error: need llvm-cov and llvm-profdata (build LLVM tools or install brew llvm)" >&2
  exit 1
fi

mkdir -p "$COV_DIR"

echo "=== Reconfiguring with coverage flags (clangVerify + cpp-verify) ==="
cmake -S "$ROOT/llvm" -B "$BUILD" \
  -DCMAKE_BUILD_TYPE=Debug \
  -DLLVM_ENABLE_PROJECTS=clang \
  -DLLVM_TARGETS_TO_BUILD=host \
  -DCPPVERIFY_VENDOR_Z3=ON \
  -DCPPVERIFY_ENABLE_COVERAGE=ON \
  -DCMAKE_CXX_FLAGS= \
  -DCMAKE_C_FLAGS= \
  -DCMAKE_EXE_LINKER_FLAGS= \
  -DCMAKE_SHARED_LINKER_FLAGS= \
  >/dev/null

ninja -C "$BUILD" clang clangVerify cpp-verify

export LLVM_PROFILE_FILE="$COV_DIR/cppverify_%p.profraw"
rm -f "$COV_DIR"/*.profraw "$PROFDATA" 2>/dev/null || true

merge_profiles() {
  shopt -s nullglob
  local files=("$COV_DIR"/*.profraw)
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

echo "=== Running verification tests for profile ==="
"$ROOT/scripts/run-verify-tests.sh" || true

# CodeGen integration path (CppVerifyIntegration async hook).
if [[ -x "$BUILD/bin/clang" ]]; then
  CLANG_COV="$COV_DIR/clang_%p.profraw"
  export LLVM_PROFILE_FILE="$CLANG_COV"
  for f in "$ROOT/clang/test/Verify/compile_with_verify.cpp" \
           "$ROOT/clang/test/Verify/suite"/{cov_*,z3_*,bmc_*,spec_*,modular*,chained*}.cpp; do
    [[ -f "$f" ]] || continue
    "$BUILD/bin/clang" -std=c++17 -fverify-contracts -c "$f" \
      -o "$COV_DIR/$(basename "$f" .cpp).o" >/dev/null 2>&1 || true
  done
  FAIL_SRC="$COV_DIR/cov_verify_fail.cpp"
  printf '%s\n' 'int bad() pre(false) post(result == 0) { return 1; }' >"$FAIL_SRC"
  "$BUILD/bin/clang" -std=c++17 -fverify-contracts -c "$FAIL_SRC" -o "$COV_DIR/cov_verify_fail.o" \
    >/dev/null 2>&1 || true
  "$BUILD/bin/clang" -std=c++17 -fverify-contracts -fno-verify -c \
    "$ROOT/clang/test/Verify/compile_with_verify.cpp" -o "$COV_DIR/compile_no_verify.o" \
    >/dev/null 2>&1 || true
  merge_profiles
  export LLVM_PROFILE_FILE="$COV_DIR/cppverify_%p.profraw"
fi

merge_profiles

# Lean backend edge cases.
"$BUILD/bin/cpp-verify" --backend=lean \
  "$ROOT/clang/test/Verify/suite/z3_modular_call.cpp" >/dev/null 2>&1 || true

# Extra suite sweep to hit backend branches.
SUITE="$ROOT/clang/test/Verify/suite"
if [[ -d "$SUITE" ]]; then
  LEAN_TMP="$COV_DIR/lean_scratch.lean"
  for f in "$SUITE"/*.cpp; do
    "$BUILD/bin/cpp-verify" "$f" >/dev/null 2>&1 || true
    case "$(basename "$f")" in
      cov_*bmc*|*bmc*.cpp|cov_loop*) "$BUILD/bin/cpp-verify" --backend=bmc --unroll=3 "$f" >/dev/null 2>&1 || true
        "$BUILD/bin/cpp-verify" --backend=bmc --unroll=0 "$f" >/dev/null 2>&1 || true ;;
      cov_*lean*|lean*.cpp) "$BUILD/bin/cpp-verify" --backend=lean "--lean-out=$LEAN_TMP" "$f" >/dev/null 2>&1 || true ;;
      cov_dump*|dump_ir*) "$BUILD/bin/cpp-verify" --dump-ir=all "$f" >/dev/null 2>&1 || true ;;
    esac
  done
  rm -f "$LEAN_TMP"
  merge_profiles
  # DumpIR layer parsing branches.
  if [[ -f "$SUITE/dump_ir_layers.cpp" ]]; then
    for layers in 1 2 3 4 "layer-3,layer-4" all; do
      "$BUILD/bin/cpp-verify" "--dump-ir=$layers" "$SUITE/dump_ir_layers.cpp" >/dev/null 2>&1 || true
    done
  fi
  for f in "$ROOT/clang/test/Verify"/*.cpp; do
    [[ -f "$f" ]] || continue
    "$BUILD/bin/cpp-verify" "$f" >/dev/null 2>&1 || true
    "$BUILD/bin/cpp-verify" --dump-ir=all "$f" >/dev/null 2>&1 || true
    "$BUILD/bin/cpp-verify" --backend=lean "--lean-out=$LEAN_TMP" "$f" >/dev/null 2>&1 || true
  done
  merge_profiles
fi

echo "=== Merging profiles ==="
merge_profiles

OBJ_DIR="$BUILD/tools/clang/lib/Verify/CMakeFiles/obj.clangVerify.dir"
if [[ ! -d "$OBJ_DIR" ]]; then
  echo "error: object dir not found: $OBJ_DIR" >&2
  exit 1
fi

REPORT="$COV_DIR/report.txt"
echo "=== Coverage report (clang/lib/Verify) ==="
OBJ_FILES=("$OBJ_DIR"/*/*.o)
if [[ ! -e "${OBJ_FILES[0]}" ]]; then
  OBJ_FILES=("$OBJ_DIR"/*.o)
fi
COV_BINARIES=("$BUILD/bin/cpp-verify")
[[ -x "$BUILD/bin/clang" ]] && COV_BINARIES+=("$BUILD/bin/clang")
"$LLVM_COV" report "${COV_BINARIES[@]}" \
  -instr-profile="$PROFDATA" "${OBJ_FILES[@]}" \
  > "$REPORT" 2>/dev/null

echo "--- clang/lib/Verify only (regions) ---"
grep 'clang/lib/Verify' "$REPORT" | awk '{reg+=$2; miss+=$3} END {
  if (reg>0) printf "TOTAL Verify regions: %.2f%% (%d/%d)\n", 100*(reg-miss)/reg, reg-miss, reg;
  else print "no Verify rows"
}'

cat "$REPORT"
REGIONS="$(grep 'clang/lib/Verify' "$REPORT" | awk '{reg+=$2; miss+=$3} END {
  if (reg>0) printf "%.2f", 100*(reg-miss)/reg; else print "0"
}')"
echo "=== TOTAL regions line coverage: ${REGIONS}% (threshold ${THRESHOLD}%) ==="
python3 - <<PY
import sys
r = float("${REGIONS}")
t = float("${THRESHOLD}")
sys.exit(0 if r >= t else 1)
PY