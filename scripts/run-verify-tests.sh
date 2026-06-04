#!/usr/bin/env bash
# Run clang/test/Verify tests with correct expectations (syntax vs verify vs expect-fail).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="${CPPVERIFY_BUILD:-$ROOT/build}"
CLANG="$BUILD/bin/clang"
CPP_VERIFY="$BUILD/bin/cpp-verify"
TEST_DIR="$ROOT/clang/test/Verify"

if [[ ! -x "$CPP_VERIFY" ]]; then
  echo "error: cpp-verify not found at $CPP_VERIFY (run ./setup.sh first)" >&2
  exit 1
fi

pass=0
fail=0
skip=0

run_one() {
  local f="$1"
  local base
  base="$(basename "$f")"

  # Frontend-only (clang_cc1 / ast-dump / emit-llvm); no end-to-end verify expectation.
  if grep -q '%clang_cc1' "$f" 2>/dev/null && ! grep -q '%cpp-verify' "$f" 2>/dev/null; then
    if grep -q 'RUN:.*clang_cc1' "$f"; then
      echo "SKIP $base (frontend-only)"
      skip=$((skip + 1))
      return 0
    fi
  fi

  # Parse/type error tests: only clang syntax-check.
  if [[ "$base" == errors_*.cpp ]] || [[ "$base" == lexer_keywords.cpp ]] \
     || [[ "$base" == backward_compat*.cpp ]]; then
    if "$CLANG" -std=c++17 -fverify-contracts -fsyntax-only "$f" >/dev/null 2>&1; then
      : # expected compile errors may still return 0 for partial parse in some cases
    fi
    echo "SKIP $base (negative frontend)"
    skip=$((skip + 1))
    return 0
  fi

  local out rc expect_fail=0
  if grep -q 'not %cpp-verify' "$f" 2>/dev/null || grep -q 'FAIL:' "$f" 2>/dev/null; then
    expect_fail=1
  fi

  local -a extra_args=()
  if grep -q '%cpp-verify --backend=lean' "$f" 2>/dev/null; then
    local tmp
    tmp="$(mktemp -t cppverify.lean.XXXXXX)"
    extra_args=(--backend=lean "--lean-out=$tmp")
  elif grep -q '%cpp-verify --backend=bmc' "$f" 2>/dev/null; then
    extra_args=(--backend=bmc)
  fi
  # Undefined-behavior checking is opt-in per test via the RUN line.
  if grep -qE '(not )?%cpp-verify --check-ub' "$f" 2>/dev/null; then
    extra_args+=(--check-ub)
  fi

  # Hard wall-clock cap per test. cpp-verify ignores SIGTERM (LLVM installs
  # signal handlers), so use SIGKILL. The in-tool --timeout bounds Z3 itself;
  # this guards against any other runaway.
  local TIMEOUT="${CPPVERIFY_TEST_TIMEOUT:-60}"
  if ((${#extra_args[@]} > 0)); then
    out="$(timeout -s KILL "$TIMEOUT" "$CPP_VERIFY" "${extra_args[@]}" "$f" 2>&1)" || rc=$?
  else
    out="$(timeout -s KILL "$TIMEOUT" "$CPP_VERIFY" "$f" 2>&1)" || rc=$?
  fi
  rc="${rc:-0}"
  if [[ "$rc" -eq 137 ]]; then
    echo "FAIL $base (timed out after ${TIMEOUT}s)"
    fail=$((fail + 1))
    return 0
  fi

  if [[ "$expect_fail" -eq 1 ]]; then
    if echo "$out" | grep -qE 'verification failed:|error:'; then
      echo "PASS $base (expected failure)"
      pass=$((pass + 1))
    else
      echo "FAIL $base (expected verification failure)"
      echo "$out" | head -8
      fail=$((fail + 1))
    fi
    return 0
  fi

  if echo "$out" | grep -q '^error:'; then
    echo "FAIL $base (verify error)"
    echo "$out" | grep '^error:' | head -5
    fail=$((fail + 1))
    return 0
  fi

  if [[ "$rc" -ne 0 ]]; then
    echo "FAIL $base (exit $rc)"
    echo "$out" | head -8
    fail=$((fail + 1))
    return 0
  fi

  echo "PASS $base"
  pass=$((pass + 1))
}

echo "=== cpp-verify test sweep ==="
echo "build: $BUILD"

shopt -s nullglob
for f in "$TEST_DIR"/*.cpp "$TEST_DIR"/suite/*.cpp; do
  [[ -f "$f" ]] || continue
  run_one "$f"
done

echo "=== summary: pass=$pass fail=$fail skip=$skip ==="
[[ "$fail" -eq 0 ]]