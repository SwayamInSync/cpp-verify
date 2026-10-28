#!/usr/bin/env bash
# Checks the cpp-verify and clang++ in the directory $1: what --version
# reports, a correct program verified and compiled with its contracts
# verified, and an incorrect one rejected by both, with its counterexample in
# text and in JSON.
set -euo pipefail

BIN="$1"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

fail() {
  echo "error: $1" >&2
  exit 1
}

cat > "$WORK/good.cpp" <<'EOF'
#include <cstdint>
#include <filesystem>
#include <vector>

namespace cv = cppverify;

int abs_value(int x)
  cv::pre(x > INT32_MIN)
  cv::post(cv::result >= 0)
{
  return x < 0 ? -x : x;
}
EOF

cat > "$WORK/bad.cpp" <<'EOF'
namespace cv = cppverify;

int twice(int x)
  cv::pre(x >= 0 && x <= 1000)
  cv::post(cv::result == 2 * x + 1)
{
  return 2 * x;
}
EOF

"$BIN/cpp-verify" --version | tee "$WORK/version.txt"
grep -Eq '^cpp-verify [0-9]+\.[0-9]+\.[0-9]+' "$WORK/version.txt" ||
  fail "--version does not start with cpp-verify's version"
grep -Eq '^  based on LLVM [0-9]+\.[0-9]+\.[0-9]+' "$WORK/version.txt" ||
  fail "--version names no LLVM release"
grep -Eq '^  z3 +[0-9]+\.[0-9]+\.[0-9]+ +built in' "$WORK/version.txt" ||
  fail "--version names no built-in Z3"

"$BIN/cpp-verify" "$WORK/good.cpp" | tee "$WORK/good.txt"
grep -q "Verified: abs_value" "$WORK/good.txt" ||
  fail "the correct program did not verify"

if "$BIN/cpp-verify" "$WORK/bad.cpp" > "$WORK/bad.txt" 2>&1; then
  cat "$WORK/bad.txt"
  fail "the incorrect program verified"
fi
cat "$WORK/bad.txt"
grep -q "verification failed: twice" "$WORK/bad.txt" ||
  fail "the incorrect program's failure is missing"
grep -Eq "counterexample: x( \[[^]]*\])* = " "$WORK/bad.txt" ||
  fail "the incorrect program's counterexample is missing"

if "$BIN/cpp-verify" --diagnostics-format=json "$WORK/bad.cpp" \
    > "$WORK/bad.json" 2> /dev/null; then
  fail "the incorrect program verified with --diagnostics-format=json"
fi
cat "$WORK/bad.json"
grep -q '"function":"twice"' "$WORK/bad.json" &&
  grep -q '"status":"failed"' "$WORK/bad.json" &&
  grep -q '"name":"x"' "$WORK/bad.json" ||
  fail "the incorrect program's JSON record is missing"

"$BIN/clang++" -std=c++17 -fverify-contracts -c "$WORK/good.cpp" \
  -o "$WORK/good.o"
test -s "$WORK/good.o" || fail "clang++ wrote no object for the correct program"

if "$BIN/clang++" -std=c++17 -fverify-contracts -c "$WORK/bad.cpp" \
    -o "$WORK/bad.o" > "$WORK/bad-clang.txt" 2>&1; then
  cat "$WORK/bad-clang.txt"
  fail "clang++ -fverify-contracts compiled the incorrect program"
fi
cat "$WORK/bad-clang.txt"
grep -q "error: verification failed: twice" "$WORK/bad-clang.txt" ||
  fail "clang++ did not report the incorrect program's failure"
test ! -e "$WORK/bad.o" || fail "clang++ wrote an object for the incorrect program"

echo "smoke test passed"
