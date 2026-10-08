#!/usr/bin/env bash
# Verifies a correct and an incorrect program with the cpp-verify and clang++
# in the directory $1, and compiles the correct one with contracts verified.
set -euo pipefail

BIN="$1"
WORK="$(mktemp -d)"

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

"$BIN/cpp-verify" --version

"$BIN/cpp-verify" "$WORK/good.cpp" | tee "$WORK/good.txt"
grep -q "Verified: abs_value" "$WORK/good.txt"

if "$BIN/cpp-verify" "$WORK/bad.cpp" > "$WORK/bad.txt" 2>&1; then
  cat "$WORK/bad.txt"
  echo "error: the incorrect program verified" >&2
  exit 1
fi
cat "$WORK/bad.txt"
grep -q "verification failed: twice" "$WORK/bad.txt"

"$BIN/clang++" -std=c++17 -fverify-contracts -c "$WORK/good.cpp" -o "$WORK/good.o"
echo "smoke test passed"
