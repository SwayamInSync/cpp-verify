#!/bin/bash
# Runs every Verify test program through a cpp-verify built with
# -DCPPVERIFY_SANITIZER="address;undefined" and fails when a sanitizer reports
# anything. Verdicts are not compared: the sanitizers slow the verifier, and
# lit checks verdicts.
#
# usage: cppverify-sanitize.sh BUILD_DIR [PARALLEL]
#
# LLVM's allocators poison memory in the instrumented code's copies of their
# inline functions, which the uninstrumented libraries then use, so poisoning
# by hand is off; threads get 1 GiB stacks, since instrumented frames are many
# times larger and the counterexample checker recurses deeply. Each program
# runs with two jobs, so the pool runs under the sanitizers too.
set -u
BUILD=$1
PARALLEL=${2:-$(nproc)}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
TESTS=$ROOT/clang/test/Verify
OUT=$(mktemp -d)
export OUT TESTS
export CPPVERIFY=$BUILD/bin/cpp-verify
export ASAN_OPTIONS=detect_leaks=0:allow_user_poisoning=0
export UBSAN_OPTIONS=print_stacktrace=1
ulimit -s 1048576

run() {
  local file=$1 name
  name=$(echo "${file#$TESTS/}" | tr / _)
  timeout -k 60 900 "$CPPVERIFY" --timeout=5000 --jobs=2 "$file" -- \
    "-I$TESTS/suite/Inputs" > "$OUT/$name.txt" 2>&1
  return 0
}
export -f run

find "$TESTS" -name '*.cpp' -not -path '*/Inputs/*' -print0 |
  xargs -0 -P "$PARALLEL" -I{} bash -c 'run "$1"' _ {}

reports=$(grep -l -E 'ERROR: AddressSanitizer|runtime error:' "$OUT"/*.txt)
programs=$(find "$TESTS" -name '*.cpp' -not -path '*/Inputs/*' | wc -l)
if [ -z "$reports" ]; then
  echo "no reports in $programs programs"
  exit 0
fi
for report in $reports; do
  echo "=== $(basename "$report" .txt)"
  grep -m1 -A40 -E 'ERROR: AddressSanitizer|runtime error:' "$report"
done
echo "reports in $(echo "$reports" | wc -l) of $programs programs"
mkdir -p sanitizer-reports && cp $reports sanitizer-reports/
exit 1
