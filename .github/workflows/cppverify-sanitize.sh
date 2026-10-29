#!/bin/bash
# Runs every Verify test program that lit runs through a sanitized cpp-verify
# and fails when a sanitizer reports anything. Verdicts are not compared: the
# sanitizers slow the verifier, and lit checks verdicts.
#
# usage: cppverify-sanitize.sh BUILD_DIR address|thread [PARALLEL]
#
# address: a build with -DCPPVERIFY_SANITIZER="address;undefined". LLVM's
# allocators poison memory in the instrumented code's copies of their inline
# functions, which the uninstrumented libraries then use, so poisoning by
# hand is off. Each program runs with two jobs, so the pool runs under the
# sanitizers too.
#
# thread: a build with -DLLVM_USE_SANITIZER=Thread, which instruments LLVM,
# Clang, the verifier, and the vendored Z3. Each program runs with four jobs
# and a proof cache of its own, and a program whose tests race Z3 against
# cvc5 runs on the race backend, so the pool, the cache, and the races run
# concurrently. cppverify-tsan.supp lists the reports inside Z3 itself and
# LLVM's crash handler.
set -u
BUILD=$1
MODE=$2
PARALLEL=${3:-$(nproc)}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
TESTS=$ROOT/clang/test/Verify
OUT=$(mktemp -d)
export OUT TESTS MODE
export CPPVERIFY=$BUILD/bin/cpp-verify
export ASAN_OPTIONS=detect_leaks=0:allow_user_poisoning=0
export UBSAN_OPTIONS=print_stacktrace=1
export TSAN_OPTIONS="suppressions=$HERE/cppverify-tsan.supp second_deadlock_stack=1"

# A runtime that hangs reports nothing, so a program without a result
# within the time limit is reported too.
case $MODE in
  address) REPORT='ERROR: AddressSanitizer|runtime error:' ;;
  thread) REPORT='WARNING: ThreadSanitizer|ERROR: ThreadSanitizer|ThreadSanitizer shadow stack' ;;
  *) echo "unknown mode $MODE" >&2; exit 2 ;;
esac
REPORT="$REPORT|cppverify-sanitize: no result"

run() {
  local file=$1 name extra=()
  name=$(echo "${file#$TESTS/}" | tr / _)
  grep -q '^// UNSUPPORTED: true' "$file" && return 0
  if [ "$MODE" = thread ]; then
    extra=(--jobs=4 "--proof-cache=$OUT/cache-$name")
    if grep -q -E -- '--backend[= ]race' "$file" && command -v cvc5 > /dev/null; then
      extra+=(--backend=race)
    fi
  else
    extra=(--jobs=2)
  fi
  timeout -k 60 900 "$CPPVERIFY" --timeout=5000 "${extra[@]}" "$file" -- \
    "-I$TESTS/suite/Inputs" > "$OUT/$name.txt" 2>&1
  local status=$?
  if [ $status -eq 124 ] || [ $status -eq 137 ]; then
    echo "cppverify-sanitize: no result within 900 s (status $status)" >> "$OUT/$name.txt"
  fi
  return 0
}
export -f run

find "$TESTS" -name '*.cpp' -not -path '*/Inputs/*' -print0 |
  xargs -0 -P "$PARALLEL" -I{} bash -c 'run "$1"' _ {}

reports=$(grep -l -E "$REPORT" "$OUT"/*.txt)
programs=$(find "$TESTS" -name '*.cpp' -not -path '*/Inputs/*' -exec grep -L '^// UNSUPPORTED: true' {} + | wc -l)
if [ -z "$reports" ]; then
  echo "$MODE: no reports in $programs programs"
  exit 0
fi
for report in $reports; do
  echo "=== $(basename "$report" .txt)"
  grep -m1 -A40 -E "$REPORT" "$report"
done
echo "$MODE: reports in $(echo "$reports" | wc -l) of $programs programs"
mkdir -p sanitizer-reports && cp $reports sanitizer-reports/
exit 1
