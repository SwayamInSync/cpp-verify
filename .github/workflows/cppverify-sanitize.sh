#!/bin/bash
# Runs every Verify test program through a cpp-verify built with
# -DCPPVERIFY_SANITIZER and fails when a sanitizer reports anything. Verdicts
# are not compared: the sanitizers slow the verifier, and lit checks verdicts.
#
# usage: cppverify-sanitize.sh BUILD_DIR address|thread [PARALLEL]
#
# address (ASan with UBSan): LLVM's allocators poison memory in the
# instrumented code's copies of their inline functions, which the
# uninstrumented libraries then use, so poisoning by hand is off; threads get
# 1 GiB stacks, since instrumented frames are many times larger and the
# counterexample checker recurses deeply.
#
# thread (TSan): each program runs with four jobs, a proof cache, and, for
# the race tests, the race backend, so the pool, the cache, and the races run
# concurrently; cppverify-tsan.supp lists the reports of code that is not
# instrumented.
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
ulimit -s 1048576

run() {
  local file=$1 name extra=()
  name=$(echo "${file#$TESTS/}" | tr / _)
  if [ "$MODE" = thread ]; then
    extra=(--jobs=4 "--proof-cache=$OUT/cache-$name")
    case $name in
      *race*) command -v cvc5 > /dev/null && extra+=(--backend=race) ;;
    esac
  else
    extra=(--jobs=2)
  fi
  timeout -k 60 900 "$CPPVERIFY" --timeout=5000 "${extra[@]}" "$file" -- \
    "-I$TESTS/suite/Inputs" > "$OUT/$name.txt" 2>&1
  return 0
}
export -f run

find "$TESTS" -name '*.cpp' -not -path '*/Inputs/*' -print0 |
  xargs -0 -P "$PARALLEL" -I{} bash -c 'run "$1"' _ {}

reports=$(grep -l -E 'ERROR: AddressSanitizer|runtime error:|WARNING: ThreadSanitizer|ERROR: ThreadSanitizer' "$OUT"/*.txt)
programs=$(find "$TESTS" -name '*.cpp' -not -path '*/Inputs/*' | wc -l)
if [ -z "$reports" ]; then
  echo "$MODE: no reports in $programs programs"
  exit 0
fi
for report in $reports; do
  echo "=== $(basename "$report" .txt)"
  grep -m1 -A40 -E 'ERROR: AddressSanitizer|runtime error:|WARNING: ThreadSanitizer|ERROR: ThreadSanitizer' "$report"
done
echo "$MODE: reports in $(echo "$reports" | wc -l) of $programs programs"
mkdir -p sanitizer-reports && cp $reports sanitizer-reports/
exit 1
