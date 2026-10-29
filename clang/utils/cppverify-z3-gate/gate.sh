#!/bin/bash
# The gate a Z3 release passes before cpp-verify adopts it.
#
# usage: gate.sh BASE CANDIDATE [OUT]
#
# BASE and CANDIDATE are cpp-verify build directories, each with
# bin/cpp-verify and the Z3 it is built with in cppverify-z3/install/bin/z3.
# Run from the repository root. Results land in OUT (default: a fresh
# temporary directory).
#
# Stage 1 solves the sequence benchmark (seqbench.py) with both Z3 binaries,
# in cpp-verify's own encoding (NT) and in the plain sequence theory (N),
# which a run with more than one job races beside it. A claim counts as the
# verifier would decide it: by NT with one job, by NT or N with more. The
# candidate fails when it loses a proof of a valid claim or a model of a false
# one that the base has in either.
#
# Stage 2 verifies every Verify test program with both builds at one job
# (differential.py) and fails when the candidate loses a proof or a certified
# failure, or when a function is Verified in one and Failed in the other.
set -u
BASE=$1
CAND=$2
OUT=${OUT:-${3:-$(mktemp -d)}}
JOBS=${JOBS:-$(nproc)}
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT/queries"
status=0

echo "== stage 1: the sequence benchmark"
python3 "$HERE/seqbench.py" "$OUT/queries" > /dev/null
solve() {  # solve Z3 FILE: prints "name,verdict"
  local out
  out=$(timeout 30 "$1" -T:20 "$2" 2>&1 | head -1 | tr -d '\r')
  case "$out" in sat|unsat|unknown) ;; *) out=timeout ;; esac
  echo "$(basename "$2" .smt2),$out"
}
export -f solve
for role in base cand; do
  z3=$BASE/cppverify-z3/install/bin/z3
  [ $role = cand ] && z3=$CAND/cppverify-z3/install/bin/z3
  "$z3" --version
  ls "$OUT"/queries/*.N.z3.smt2 "$OUT"/queries/*.NT.z3.smt2 |
    xargs -P "$JOBS" -I{} bash -c "solve '$z3' {}" | sort > "$OUT/stage1_$role.csv"
done
python3 - "$OUT" <<'EOF' || status=1
import csv, sys
out = sys.argv[1]
def load(role):
    return {row[0]: row[1] for row in csv.reader(open(f"{out}/stage1_{role}.csv"))}
def decided(results, claim, encodings):
    want = 'unsat' if '.ok' in claim else 'sat'
    return any(results.get(f"{claim}.{e}.z3") == want for e in encodings)
base, cand = load('base'), load('cand')
claims = sorted({name.rsplit('.', 2)[0] for name in base})
lost = []
for jobs, encodings in (('one job', ('NT',)), ('more jobs', ('NT', 'N'))):
    for role, results in (('base', base), ('cand', cand)):
        proved = sum(decided(results, c, encodings) for c in claims if '.ok' in c)
        models = sum(decided(results, c, encodings) for c in claims if '.bad' in c)
        print(f"{jobs:9} {role}: {proved} proofs, {models} models")
    for c in claims:
        if decided(base, c, encodings) and not decided(cand, c, encodings):
            lost.append((jobs, c))
for jobs, c in lost:
    print(f"LOST {c} ({jobs})")
for c in claims:
    if decided(cand, c, ('NT', 'N')) and not decided(base, c, ('NT', 'N')):
        print(f"GAINED {c}")
sys.exit(1 if lost else 0)
EOF

echo "== stage 2: every Verify test program"
python3 "$HERE/differential.py" "$BASE/bin/cpp-verify" "$CAND/bin/cpp-verify" \
  "$OUT/stage2.jsonl" --parallel "$JOBS" | tee "$OUT/stage2.txt"
[ "${PIPESTATUS[0]}" = 0 ] || status=1

echo "results in $OUT"
if [ $status = 0 ]; then echo "gate: pass"; else echo "gate: FAIL"; fi
exit $status
