#!/usr/bin/env python3
"""Compare the results of several runs of a lit suite (lit -o FILE.json).

Prints each test whose result is not PASS, UNSUPPORTED, or XFAIL in some run,
with its result in every run, and exits non-zero if there is one. A test whose
results differ between runs is flaky: its verdict depends on more than the
program, such as the load or the solver's search order.
"""

import json
import sys

GOOD = {"PASS", "UNSUPPORTED", "XFAIL"}

runs = []
for path in sys.argv[1:]:
    with open(path) as f:
        runs.append({t["name"]: t["code"] for t in json.load(f)["tests"]})

names = sorted(set().union(*runs))
flaky, failing = [], []
for name in names:
    codes = [run.get(name, "MISSING") for run in runs]
    if all(code in GOOD for code in codes):
        continue
    (failing if len(set(codes)) == 1 else flaky).append((name, codes))

print(f"{len(names)} tests, {len(runs)} runs: {len(flaky)} flaky, "
      f"{len(failing)} failing in every run")
for title, tests in (("Flaky", flaky), ("Failing in every run", failing)):
    if tests:
        print(f"\n{title}:")
        for name, codes in tests:
            print(f"  {name}: {' '.join(codes)}")
sys.exit(1 if flaky or failing else 0)
