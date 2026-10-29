#!/usr/bin/env python3
"""Verdict-and-time differential between two cpp-verify binaries.

usage: differential.py BASE NEW OUT.jsonl [--parallel N] [-- extra cpp-verify args]

Every .cpp file under clang/test/Verify (run from the repository root) is
verified by both binaries with --diagnostics-format=json and CPPVERIFY_JOBS=1.
A function's verdict is its status, reason, and qualifiers (vacuous,
partial, trusts). The differential prints each function whose verdict
changed, as one of:

  LOST     a proof or certified failure of BASE that NEW does not give
  FLIPPED  Verified in one and Failed in the other: a solver or the verifier
           is wrong in one of them
  GAINED   a proof or certified failure NEW gives and BASE does not
  CHANGED  any other change

and each file whose time changed by more than 2x and 5 s. It exits with 1
when a verdict is LOST or FLIPPED."""
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time

args = sys.argv[1:]
extra = []
if "--" in args:
    i = args.index("--")
    extra = args[i + 1:]
    args = args[:i]
parallel = os.cpu_count() or 4
if "--parallel" in args:
    i = args.index("--parallel")
    parallel = int(args[i + 1])
    del args[i:i + 2]
base, new, out_path = args
files = subprocess.run(["git", "ls-files", "clang/test/Verify/*.cpp",
                        "clang/test/Verify/**/*.cpp"],
                       capture_output=True, text=True, check=True).stdout.split()
files = [f for f in files if "/Inputs/" not in f]
INPUTS = os.path.abspath("clang/test/Verify/suite/Inputs")


def run(binary, path):
    env = dict(os.environ, CPPVERIFY_JOBS="1")
    start = time.monotonic()
    try:
        p = subprocess.run([binary, "--diagnostics-format=json", *extra, path,
                            "--", "-std=c++17", "-I" + INPUTS],
                           capture_output=True, text=True, timeout=1800, env=env)
        out = p.stdout
    except subprocess.TimeoutExpired:
        out = ""
    seconds = time.monotonic() - start
    verdicts = {}
    for line in out.splitlines():
        try:
            r = json.loads(line)
        except ValueError:
            continue
        name = r.get("function")
        status = r.get("status")
        if not name or status not in ("verified", "failed", "unresolved",
                                      "bounded-safe", "trusted"):
            continue
        verdict = {"status": status, "reason": r.get("reason"),
                   "vacuous": bool(r.get("vacuous")),
                   "partial": bool(r.get("partial")),
                   "trusts": sorted(r.get("trusts") or [])}
        verdicts.setdefault(name, []).append(verdict)
    return {"verdicts": verdicts, "seconds": round(seconds, 2)}


def decisive(verdict):
    return verdict["status"] in ("verified", "failed")


def compare(a, b):
    """The changes between two runs of one file."""
    changes = []
    for name in sorted(set(a) | set(b)):
        va, vb = a.get(name, []), b.get(name, [])
        if va == vb:
            continue
        sa = {v["status"] for v in va}
        sb = {v["status"] for v in vb}
        if ("verified" in sa and "failed" in sb) or ("failed" in sa and "verified" in sb):
            kind = "FLIPPED"
        elif any(decisive(v) and v not in vb for v in va):
            kind = "LOST"
        elif any(decisive(v) and v not in va for v in vb):
            kind = "GAINED"
        else:
            kind = "CHANGED"
        changes.append((kind, name, va, vb))
    return changes


def job(path):
    return path, run(base, path), run(new, path)


counts = {"LOST": 0, "FLIPPED": 0, "GAINED": 0, "CHANGED": 0}
slow = 0
with open(out_path, "w") as out, \
        concurrent.futures.ThreadPoolExecutor(parallel) as pool:
    for path, a, b in pool.map(job, files):
        out.write(json.dumps({"file": path, "base": a, "new": b}) + "\n")
        for kind, name, va, vb in compare(a["verdicts"], b["verdicts"]):
            counts[kind] += 1
            print("%s %s %s" % (kind, path, name))
            print("  base: %s" % json.dumps(va))
            print("  new:  %s" % json.dumps(vb))
        ta, tb = a["seconds"], b["seconds"]
        if abs(tb - ta) > 5 and (tb > 2 * ta or ta > 2 * tb):
            slow += 1
            print("TIME %s base %.1f s new %.1f s" % (path, ta, tb))
total_a = total_b = 0.0
for line in open(out_path):
    record = json.loads(line)
    total_a += record["base"]["seconds"]
    total_b += record["new"]["seconds"]
print("%d files: %d lost, %d flipped, %d gained, %d changed, %d with a time "
      "change; total %.0f s -> %.0f s"
      % (len(files), counts["LOST"], counts["FLIPPED"], counts["GAINED"],
         counts["CHANGED"], slow, total_a, total_b))
sys.exit(1 if counts["LOST"] or counts["FLIPPED"] else 0)
