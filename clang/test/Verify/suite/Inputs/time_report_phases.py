"""Reads the JSON Lines of a run with --time-report and prints, for each
function, which phases took any time, and whether its times add up: the
total is lowering, solving, and confirmation; induction is part of solving;
and with one job, so is certification. Then whether the functions come
busiest first."""
import json
import sys

totals = []
for line in sys.stdin:
    record = json.loads(line)
    if record.get("schema") != "cppverify.time/1":
        continue
    seconds = record["seconds"]
    if "function" not in record:
        print("run " + " ".join(sorted(seconds)))
        continue
    totals.append(seconds["total"])
    parts = seconds["lowering"] + seconds["solving"] + seconds["confirmation"]
    adds_up = (abs(seconds["total"] - parts) < 1e-6 and
               seconds["lowering"] >= 0 and
               seconds["induction"] <= seconds["solving"] and
               seconds["certification"] <= seconds["solving"])
    print("%s solving=%d induction=%d certification=%d confirmation=%d %s" % (
        record["function"], seconds["solving"] > 0, seconds["induction"] > 0,
        seconds["certification"] > 0, seconds["confirmation"] > 0,
        "adds up" if adds_up else "does not add up: %r" % seconds))
print("busiest first" if totals == sorted(totals, reverse=True)
      else "not busiest first: %r" % totals)
