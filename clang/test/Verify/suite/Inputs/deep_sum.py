# usage: deep_sum.py N OUT: a function returning x + 1 + ... + 1, N ones.
import sys

n = int(sys.argv[1])
with open(sys.argv[2], "w") as out:
    out.write("int deep_sum(int x)\n"
              "  cppverify::pre(0 <= x && x <= 100)\n"
              "  cppverify::post(cppverify::result == x + %d)\n"
              "{\n  return %s;\n}\n" % (n, " + ".join(["x"] + ["1"] * n)))
