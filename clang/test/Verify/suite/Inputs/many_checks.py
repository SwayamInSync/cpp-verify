# usage: many_checks.py N OUT: a function of N increments, each followed by a
# check. Each check repeats every assumption before it, so its obligations
# grow with N squared.
import sys

n = int(sys.argv[1])
steps = "".join("  y = y + 1;\n  cppverify::check(y == x + %d);\n" % (i + 1)
                for i in range(n))
with open(sys.argv[2], "w") as out:
    out.write("int many_checks(int x)\n"
              "  cppverify::pre(0 <= x && x <= 100)\n"
              "  cppverify::post(cppverify::result == x + %d)\n"
              "{\n  int y = x;\n%s  return y;\n}\n" % (n, steps))
