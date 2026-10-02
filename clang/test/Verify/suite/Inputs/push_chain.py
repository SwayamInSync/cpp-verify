import sys

# A ghost sequence built by N pushes, and a false claim about one element.
n = int(sys.argv[1])
print("#include <cppverify.h>")
print("using cppverify::seq;")
print("proof void chain_bad() {")
print("  ghost seq s = cppverify::seq_empty();")
for i in range(n):
    print(f"  s = s.push({i});")
print(f"  contract_assert(s[{n // 2}] == {n // 2 + 1});")
print("}")
