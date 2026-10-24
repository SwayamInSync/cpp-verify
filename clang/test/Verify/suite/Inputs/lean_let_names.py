"""Prints how many theorems of a Lean export bind one name twice in the lets
their statement starts with: a subterm shared by several places of a
statement is named once."""
import re
import sys

twice = 0
for theorem in re.split(r"(?m)^(?=theorem )", open(sys.argv[1]).read()):
    lines = theorem.splitlines()
    start = next((i for i, l in enumerate(lines) if "(let __cppverify_term_" in l), None)
    if start is None:
        continue
    names = re.findall(r"\(let (__cppverify_term_\d+) :", lines[start])[:1]
    for line in lines[start + 1:]:
        bound = re.match(r"  let (__cppverify_term_\d+) :", line)
        if not bound:
            break
        names.append(bound.group(1))
    twice += len(names) != len(set(names))
print(f"statements that bind a let name twice: {twice}")
