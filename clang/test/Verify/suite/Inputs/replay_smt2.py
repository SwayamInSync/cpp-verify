"""Replays the scripts --dump-smt2 wrote for one solver and compares each
answer with the one cpp-verify recorded.

usage: replay_smt2.py SOLVER EXECUTABLE DIRECTORY
       replay_smt2.py --list DIRECTORY

Prints one line per script whose replay differs (an error, or another
answer to a script cpp-verify answered sat or unsat), then a summary line.
"""
import os
import subprocess
import sys

if sys.argv[1] == "--list":
    # The files, relative to the directory, in order.
    for root, _, names in sorted(os.walk(sys.argv[2])):
        for name in sorted(names):
            print(os.path.relpath(os.path.join(root, name), sys.argv[2])
                  .replace(os.sep, "/"))
    sys.exit(0)

solver, executable, directory = sys.argv[1:4]
scripts = sorted(
    os.path.join(root, name)
    for root, _, names in os.walk(directory)
    for name in names
    if name.endswith(".smt2") and ".%s-" % solver in name
)
compared = differing = 0
for path in scripts:
    with open(path) as f:
        recorded = [l for l in f if l.startswith("; cpp-verify: ")]
    answer = recorded[-1][len("; cpp-verify: ") :].strip() if recorded else ""
    # A script cpp-verify did not settle is only read, for errors, not
    # solved again to its timeout.
    try:
        output = subprocess.run(
            [executable, path], stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, universal_newlines=True,
            timeout=None if answer in ("sat", "unsat") else 5,
        ).stdout
    except subprocess.TimeoutExpired as stopped:
        output = stopped.output or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
    lines = output.splitlines()
    first = lines[0].strip() if lines else ""
    relative = os.path.relpath(path, directory).replace(os.sep, "/")
    if any(l.startswith("(error") for l in lines):
        differing += 1
        error = next(l for l in lines if l.startswith("(error"))
        print("%s: %s" % (relative, error))
    elif answer in ("sat", "unsat"):
        compared += 1
        if first != answer:
            differing += 1
            print("%s: recorded %s, replayed %s" % (relative, answer, first))
print(
    "%s: %d scripts, %d with a recorded sat or unsat, %d differing"
    % (solver, len(scripts), compared, differing)
)
