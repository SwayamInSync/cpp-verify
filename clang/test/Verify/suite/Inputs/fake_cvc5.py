#!/usr/bin/env python3
import pathlib
import os
import re
import signal
import sys
import time


def default_value(sort):
    if sort == "Bool":
        return "false"
    if sort == "Int":
        return "0"
    if sort.startswith("(_ BitVec"):
        return "(_ bv0 {})".format(sort.split()[2].rstrip(")"))
    return "((as const (Array Int Int)) 0)"


def print_model(script):
    # An arbitrary model, as --dump-models prints one after sat.
    print("(")
    for name, params, sort in re.findall(
        r"^\(declare-fun (\S+) \(([^)]*)\) (.+)\)$", script, re.M
    ):
        args = " ".join(
            "(_arg_{} {})".format(i + 1, p) for i, p in enumerate(params.split())
        )
        print("(define-fun {} ({}) {} {})".format(name, args, sort, default_value(sort)))
    print(")")


mode = pathlib.Path(sys.argv[0]).suffix.removeprefix(".")
if mode == "sat":
    print("sat")
    print_model(pathlib.Path(sys.argv[-1]).read_text())
elif mode == "unsat":
    print("unsat")
elif mode == "unknown":
    print("unknown")
elif mode == "comment":
    print("; sat")
    print("unsat")
elif mode == "trailing":
    print("unsat")
    print("unexpected")
elif mode == "large":
    print("x" * (64 * 1024 + 1))
elif mode == "stream":
    while True:
        sys.stdout.write("x" * 4096)
        sys.stdout.flush()
        time.sleep(0.01)
elif mode == "stderr":
    print("unsat")
    print("unexpected diagnostic", file=sys.stderr)
elif mode == "exit":
    print("solver failure", file=sys.stderr)
    sys.exit(7)
elif mode == "crash":
    os.kill(os.getpid(), signal.SIGTERM)
elif mode == "hang":
    time.sleep(10)
else:
    print("unsupported fake solver mode", file=sys.stderr)
    sys.exit(8)
