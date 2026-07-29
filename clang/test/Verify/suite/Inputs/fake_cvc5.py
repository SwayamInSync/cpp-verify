#!/usr/bin/env python3
import pathlib
import os
import signal
import sys
import time

mode = pathlib.Path(sys.argv[0]).suffix.removeprefix(".")
if mode == "sat":
    print("sat")
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
