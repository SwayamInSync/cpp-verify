"""Runs a command and fails if it ends sooner than the given seconds.

usage: at_least_seconds.py SECONDS COMMAND...
The command's output and exit status pass through."""
import subprocess
import sys
import time

least = float(sys.argv[1])
start = time.monotonic()
done = subprocess.run(sys.argv[2:])
taken = time.monotonic() - start
if taken < least:
    print(f"at_least_seconds: the command took {taken:.1f} s, less than {least:g} s")
    sys.exit(125)
sys.exit(done.returncode)
