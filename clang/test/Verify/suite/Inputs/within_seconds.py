"""Runs a command and fails if it takes longer than the given seconds.

usage: within_seconds.py SECONDS COMMAND...
The command's output and exit status pass through."""
import subprocess
import sys

limit = float(sys.argv[1])
try:
    done = subprocess.run(sys.argv[2:], timeout=limit)
except subprocess.TimeoutExpired:
    print(f"within_seconds: the command took longer than {limit:g} s")
    sys.exit(125)
sys.exit(done.returncode)
