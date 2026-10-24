#!/usr/bin/env python3
"""Runs a command, then prints whether the largest process it ran stayed
below a resident memory bound, in MB, and exits with the command's status.

usage: peak_memory.py MB COMMAND...

Linux reports ru_maxrss in kilobytes, for every descendant waited for."""
import resource
import subprocess
import sys

limit = int(sys.argv[1])
done = subprocess.run(sys.argv[2:])
peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
if peak < limit:
    print("peak memory below {} MB".format(limit))
else:
    print("peak memory {} MB, not below {} MB".format(peak, limit))
sys.exit(done.returncode)
