"""Interrupts a command as Ctrl-C does.

usage: interrupt_after.py SECONDS LIMIT COMMAND...
Runs the command in a process group of its own, sends SIGINT to the command
alone after SECONDS (so that the processes it started are its to stop), and
prints its output and then its exit status. Fails if the command has not
ended LIMIT seconds after the signal, or leaves a process of its group
running."""
import os
import signal
import subprocess
import sys

delay, limit = float(sys.argv[1]), float(sys.argv[2])
process = subprocess.Popen(sys.argv[3:], stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, start_new_session=True)
try:
    output, _ = process.communicate(timeout=delay)
    sys.stdout.write(output.decode(errors="replace"))
    print("interrupt_after: the command ended before the interrupt")
    sys.exit(125)
except subprocess.TimeoutExpired:
    pass
process.send_signal(signal.SIGINT)
try:
    output, _ = process.communicate(timeout=limit)
except subprocess.TimeoutExpired:
    os.killpg(process.pid, signal.SIGKILL)
    output, _ = process.communicate()
    sys.stdout.write(output.decode(errors="replace"))
    print(f"interrupt_after: the command ran on for {limit:g} s after the interrupt")
    sys.exit(125)
sys.stdout.write(output.decode(errors="replace"))
print(f"exit: {process.returncode}")
try:
    os.killpg(process.pid, 0)
except ProcessLookupError:
    sys.exit(0)
os.killpg(process.pid, signal.SIGKILL)
print("interrupt_after: the command left processes running")
sys.exit(125)
