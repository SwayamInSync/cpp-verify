#!/usr/bin/env python3
"""Writes each record of the given obligation archives to a file of its own
in OUT, named by its hash, when it is at most MAX bytes: the fuzzer's seeds.

usage: cppverify-fuzz-seeds.py OUT MAX ARCHIVE...
"""

import hashlib
import os
import sys

MAGIC = b"CPVOBL\r\n"


def records(data):
    starts = []
    at = data.find(MAGIC)
    while at != -1:
        starts.append(at)
        at = data.find(MAGIC, at + 1)
    starts.append(len(data))
    for begin, end in zip(starts, starts[1:]):
        yield data[begin:end]


def main():
    out, limit, archives = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    os.makedirs(out, exist_ok=True)
    written = 0
    for archive in archives:
        with open(archive, "rb") as f:
            data = f.read()
        for record in records(data):
            if len(record) > limit:
                continue
            name = hashlib.sha1(record).hexdigest()
            with open(os.path.join(out, name), "wb") as f:
                f.write(record)
            written += 1
    print(f"{written} records of at most {limit} bytes from {len(archives)} archives")


if __name__ == "__main__":
    main()
