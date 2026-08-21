LLVM ULEB128
============

CppVerify's flagship case study verifies the unpadded 64-bit ULEB128 buffer
codec derived from LLVM 22.1.3's ``llvm/Support/LEB128.h``.

ULEB128 stores an unsigned integer in seven-bit groups. The high bit says
whether another byte follows. It is a small algorithm with systems-level proof
content: machine shifts and masks, narrowing to bytes, a variable-length loop,
pointer writes, framing, decoding, and malformed inputs.

What is proved
--------------

For every ``uint64_t`` input and an abstract valid ten-byte output extent, Z3
proves:

- termination;
- exact encoded length from 1 through 10;
- every emitted byte, including continuation and terminator bits;
- in-bounds writes and preservation of unused capacity;
- an exact ten-cell frame;
- canonical decoding and consumed length;
- ``decode(encode(value)) == value``.

Two additional deductive checks cover a one-byte truncated sequence and a
tenth-byte overflow sequence. A one-step BMC check rejects an encoder mutation
that omits the continuation bit.

Extraction boundary
-------------------

The artifact is faithful but not verbatim:

.. list-table::
   :header-rows: 1
   :widths: 30 70

   * - Normalization
     - Reason
   * - ``PadTo`` is fixed at zero.
     - The theorem covers canonical unpadded ULEB128.
   * - ``*p++`` becomes ``buffer[count - 1]``.
     - The current abstract extent is attached to the allocation base and does
       not survive loop-carried cursor reassignment.
   * - The decoder receives an ``expected`` proof witness.
     - It appears only in contracts and invariants, not executable accumulator
       arithmetic.
   * - Error strings become scalar status.
     - Nested ``const char **`` mutation remains fail-closed.
   * - Ten finite byte invariants replace one quantified heap invariant.
     - A ``uint64_t`` ULEB128 encoding has a hard ten-byte maximum; the
       quantified form timed out.

A native harness compiles the extraction with proof constructs erased and
compares it with LLVM on lengths, bytes, sentinels, decoding, consumed counts,
and error results.

Measured evidence
-----------------

.. list-table::
   :header-rows: 1
   :widths: 34 26 40

   * - Evidence
     - Result
     - Scope
   * - Complete deductive proof
     - Z3 verified
     - 370 canonical obligations: 318 across encoder, decoder, and round
       trip, plus 52 discharging the machine-byte ``proof`` lemmas
   * - Reduced length/bounds proof
     - Z3+cvc5 portfolio verified
     - Both solvers agree on the smaller surface
   * - Complete strict portfolio
     - Unresolved
     - cvc5 returns ``unknown`` on encoder and decoder; Z3 verifies them
   * - Native canonical comparison
     - 2,048,618 executions pass
     - 42 boundary, 1,048,576 exhaustive-small, and 1,000,000 deterministic
       random executions
   * - Native malformed comparison
     - 2 examples pass
     - Truncated and 64-bit-too-large branches

The full artifact is therefore described as **Z3-verified**, not
portfolio-certified.

Known LLVM shift defect
-----------------------

The pinned LLVM decoder validates pure zero extension in an overlong input but
still evaluates ``Slice << Shift``. For ten ``0x80`` bytes followed by
``0x00``, the next accumulator step has ``Shift == 70``. A 64-bit shift by 70
is undefined in C++.

The deductive regression isolates the accumulator in an indexed, fixed-input
model: CppVerify accepts the guarded form and rejects the unguarded form with a
source-level ``shift = 70`` counterexample. A separate GCC UBSan executable
calls the pinned LLVM decoder and independently reports the same shift. LLVM
fixed this known defect in
`commit 8014a1d2 <https://github.com/llvm/llvm-project/commit/8014a1d208f0f9e58cfeaf022517cf3d69257bff>`_,
`PR #205907 <https://github.com/llvm/llvm-project/pull/205907>`_. The case
study independently reproduces the defect; it does not claim to have
discovered it.

Reproduce
---------

From the outer repository root, with the existing build plus cvc5 and a
UBSan-capable ``g++``:

.. code-block:: bash

   ./scripts/run-uleb128-case-study.sh

The command writes validated, schema-versioned evidence to
``build/uleb128-case-study/summary.json`` and retains the individual JSON Lines
diagnostics, obligation hashes, timings, native result, and sanitizer witness.
It rebuilds the verifier, verifies the pinned LLVM header, and records SHA-256
digests for every proof/harness source and principal tool binary before
execution. Proof and native commands consume a read-only source snapshot; the
workflow rejects input, snapshot, or tool changes and validates compiler
dependency files to ensure the native builds resolved the snapshotted pinned
header.

Read the full
`technical report <https://github.com/SwayamInSync/cpp-verify-roadmap/blob/main/extras/docs/TECHNICAL_REPORT.md>`_
for the architecture, proof design, trust boundary, measurements, limitations,
and references.
