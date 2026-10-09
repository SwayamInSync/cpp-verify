LLVM ULEB128
============

CppVerify's flagship case study verifies the unpadded 64-bit ULEB128 buffer
codec derived from LLVM 22.1.3's ``llvm/Support/LEB128.h``. This release is
based on LLVM 23.1.3, whose encoder is unchanged and whose decoder adds the
guard described under "Known LLVM shift defect" below.

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
     - Pointer increment (``p++``, ``p += 1``) is not in the verified subset,
       so the extraction indexes from the base. A loop-carried ``p = p + 1``
       with an invariant relating ``p`` to the base would also verify.
   * - The decoder receives an ``expected`` proof witness.
     - It appears only in contracts and invariants, not executable accumulator
       arithmetic.
   * - Error strings become scalar status.
     - Nested ``const char **`` mutation remains fail-closed.
   * - Ten finite byte invariants replace one quantified heap invariant.
     - A ``uint64_t`` ULEB128 encoding has a hard ten-byte maximum; the
       quantified form timed out.

A native harness compiles the extraction with proof constructs erased and
compares it with this tree's LLVM 23.1.3 header on lengths, bytes, sentinels,
decoding, consumed counts, and error results.

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
     - 328 canonical obligations: 285 across encoder (186), decoder (33), and
       round trip (66), plus 43 discharging the eleven machine-byte
       ``cppverify::proof`` lemmas (four for each of ten, three for the last)
   * - Reduced length/bounds proof
     - Z3+cvc5 portfolio verified
     - Both solvers agree on the smaller surface
   * - Complete strict portfolio
     - Unresolved
     - cvc5 returns ``unknown`` or times out (``--timeout=30000``); Z3 alone
       verifies every function (row above)
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

LLVM 22.1.3's decoder validates pure zero extension in an overlong input but
still evaluates ``Slice << Shift``. For ten ``0x80`` bytes followed by
``0x00``, the next accumulator step has ``Shift == 70``. A 64-bit shift by 70
is undefined in C++. LLVM 23.1.3's decoder, the one in this tree, evaluates
the step only under ``if (LLVM_LIKELY(Shift < 64))``, so that shift no longer
occurs.

The deductive regression ``llvm_uleb128_shift_ub.cpp`` isolates the
accumulator in an indexed, fixed-input model: CppVerify accepts the guarded
form and rejects the 22.1.3 accumulator, kept as ``decode_overlong_upstream``,
with a source-level ``shift = 70`` counterexample. Built with GCC's
``-fsanitize=undefined``,
``clang/test/Verify/suite/Inputs/llvm_uleb128_ubsan.cpp`` reports the same
shift when it calls LLVM 22.1.3's decoder, and nothing with this tree's
header. LLVM has fixed this known defect; the case study independently
reproduces it and does not claim to have discovered it.

Reproduce
---------

From the repository root, after building the lit tools with
``ninja -C build FileCheck not count split-file llvm-config``:

.. code-block:: bash

   ./build/bin/llvm-lit -sv \
     clang/test/Verify/suite/llvm_uleb128.cpp \
     clang/test/Verify/suite/llvm_uleb128_errors.cpp \
     clang/test/Verify/suite/llvm_uleb128_mutation.cpp \
     clang/test/Verify/suite/llvm_uleb128_portfolio.cpp \
     clang/test/Verify/suite/llvm_uleb128_shift_ub.cpp

``llvm_uleb128_portfolio.cpp`` requires cvc5. The native comparison builds the
extraction with its proof constructs erased:

.. code-block:: bash

   ./build/bin/clang++ -std=c++17 -O2 -fverify-contracts -fno-verify \
     -Illvm/include -Ibuild/include \
     clang/test/Verify/suite/Inputs/llvm_uleb128_native.cpp -o uleb128-native
   ./uleb128-native
