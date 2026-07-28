Commands and flags
==================

Standalone verifier
-------------------

.. code-block:: bash

   cpp-verify file.cpp
   cpp-verify --backend=z3 file.cpp
   cpp-verify --backend=bmc --unroll=3 file.cpp
   cpp-verify --backend=lean --lean-out=goal.lean file.cpp
   cpp-verify --check-ub file.cpp
   cpp-verify --timeout=20000 file.cpp
   cpp-verify --dump-ir=1,2,3,4 file.cpp
   cpp-verify --lower-only --dump-ir=1,2,3,4 file.cpp

``cpp-verify`` is a Clang tooling driver: it always adds ``-std=c++17`` and ``-fverify-contracts``.

Backends
--------

.. list-table::
   :header-rows: 1
   :widths: 22 78

   * - Flag
     - Meaning
   * - ``--backend=z3``
     - Default. Weakest precondition + Z3 (loops via contracts on the WP path).
   * - ``--backend=bmc``
     - Unroll loops up to ``--unroll=N`` (default 10), then Z3.
   * - ``--backend=lean``
     - Write an unchecked Lean 4 scratch-pad to ``--lean-out``. This path does
       not run Z3 and reports ``Exported``, never ``Verified``. Multi-function
       output uses one shared preamble and identity-qualified theorem names.
   * - ``--unroll=N``
     - BMC loop bound only.
   * - ``--check-ub``
     - On the Z3 and BMC backends, additionally recognize ``valid(p, n)``
       preconditions as buffer extents and prove indexed accesses, modular
       sub-slices, and same-array pointer positions are in bounds. Markers must
       be positive top-level conjunction clauses on bare pointers. Core
       expression definedness (overflow, division, shifts, and dereferences)
       is always checked. See :doc:`integers` and :doc:`pointers`.
   * - ``--timeout=N``
     - Per-query Z3 timeout in milliseconds (default 30000; ``0`` disables). A query
       that exceeds it is reported as ``unknown`` instead of hanging.
   * - ``--lower-only``
     - Run Clang conversion, backend-specific preparation, passivization,
       canonical Obligation IR construction, spec-axiom encoding, and Z3
       translation without calling the solver. Supported for Z3 and BMC.

``--lower-only`` is deliberately different from compiler ``-fno-verify``.
``-fno-verify`` stops after Clang syntax and contract semantic checks;
``--lower-only`` exercises the complete verification pipeline through backend
encoding. A successful run prints ``Lowered: function``. That means the formula
was constructed and encoded, **not** that its obligations are true.

Supported compiler
------------------

Contract syntax and ``-fverify-contracts`` exist **only in this repository's
Clang**. Use the shipped ``./build/bin/cpp-verify`` and
``./build/bin/clang++`` for any code that uses contracts — stock GCC or upstream
Clang reject the flag and the contract keywords. (Building cpp-verify itself from
source is independent and works with any standard host compiler.)

Compile with contracts (``clang++``)
------------------------------------

.. code-block:: bash

   clang++ -std=c++17 -fverify-contracts -c file.cpp -o file.o   # compile + verify
   clang++ -std=c++17 -fno-verify -fsyntax-only file.cpp         # light syntax/semantics check

Two independent axes
~~~~~~~~~~~~~~~~~~~~~

Contract behaviour is governed by **two** switches, not one. Understanding the
split is the whole game:

.. list-table::
   :header-rows: 1
   :widths: 30 18 52

   * - Switch (flag)
     - Default
     - What it controls
   * - **Contract language**

       ``-fverify-contracts`` / ``-fno-verify-contracts``
     - off
     - Whether the parser recognises ``pre``/``post``/``ghost``/``spec``/… (and
       therefore whether CodeGen strips them). This is the **master** switch — with
       it off, the file is byte-identical to stock C++ and the verifier never runs.
   * - **Run the prover**

       ``-fno-verify``
     - on (when contracts are on)
     - Whether the SMT verifier runs (in a thread, parallel to code generation).
       The verifier runs by default once contracts are enabled; ``-fno-verify``
       skips it. There is no ``-fverify`` — it would just be the default.

``-fno-verify`` is meaningless without the contract language, so it **implies
-fverify-contracts** (unless you explicitly pass ``-fno-verify-contracts``). That
makes a lone ``-fno-verify`` a fast *light check*: it validates C++ syntax,
contract syntax, **and** contract semantics (the ``old``/``result`` placement and
bool-convertibility rules), but does **not** check your logic. Ideal for
editors, CI pre-flight, and LLM/agent loops.

Quick lookup
~~~~~~~~~~~~

.. list-table::
   :header-rows: 1
   :widths: 34 14 14 38

   * - Flags (with ``clang++``)
     - Contracts
     - Verify
     - Result
   * - *(none)*
     - off
     - —
     - Plain C++; ``pre``/``post`` are ordinary identifiers. Zero overhead.
   * - ``-fverify-contracts``
     - on
     - **yes**
     - **Full**: compile **and** verify in parallel. A failed contract is a compile error.
   * - ``-fno-verify``
     - on *(implied)*
     - no
     - **Light**: parse + Sema + compile, skip the solver. Catches syntax/semantic
       errors, ignores logic.
   * - ``-fno-verify -fsyntax-only``
     - on *(implied)*
     - no
     - Fastest light check — no code generation either.
   * - ``-fno-verify-contracts``
     - off
     - —
     - Off entirely. Combined with ``-fno-verify``, the explicit *off* wins.

The standalone ``cpp-verify`` tool normally runs the **full** path (it adds
``-fverify-contracts`` for you and does no code generation);
``--lower-only`` is its explicit solver-free verification-IR mode.

IR dump layers
--------------

``--dump-ir`` accepts a comma-separated mask (or ``all``):

.. list-table::
   :header-rows: 1
   :widths: 12 88

   * - Layer
     - Content
   * - ``1`` / ``layer-1``
     - VCR IR — typed control flow, contracts preserved
   * - ``2`` / ``layer-2``
     - Passive IR — SSA, ``assume`` / ``assert``, heap versions
   * - ``3`` / ``layer-3``
     - Verification condition (logical formula)
   * - ``4`` / ``layer-4``
     - Z3 translation of the VC

Examples:

.. code-block:: bash

   cpp-verify --dump-ir=1 file.cpp
   cpp-verify --dump-ir=layer-3,layer-4 file.cpp
   cpp-verify --dump-ir file.cpp          # all layers

Layers are separated by a line of ``======`` in the output.

For lowering regressions, combine the dump with ``--lower-only``. This makes
VCR/passive/VC/Z3 ``FileCheck`` expectations independent of solver runtime:

.. code-block:: bash

   cpp-verify --lower-only --dump-ir=1 program.cpp
   cpp-verify --lower-only --dump-ir=2 program.cpp
   cpp-verify --lower-only --dump-ir=3 program.cpp
   cpp-verify --lower-only --dump-ir=4 program.cpp

Layer 4 still performs the complete Z3 encoding, including reachable spec
axioms, and fails closed on an encoding error. It only omits
``Solver.check()``.

Layer 3 is the canonical backend-neutral ``ObligationModule``. It prints the
same in-memory module consumed by Layer 4 and ordinary verification: explicit
logic sorts and required features, one complete counterexample query,
deterministic obligation IDs/kinds, source encodings, and equivalent ordered
queries. A malformed, untyped, or unsupported term fails lowering rather than
becoming a proof-shaped default.

Testing and coverage
--------------------

Regression tests live under ``clang/test/Verify/``. From the **repository root**:

.. list-table::
   :header-rows: 1
   :widths: 32 68

   * - Script
     - Purpose
   * - ``./scripts/run-verify-tests.sh``
     - Lower every solver-positive executable example first, then run its
       ordinary pass / expected-fail solver check.
   * - ``./scripts/coverage-sweep.sh``
     - Fast profile merge after a normal build (from repo root).
   * - ``./scripts/coverage-verify.sh``
     - Full instrumented rebuild + sweep (slow; use when changing coverage setup).

Set ``CPPVERIFY_ENABLE_COVERAGE=ON`` on ``clangVerify`` only — not the whole LLVM tree.

New language features should have both semantic and structural oracles:

- real C++ positive and negative programs;
- exact Layer 1 VCR and Layer 2 passive-SSA expectations;
- Layer 3 Obligation IR checks for sorts, IDs, origins, and the decisive query,
  plus Layer 4 Z3 checks for its translation;
- ordinary solver checks for valid programs and deliberate false proofs.

Solver ``unknown`` never validates a feature. Structural lowering can still be
tested with ``--lower-only``, while proof acceptance remains blocked until a
backend returns a proof result.

Engine headers: :doc:`../api/index`.