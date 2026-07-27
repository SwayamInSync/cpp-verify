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
     - Write Lean 4 scratch-pad to ``--lean-out`` (required for useful output).
   * - ``--unroll=N``
     - BMC loop bound only.
   * - ``--check-ub``
     - On the Z3 backend, additionally recognize ``valid(p, n)`` preconditions
       as buffer extents and prove every indexed access is in bounds. Markers
       must be positive top-level conjunction clauses on bare pointers. Core
       expression definedness (overflow, division, shifts, and dereferences)
       is always checked. See :doc:`integers` and :doc:`pointers`.
   * - ``--timeout=N``
     - Per-query Z3 timeout in milliseconds (default 30000; ``0`` disables). A query
       that exceeds it is reported as ``unknown`` instead of hanging.

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

The standalone ``cpp-verify`` tool always runs the **full** path (it adds
``-fverify-contracts`` for you and does no code generation).

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

Testing and coverage
--------------------

Regression tests live under ``clang/test/Verify/``. From the **repository root**:

.. list-table::
   :header-rows: 1
   :widths: 32 68

   * - Script
     - Purpose
   * - ``./scripts/run-verify-tests.sh``
     - Run executable examples (pass / expected-fail).
   * - ``./scripts/coverage-sweep.sh``
     - Fast profile merge after a normal build (from repo root).
   * - ``./scripts/coverage-verify.sh``
     - Full instrumented rebuild + sweep (slow; use when changing coverage setup).

Set ``CPPVERIFY_ENABLE_COVERAGE=ON`` on ``clangVerify`` only — not the whole LLVM tree.

Engine headers: :doc:`../api/index`.