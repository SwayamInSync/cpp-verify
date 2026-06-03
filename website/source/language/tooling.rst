Commands and flags
==================

Standalone verifier
-------------------

.. code-block:: bash

   cpp-verify file.cpp
   cpp-verify --backend=z3 file.cpp
   cpp-verify --backend=bmc --unroll=3 file.cpp
   cpp-verify --backend=lean --lean-out=goal.lean file.cpp
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
   * - ``--timeout=N``
     - Per-query Z3 timeout in milliseconds (default 10000; ``0`` disables). A query
       that exceeds it is reported as ``unknown`` instead of hanging.

Supported compiler
------------------

Contract syntax and ``-fverify-contracts`` exist **only in this repository's
Clang**. Use the shipped ``./build/bin/cpp-verify`` and
``./build/bin/clang++`` for any code that uses contracts — stock GCC or upstream
Clang reject the flag and the contract keywords. (Building cpp-verify itself from
source is independent and works with any standard host compiler.)

Compile with contracts
----------------------

.. code-block:: bash

   clang++ -std=c++17 -fverify-contracts -c file.cpp -o file.o
   clang++ -std=c++17 -fverify-contracts -fno-verify -c file.cpp -o file.o

.. list-table::
   :header-rows: 1
   :widths: 28 72

   * - Flag
     - Effect
   * - ``-fverify-contracts``
     - Enable contract keywords (``pre``, ``post``, ``spec``, ``ghost``, …).
   * - ``-fno-verify``
     - Parse contracts but skip SMT; compile only (no parallel verify).

Without ``-fno-verify``, verification runs **in parallel** with code generation (see
:doc:`../book/part-ii/ch17-backends-modular-calls`).

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