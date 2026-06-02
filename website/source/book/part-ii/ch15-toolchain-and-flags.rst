Chapter 15 — Toolchain and flags
================================

Tools
-----

.. list-table::
   :header-rows: 1
   :widths: 28 72

   * - Tool
     - Role
   * - ``cpp-verify``
     - Verify-only driver
   * - ``clang++ -fverify-contracts``
     - Parse contracts + verify (parallel) + compile
   * - ``clang++ -fverify-contracts -fno-verify``
     - Contracts on; skip SMT

Key flags
---------

- ``-fverify-contracts`` — enable contract keywords
- ``-fno-verify`` — compile path without Z3
- ``cpp-verify --backend={z3,bmc,lean}`` — verification engine (see :doc:`ch17-backends-modular-calls`)
- ``cpp-verify --unroll=N`` — loop bound for BMC
- ``cpp-verify --dump-ir[=1,2,3,4]`` — dump VCR / passive / VC / Z3 layers

IR layers
---------

1. VCR (control-flow IR)
2. Passive (SSA assume/assert)
3. VC (formula)
4. Z3 (SMT string)

Multiple layers are separated by ``======`` in the dump.

Compiler flags table and IR dump details: :doc:`../../language/tooling`.

Engine API: :doc:`../../api/index`.

