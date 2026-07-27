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
   * - ``clang++ -fno-verify``
     - Light check — contracts on, skip the solver

Two axes
--------

Contract behaviour is two independent switches (full reference and a quick-lookup
table: :doc:`../../language/tooling`):

- **Contract language** — ``-fverify-contracts`` / ``-fno-verify-contracts`` (default
  off). The master switch: enables the keywords and the codegen stripping. With it
  off, the file is plain C++ and the verifier never runs.
- **Run the prover** — ``-fno-verify`` (the verifier runs by default once contracts
  are on). There is no ``-fverify`` — it would just be the default.

``-fno-verify`` **implies ``-fverify-contracts``** (unless ``-fno-verify-contracts``
is given), so a lone ``-fno-verify`` is a fast **light check**: it validates C++ and
contract syntax *and* contract semantics, but not your logic — handy for editors,
CI pre-flight, and LLM/agent loops.

Other flags
-----------

- ``cpp-verify --backend={z3,bmc,lean}`` — verification engine (see :doc:`ch17-backends-modular-calls`)
- ``cpp-verify --check-ub`` — add ``valid(p, n)`` buffer-bounds checks to
  always-on core definedness (see :doc:`ch18-undefined-behavior`)
- ``cpp-verify --unroll=N`` — loop bound for BMC
- ``cpp-verify --timeout=N`` — per-query Z3 timeout in ms (default 30000)
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
