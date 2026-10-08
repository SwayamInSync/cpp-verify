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
  off). The master switch: enables the constructs and the codegen stripping. With it
  off, the file is plain C++ and the verifier never runs.
- **Run the prover** — ``-fno-verify`` (the verifier runs by default once contracts
  are on). There is no ``-fverify`` — it would just be the default.

``-fno-verify`` **implies ``-fverify-contracts``** (unless ``-fno-verify-contracts``
is given), so a lone ``-fno-verify`` is a fast **light check**: it validates C++ and
contract syntax *and* contract semantics, but not your logic — handy for editors,
CI pre-flight, and LLM/agent loops.

Other flags
-----------

- ``cpp-verify --backend={z3,cvc5,portfolio,race,bmc,lean}`` — verification
  engine: Z3 (the default), cvc5, both with agreement required
  (``portfolio``), both at once with the first proof or certified
  counterexample standing (``race``), bounded model checking, or Lean export
  (see :doc:`ch17-backends-modular-calls`)
- ``cpp-verify --cvc5-path=FILE`` — the cvc5 executable, for ``cvc5``,
  ``portfolio``, and ``race``
- ``cpp-verify --check-ub`` / ``--no-check-ub`` — the default memory checks
  (object bounds of accesses and pointer arithmetic, enumeration ranges) on or
  off; core definedness stays on (see :doc:`ch18-undefined-behavior`)
- ``cpp-verify --int-encoding={auto,integer,bitvector}`` — how machine
  integers reach the solver; every choice is exact, so only speed changes
  (see :doc:`../../language/integers`)
- ``cpp-verify --profile-quantifiers`` — for an unresolved quantified query,
  report how often each quantifier was instantiated (see
  :doc:`ch16-when-verification-fails`)
- ``cpp-verify --unroll=N`` — loop bound for BMC
- ``cpp-verify --timeout=N`` — per-query solver timeout in ms (default 30000)
- ``cpp-verify --collection-timeout=N`` — per-query timeout for queries over
  sequences, sets, multisets, or maps (default twice ``--timeout``)
- ``cpp-verify --function-timeout=N`` — time all queries of one function may
  take together (default ten times ``--timeout``; ``0`` disables)
- ``cpp-verify --certify-timeout=N`` — time checking one counterexample
  against the true definitions may take (default half the query timeout;
  ``0`` lets it take the query's own time), so one slow model leaves time to
  others
- ``cpp-verify --solver-rlimit=N`` — deterministic per-query resource budget
  for Z3 and cvc5 (``0`` disables)
- ``cpp-verify --max-query-nodes=N`` — refuse a query larger than ``N``
  expression nodes (``query.size-limit``)
- ``cpp-verify --jobs=N`` — solver workers shared by all functions (default
  every core)
- ``cpp-verify --proof-cache=DIR`` — keep proofs of single obligations between
  runs (``--proof-cache-max-mb``, ``--proof-cache-max-entries`` bound it)
- ``cpp-verify --diagnostics-format=json`` — emit versioned
  ``cppverify.diagnostic/1`` JSON Lines for verification results
- ``cpp-verify --lean-out=FILE`` — with ``--backend=lean``, write a standalone
  Lean scratch-pad
- ``cpp-verify --lean-project=DIR`` — generate a preserved, pinned Lean project
- ``cpp-verify --lean-fallback=DIR`` — export the obligations Z3 left unproved
  in unresolved functions to Lean (``--lean-fallback-scope=all`` exports every
  obligation of those functions)
- ``cpp-verify --lean-certify`` — kernel-check all active project proofs without
  admissions or undocumented proof axioms
- ``cpp-verify --dump-ir[=1,2,3,4]`` — dump VCR / passive / Obligation IR / Z3 layers
- ``cpp-verify --lower-only`` — construct and encode VCs without invoking Z3's
  satisfiability check
- ``cpp-verify --obligation-out=FILE`` — write validated, versioned canonical
  obligation records with semantic hashes
- ``cpp-verify --obligation-in=FILE`` — validate and replay records through Z3,
  lower-only dumps, or Lean scratch export without reparsing C++; records made
  by BMC retain and enforce their archived unroll bound

IR layers
---------

1. VCR (control-flow IR)
2. Passive (SSA assume/assert)
3. Canonical Obligation IR (typed complete and ordered queries)
4. Z3 (SMT string)

Multiple layers are separated by ``======`` in the dump.

Use ``--lower-only`` with the dump flags when testing a lowering rule. The
frontend, VCR transforms, passive SSA, canonical obligation construction, and
Z3 encoding all run, including spec-axiom encoding, but ``Solver.check()`` does
not. ``Lowered`` therefore means “well-formed through backend encoding,” not
“proved.” This is stronger than ``clang++ -fno-verify``, which stops before the
verification IR pipeline.

Compiler flags table and IR dump details: :doc:`../../language/tooling`.

Engine API: :doc:`../../api/index`.
