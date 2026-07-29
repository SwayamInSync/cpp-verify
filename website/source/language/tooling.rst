Commands and flags
==================

Standalone verifier
-------------------

.. code-block:: bash

   cpp-verify file.cpp
   cpp-verify --backend=z3 file.cpp
   cpp-verify --backend=bmc --unroll=3 file.cpp
   cpp-verify --backend=lean --lean-out=goal.lean file.cpp
   cpp-verify --backend=lean --lean-project=proof file.cpp
   cpp-verify --backend=lean --lean-project=proof --lean-certify file.cpp
   cpp-verify --lean-fallback=proof file.cpp
   cpp-verify --check-ub file.cpp
   cpp-verify --timeout=20000 file.cpp
   cpp-verify --diagnostics-format=json file.cpp
   cpp-verify --dump-ir=1,2,3,4 file.cpp
   cpp-verify --lower-only --dump-ir=1,2,3,4 file.cpp
   cpp-verify --lower-only --obligation-out=goals.cpv file.cpp
   cpp-verify --obligation-in=goals.cpv --backend=z3

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
   * - ``--lean-project=DIR``
     - With ``--backend=lean``, generate a pinned editable project. Generated
       semantics live in ``CppVerify/Generated.lean``; reusable lemmas and
       per-obligation proof files are preserved across regeneration.
   * - ``--lean-certify``
     - Build the active project with Lean 4.32.2, reject ``sorry`` and
       undocumented proof axioms, and report ``Certified`` only after every
       active proof kernel-checks. Requires ``--lean-project`` or
       ``--lean-fallback``.
   * - ``--lean-fallback=DIR``
     - On the default Z3 path, export only functions that remain
       ``Unresolved`` to an editable Lean project. Initial export remains a
       non-success result. Rerun with ``--lean-certify`` after completing the
       preserved proof files.
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
   * - ``--diagnostics-format={text,json}``
     - Select Clang-style text (default) or versioned JSON Lines for verification
       results. JSON records use schema ``cppverify.diagnostic/1``.
   * - ``--lower-only``
     - Run Clang conversion, backend-specific preparation, passivization,
       canonical Obligation IR construction, spec-axiom encoding, and Z3
       translation without calling the solver. Supported for Z3 and BMC.
   * - ``--obligation-out=FILE``
     - Write deterministic, versioned backend-neutral modules with portable
       source attribution and SHA-256 semantic identities. Multiple modules are
       concatenated in one archive.
   * - ``--obligation-in=FILE``
     - Validate and replay an archive without reparsing C++. Supports Z3,
       ``--lower-only``/Layer 3-4 dumps, and Lean scratch export. Archives
       produced after BMC unrolling retain their bound and replay with BMC
       unwinding semantics; applying BMC to an untransformed archive is
       rejected because unrolling must run before obligation lowering.

``--lower-only`` is deliberately different from compiler ``-fno-verify``.
``-fno-verify`` stops after Clang syntax and contract semantic checks;
``--lower-only`` exercises the complete verification pipeline through backend
encoding. A successful run prints ``Lowered: function``. That means the formula
was constructed and encoded, **not** that its obligations are true.

Backend results are intentionally distinct. Z3 ``unsat`` reports ``Verified``;
``sat`` reports a failed source obligation; timeout/``unknown`` reports
``Unresolved``. BMC reports ``BoundedSafe(N)`` when only its unwinding
obligation fails, and reports ``Verified`` only when the selected bound itself
is proved complete. Lean generation reports ``Exported``. Only the pinned,
admission-free kernel workflow reports ``Certified``.

Structured diagnostics
----------------------

Failed Z3 and BMC results identify a source-anchored obligation such as
``function-identity::postcondition@line:column#2``. The local suffix only
disambiguates obligations at the same anchor, so inserting or reordering an
unrelated obligation does not renumber later IDs unless its source anchor
moves. Diagnostics include inclusive source ranges and source display names
while retaining internal SSA names for unambiguous tooling.

Counterexample values carry exact sorts such as ``bool``, ``i32``, ``u32``,
``math-i32``, ``pointer``, and ``heap``. Z3 model completion is disabled:
undetermined values print as ``<unknown>`` and become JSON ``null``. Signed and
unsigned bit-vectors are decoded to source-level decimal values.

Counterexample traces may contain guarded branch, modular-call, loop,
heap-write, allocation/provenance, lifetime-end, deletion, and return events.
False guards are omitted; a guard the model does not determine is retained with
JSON ``"active": null`` rather than an invented path choice. Archives preserve
the same names, ranges, IDs, and trace data during replay.

Each non-success verification result also carries a stable reason code. Current
codes include ``counterexample``, ``solver.timeout``, ``solver.unknown``,
``encoding.failed``, ``obligation.invalid``, ``logic.unsupported``,
``query.missing``, ``backend.invalid-result``,
``backend.inconsistent-results``, ``bmc.incomplete-bound``, and
``lean.export-failed``.

``--diagnostics-format=json`` covers verification-result diagnostics.
Command-line validation and frontend parse errors may still use text. Combining
JSON diagnostics with IR dumps intentionally creates a mixed stream. Malformed
byte sequences in source or archive display text are rendered with the Unicode
replacement character, so every emitted JSON record remains valid UTF-8.

Portable obligation archives
----------------------------

``--obligation-out`` writes ``cppverify.obligation/1`` records only after exact
serialize/deserialize/validate/reserialize checks. Stable wire tags make the
format independent of C++ enum ordinals. The reader rejects malformed magic,
unsupported versions, truncation, invalid tags, inconsistent feature
declarations, duplicate identities, and oversized/deep expressions.
Schema v1 caps integer widths at 4096 bits, expression depth at 4096, and
collections plus expression nodes/edges at 100,000 per record. It also rejects
embedded NULs, non-canonical numerals, inactive payload fields, ill-scoped
variables, conflicting module-wide free-symbol sorts across semantic and
diagnostic expressions, and contradictory complete/ordered queries before
backend dispatch.

Module and per-obligation SHA-256 hashes omit source paths and display-only
names, source ranges, internal positional and public source-anchored IDs, and
traces, so moving unchanged source, inserting an unrelated earlier obligation,
or changing display metadata preserves an individual goal's semantic identity.
Archives still
retain that metadata for replay diagnostics. Failure-triggered
``recommends`` warnings are diagnostic-only and do not make archive bytes depend
on a solver result. BMC transform provenance is semantic: it is retained in
archives and hashes so bounded obligations cannot be mistaken for unbounded
deductive proofs.

Before hashing or backend dispatch, source-built and replayed modules use the
same conservative canonicalizer. It folds Boolean constants, double negation,
constant conditionals, and reflexive equality/inequality, then removes logical
declarations unreachable from every ordered goal. Exact goal/query pairs and
required features are rebuilt and revalidated. Arithmetic, quantifiers,
pointer/heap terms, and assumptions are left intact. Semantic-hash format v2
introduced this canonical boundary; format v3 excludes positional and public
diagnostic identities while archive schema v1 remains compatible.

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
deterministic internal and source-anchored public obligation IDs/kinds, source
ranges, typed model metadata, guarded trace events, source encodings, and
equivalent ordered queries. A malformed, untyped, or unsupported term fails lowering rather than
becoming a proof-shaped default. Source-built dumps also report canonical
simplification node, rewrite, and dead-declaration counts.

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