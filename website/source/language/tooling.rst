Commands and flags
==================

Standalone verifier
-------------------

.. code-block:: bash

   cpp-verify file.cpp
   cpp-verify --backend=z3 file.cpp
   cpp-verify --backend=cvc5 file.cpp
   cpp-verify --backend=portfolio file.cpp
   cpp-verify --backend=bmc --unroll=3 file.cpp
   cpp-verify --backend=lean --lean-out=goal.lean file.cpp
   cpp-verify --backend=lean --lean-project=proof file.cpp
   cpp-verify --backend=lean --lean-project=proof --lean-certify file.cpp
   cpp-verify --lean-fallback=proof file.cpp
   cpp-verify --no-check-ub file.cpp
   cpp-verify --profile-quantifiers file.cpp
   cpp-verify --timeout=20000 file.cpp
   cpp-verify --jobs=4 --proof-cache=.cppverify-cache file.cpp
   cpp-verify --solver-rlimit=500000 --max-query-nodes=50000 file.cpp
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
   * - ``--backend=cvc5``
     - Encode each canonical obligation as standalone SMT-LIB2 and run an
       installed cvc5. ``unsat`` is ``Verified``, ``sat`` is ``Failed``, and
       unavailable/malformed/unknown execution is ``Unresolved``.
   * - ``--backend=portfolio``
     - Strictly run Z3 and cvc5 on each ordered canonical obligation. Only
       matching ``unsat`` results are ``Verified`` and matching ``sat`` results
       are ``Failed``. A timeout, missing solver, malformed output, unsupported
       query, or opposite verdict is ``Unresolved``; decisive disagreement uses
       reason ``backend.inconsistent-results``.
   * - ``--cvc5-path=FILE``
     - Use this cvc5 executable instead of searching ``PATH``. cvc5 is an
       optional system dependency and is not vendored.
   * - ``--backend=bmc``
     - Incrementally unroll loops from zero through ``--unroll=N`` (default 10),
       stopping at the first counterexample, complete unwinding proof,
       unresolved query, or maximum frontier.
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
     - On the Z3 or strict-portfolio path, export functions that remain
       ``Unresolved`` to an editable Lean project, for example
       ``Exported: lean fallback: f [z3: 18 of 20 proved; lean: 2 exported]``.
       Initial export remains a non-success result. Rerun with
       ``--lean-certify`` after completing the preserved proof files: a
       function whose exported goals all kernel-check reports
       ``Proved (z3+lean)`` (JSON ``"status":"mixed-proof"`` with an
       ``evidence`` record), or ``Certified`` when Lean checked every goal.
   * - ``--lean-fallback-scope=unproved|all``
     - ``unproved`` (default) exports only the obligations the solver did not
       prove individually; each keeps the goal name it has in a complete
       export. ``all`` exports every obligation of the function, so success
       is ``Certified``.
   * - ``--unroll=N``
     - Maximum BMC loop bound. Source verification explores ``0..N``;
       lower-only and archive replay retain one exact recorded bound.
   * - ``--check-ub``
     - The default. On every backend, prove each memory access lies in an
       object: a ``valid(p, n)`` precondition declares a buffer extent, and a
       pointer without one addresses a single object. Indexed accesses,
       pointer arithmetic, modular sub-slices, and same-array pointer
       positions are checked. Extent markers must be positive top-level
       conjunction clauses on bare pointers. See :doc:`integers` and
       :doc:`pointers`.
   * - ``--no-check-ub``
     - Turn memory checking off. Core expression definedness (overflow,
       division, shifts, and dereferences of null or dead storage) is always
       checked. Region ``modifies`` footprints then forget the whole heap at
       a call.
   * - ``--profile-quantifiers``
     - For a quantified Z3 query left unresolved, rerun it counting each
       quantifier's instantiations and report the busiest, by the source
       location of the quantifier (``note: the quantifier at L:C was
       instantiated N times, up to generation G``; JSON
       ``quantifier_profile``). Use it to find matching loops and poor
       triggers. Needs a POSIX host.
   * - ``--timeout=N``
     - Per-query solver timeout in milliseconds (default 30000; ``0`` disables).
       A query that exceeds it is reported as unresolved instead of hanging.
   * - ``--solver-rlimit=N``
     - Deterministic per-query Z3/cvc5 resource budget (default ``0``, disabled).
       Exhaustion is ``Unresolved``. Z3 reports ``solver.resource-limit``;
       cvc5 may report the conservative ``solver.unknown``.
   * - ``--max-query-nodes=N``
     - Reject a solver-backed canonical obligation module larger than ``N``
       expression nodes before verification, lower-only encoding, or a requested
       Z3 dump (default ``0``, disabled). Exhaustion is fail-closed with reason
       ``query.size-limit``.
   * - ``--int-encoding=MODE``
     - Solver representation of machine integers for Z3, cvc5, portfolio, and
       BMC: ``auto`` (default; integers reduced modulo ``2^N`` unless a query
       needs the bits of a non-constant operand, then bit-vectors),
       ``integer``, or ``bitvector``. Every mode is exact; only solver
       performance differs. See :doc:`integers`.
   * - ``--jobs=N``
     - Solve ordered obligations in up to ``N`` isolated Z3 contexts or cvc5
       processes while publishing results in source order (default ``1``;
       ``0`` selects available physical cores). Lean export remains serial.
   * - ``--proof-cache=DIR``
     - Persist successful dependency-scoped Z3 or BMC proofs. In portfolio mode
       this caches only the Z3 component and cvc5 still runs on every query.
       Standalone cvc5 does not use this cache. Failed,
       unresolved, and bounded-safe results are never proof-cache entries.
       Corrupt or incompatible entries are rejected rather than treated as hits.
   * - ``--proof-cache-max-mb=N``
     - Bound proof-cache storage in MiB (default 1024; ``0`` disables the byte
       limit).
   * - ``--proof-cache-max-entries=N``
     - Bound the number of proof-cache records (default 100000; ``0`` disables
       the entry limit).
   * - ``--diagnostics-format={text,json}``
     - Select Clang-style text (default) or versioned JSON Lines for verification
       results. JSON records use schema ``cppverify.diagnostic/1``.
   * - ``--lower-only``
     - Run Clang conversion, backend-specific preparation, passivization,
       canonical Obligation IR construction, spec-axiom encoding, and selected
       Z3/SMT-LIB translation without calling a solver. Supported for Z3, cvc5,
       portfolio, and BMC.
   * - ``--obligation-out=FILE``
     - Write deterministic, versioned backend-neutral modules with portable
       source attribution and SHA-256 semantic identities. Multiple modules are
       concatenated in one archive.
   * - ``--obligation-in=FILE``
     - Validate and replay an archive without reparsing C++. Supports Z3, cvc5,
       strict portfolio, ``--lower-only``/Layer 3-4 dumps, and Lean scratch
       export. Archives
       produced after BMC unrolling retain their bound and replay with BMC
       unwinding semantics; applying BMC to an untransformed archive is
       rejected because unrolling must run before obligation lowering.
       Each module is replayed on its own: a module that relies on a spec's
       termination, ``reads``, or ``post`` is not demoted when that spec's own
       module fails, which the replay reports separately.

``--lower-only`` is deliberately different from compiler ``-fno-verify``.
``-fno-verify`` stops after Clang syntax and contract semantic checks;
``--lower-only`` exercises the complete verification pipeline through backend
encoding. A successful run prints ``Lowered: function``. That means the formula
was constructed and encoded, **not** that its obligations are true.

Backend results are intentionally distinct. Z3 ``unsat`` reports ``Verified``;
``sat`` reports a failed source obligation; timeout/``unknown`` reports
``Unresolved``. cvc5 follows the same status mapping without model extraction.
Portfolio mode requires agreement; an agreed ``sat`` result uses Z3's typed
model and trace, while disagreement or incomplete secondary evidence is
``Unresolved``. BMC reports ``BoundedSafe(N)`` when only its unwinding
obligation fails at the maximum frontier, and reports ``Verified`` only when an
explored bound proves complete unwinding. Text diagnostics publish the terminal
``bound``, all attempted ``bounds``, and the count of successful ordered queries
reused across prefixes. JSON uses ``bound``, ``explored_bounds``, and
``reused_queries``. Lean generation reports ``Exported``. Only the pinned,
admission-free kernel workflow reports ``Certified``.

Parallel solving and proof caching
----------------------------------

``--jobs`` parallelizes only backend solving. Clang conversion, VCR transforms,
canonical obligation construction, dumps, archives, Lean generation, and
diagnostic publication stay serial and deterministic. Each worker owns a fresh
Z3 context/solver or a separate cvc5 process; no AST or solver state is shared
between workers.
The first failing source obligation is therefore identical for ``--jobs=1`` and
``--jobs=N`` even if worker completion order differs.

With ``--proof-cache``, CppVerify solves and caches individual ordered
obligations. A cache key combines the dependency-scoped semantic hash, semantic
hash format, backend namespace, adapter version, and exact Z3 version. BMC uses a
separate namespace, and its unroll provenance is semantic, so a bounded proof
cannot satisfy an unbounded Z3 lookup or another bound. Target widths, layout
constants, UB instrumentation, spec fuel, and other relevant choices are already
lowered into the canonical goal and its reachable declarations.

Only ``Verified`` obligations are written, using immutable records and atomic
replacement. Counterexamples, timeouts, resource exhaustion, unknown results,
and ``BoundedSafe`` frontiers are solved again. A malformed or unreadable lookup
produces ``cache.corrupt`` or ``cache.io-failed`` rather than proof success.
Failure to store or prune after a fresh proof is reported as cache-error
telemetry but does not invalidate that solver verdict. Pruning still runs after
cache errors, retries capacity-limited writes after eviction, and removes
abandoned atomic-write files after 24 hours while leaving newer concurrent
writes alone. Text results show ``[cache=hits/queries]`` and JSON records carry
``cache.hits``, ``cache.misses``, and ``cache.errors``. The same cache is usable
during source verification and canonical archive replay. It is a trusted local
memoization store, not a portable proof certificate: do not share a cache
directory with untrusted writers. Use Lean certification when independent
kernel checking is required.

Structured diagnostics
----------------------

Failed Z3, cvc5, portfolio, and BMC results identify a source-anchored
obligation such as ``function-identity::overflow@line:column#2``. The kind says
what the obligation checks:

- contracts: ``assertion``, ``precondition``, ``postcondition``,
  ``invariant-entry``, ``invariant-preserved``, ``termination``,
  ``type-invariant``, and ``recommends``;
- C++ definedness: ``overflow`` (including a mathematical value converted to
  a machine type it does not fit), ``division-by-zero``, ``shift``,
  ``bounds``, ``dereference``, ``initialization``, ``pointer-difference``,
  and ``deallocation``;
- generated interfaces: ``pointer-validity`` (a pointer parameter, result, or
  ``valid(p, n)`` extent must denote valid storage), ``aliasing`` (implicit
  non-aliasing), ``frame`` (writes and callee effects stay within
  ``modifies``), and ``missing-return``;
- ``unwinding`` for a BMC bound, and ``unsupported`` for a construct the
  verifier rejects fail-closed.

The local suffix only disambiguates obligations of one kind at the same anchor,
so inserting or reordering an unrelated obligation does not renumber later IDs
unless its source anchor moves. JSON records carry the kind as
``obligation.kind``. Diagnostics include inclusive source ranges and source
display names while retaining internal SSA names for unambiguous tooling.

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
``solver.resource-limit``, ``solver.unavailable``,
``solver.invocation-failed``, ``solver.malformed-output``,
``query.size-limit``, ``encoding.failed``,
``obligation.invalid``, ``logic.unsupported``, ``query.missing``,
``backend.invalid-result``,
``backend.inconsistent-results``, ``bmc.incomplete-bound``,
``lean.export-failed``, ``cache.corrupt``, ``cache.io-failed``,
``spec.fuel``, ``spec.hidden``, ``spec.termination``, ``spec.reads``,
``spec.post``, ``counterexample.unchecked``, ``callee.contract``,
``decreases.missing``, and ``construct.unsupported``.

What a verified result rests on
-------------------------------

A verified result may carry qualifiers that say what the proof assumed:

- ``[partial]``: it holds only for terminating executions, after
  ``decreases(*)`` here or in a callee (JSON ``"partial": true``).
- ``[trusts=f,g]``: it relies on the contracts of ``f`` and ``g``, marked
  ``[[cppverify::trusted]]``, directly or through verified callees (JSON
  ``"trusts": ["f", "g"]``). Each trusted function itself reports
  ``Trusted: f (contract assumed, not verified)`` (JSON ``"status":
  "trusted"``). See :doc:`functions-loops`.
- ``[vacuous]``: no execution reaches the claim, so it holds for no reason
  (JSON ``"vacuous": true``), with a warning naming the cause.

A proof can only hold vacuously when an assumption excludes every execution,
and assumptions enter a function in a few places: its preconditions and type
invariants, its behaviors' assumptions, and the contracts of its callees.
Every ``Verified`` result is checked at each:

.. list-table::
   :header-rows: 1
   :widths: 35 65

   * - Cause
     - Warning
   * - The preconditions (with type invariants) are unsatisfiable.
     - ``f: the precondition is unsatisfiable, so every claim about it holds
       vacuously``
   * - No execution reaches the end of the function.
     - ``f: no execution reaches the end, so its postcondition holds
       vacuously; check the contracts it calls and its assumptions``
   * - A behavior's assumption contradicts the preconditions.
     - ``f: behavior b never applies: its assumption contradicts the
       preconditions, so its postconditions are never checked`` (the result
       itself is not ``[vacuous]``: the other behaviors were checked)
   * - A trusted contract cannot hold in the state of one call.
     - ``f: the trusted contract of g contradicts the state of this call, so
       everything after it holds vacuously``, at the call

A verified callee always returns, so only a trusted contract can end the
paths through a call. Unreachable code itself is not flagged: a defensive
``if (p == nullptr) return -1;`` under ``pre(p != nullptr)`` is dead for a
good reason, and every claim the function makes is still checked on the
paths that remain.

``--diagnostics-format=json`` covers verification-result diagnostics.
Command-line validation and frontend parse errors may still use text. Combining
JSON diagnostics with IR dumps intentionally creates a mixed stream. Malformed
byte sequences in source or archive display text are rendered with the Unicode
replacement character, so every emitted JSON record remains valid UTF-8.

Portable obligation archives
----------------------------

``--obligation-out`` writes ``cppverify.obligation/2`` records only after exact
serialize/deserialize/validate/reserialize checks. Stable wire tags make the
format independent of C++ enum ordinals. The reader rejects malformed magic,
unsupported versions, truncation, invalid tags, inconsistent feature
declarations, duplicate identities, and oversized/deep expressions.
Schema v2 adds the precise obligation kinds; schema v1 records, which name
only assertions, postconditions, and unwinding checks, are still read.
Records cap integer widths at 4096 bits, expression depth at 4096, and
collections plus expression nodes/edges at 100,000 per record. It also rejects
embedded NULs, non-canonical numerals, inactive payload fields, ill-scoped
variables, conflicting module-wide free-symbol sorts across semantic and
diagnostic expressions, and contradictory complete/ordered queries before
backend dispatch.

Module and per-obligation SHA-256 hashes omit source paths and display-only
names, source ranges, internal positional and public source-anchored IDs,
obligation kinds other than ``unwinding``, and traces, so moving unchanged
source, inserting an unrelated earlier obligation, or changing display metadata
preserves an individual goal's semantic identity.
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
introduced this canonical boundary, format v3 excluded positional and public
diagnostic identities, and format v4 keeps only whether an obligation is an
unwinding check.

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