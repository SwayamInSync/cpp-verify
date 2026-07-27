Chapter 17 — Backends, modular calls, and debugging
===================================================

CppVerify is not only a Z3-backed WP checker. The same front end and IR feed multiple
backends and modular call lowering. This chapter ties those pieces to how you work day to day.

Verification backends
---------------------

.. list-table::
   :header-rows: 1
   :widths: 18 22 60

   * - Backend
     - CLI
     - When to use it
   * - **Z3** (default)
     - ``cpp-verify file.cpp``
     - General proofs: functions, pointers, spec/proof, loops via invariant/decreases (WP path).
   * - **BMC**
     - ``cpp-verify --backend=bmc --unroll=N file.cpp``
     - Small bounded loops: body unrolled ``N`` times, then Z3. Good when loop structure is simple and bounds are tiny.
   * - **Lean export**
     - ``cpp-verify --backend=lean --lean-out=out.lean file.cpp``
     - Export the canonical correctness obligation as an unchecked theorem
       with ``sorry``. This does not run Z3 and reports ``Exported``, not a
       proof result.

BMC does not replace loop contracts on the default path; it is an alternate pipeline stage that
**expands** loops before passivization. You still write ``invariant`` / ``decreases`` for documentation
and for the Z3 backend.

Modular function calls
----------------------

Functions with ``pre`` / ``post`` are verified **modularly**: the caller assumes the callee’s
precondition and inherits its postcondition (and frame conditions) without re-analyzing the callee body.

Simple call:

.. code-block:: cpp

   int y = abs_val(x);

Chained calls in one expression are supported by lowering inner calls to temporaries first:

.. code-block:: cpp

   int inc(int x) pre(x >= 0 && x < 100) post(result == x + 1) { return x + 1; }

   int twice(int x)
     pre(x >= 0 && x < 98)
     post(result == x + 2)
   {
     return inc(inc(x));   // inner inc, then outer inc
   }

The converter emits ``VCallStmt`` for each exec call site; passivization substitutes callee contracts
in order. Spec and proof functions are not emitted at runtime and are handled by inlining or axioms.

By-value parameters have separate entry and final meanings when the callee
reassigns them. Preconditions and ``old(parameter)`` substitute the caller's
argument. A plain parameter occurrence in the postcondition uses a fresh final
callee-local value when that formal was modified, so ``post(p == nullptr)``
after rebinding a local pointer cannot contradict the caller's non-null
argument.

Calls also enforce the caller's frame in its **entry state**. Exact footprints
(``p[i]``, ``p->field``) freshen only those addresses. A region footprint
(``*p``), or a pointer-taking declaration with no explicit footprint, freshens
the complete value heap because parameter allocation identity does not yet
cross modular boundaries. The postcondition then re-establishes whatever the
caller may rely on. This conservative boundary prevents offset writes from
masquerading as preservation of unrelated memory. Functions that perform
dynamic allocation or deallocation are currently verified only as standalone
bodies; calls to them fail closed until lifetime effects have contract syntax.

A caller-owned dynamic scalar may be passed in the other direction to a
verified, non-allocating executable callee. Its direct matching pointer
parameter may be compared or dereferenced, including a write authorized by
``modifies(*p)``. The call substitutes the caller's lifetime identity into
validity checks and accepts the footprint only after proving that identity is
one of the caller's live allocations. Acyclic direct-pointer forwarding,
scalar-value executable/spec helpers, and direct/conditional/null pointer
results are checked recursively. Pointer results receive a separate SSA
provenance target and need a result-equality contract to recover owned alias
authority. Offset/subscript access, pointer copies or rebinding, nested
pointer-result calls, recursion cycles, ghost use, proof/external contracts,
and allocation in the callee fail closed. Within the caller, address and
identity remain a pair through local copies, assignments, branches,
``nullptr``, and supported call results.

Z3 result discipline
--------------------

Passive SSA is lowered once into a typed, source-attributed
``ObligationModule``. Layer 3 dumps this exact module and all backends consume
it. It contains one complete counterexample query plus equivalent ordered
assertion/postcondition queries with deterministic IDs. The default backend
first submits the complete query.
``unsat`` means verified and ``sat`` produces a counterexample. On ``unknown``,
CppVerify retries the module-owned assertions separately in source order, using
only entry facts and assumptions that precede each obligation. It does not
rebuild a second VC. The retry helps quantified heap programs without letting a
later assumption prove an earlier assertion. If it still cannot discharge every
obligation, the final result remains ``unknown`` and the function is not
certified.

Parallel verify + compile
-------------------------

.. code-block:: bash

   clang++ -std=c++17 -fverify-contracts -c module.cpp -o module.o

With ``-fverify-contracts``, contract keywords parse as part of the language. Unless you pass
``-fno-verify``, the compiler runs **cpp-verify in parallel** with code generation. Ghost blocks,
spec functions, and proof functions are stripped from the object file — no runtime cost.

Dumping IR layers
-----------------

When a proof fails or looks wrong, dump intermediate representations:

.. code-block:: bash

   cpp-verify --dump-ir=1 file.cpp      # Layer 1: VCR (typed CFG)
   cpp-verify --dump-ir=2 file.cpp      # Layer 2: passive (SSA assume/assert)
   cpp-verify --dump-ir=3,4 file.cpp   # canonical Obligation IR and Z3 translation

Layer aliases: ``layer-1`` … ``layer-4``, or ``all``. Multiple layers are separated by ``======``.

``recommends`` and soft checks
------------------------------

``recommends`` on spec functions is optional advice. If verification **fails**, the tool may
report that a ``recommends`` clause at a call site was not implied by the caller’s precondition —
a warning, not a hard error.

Regression tests
----------------

The repository ships executable examples under ``clang/test/Verify/`` and ``clang/test/Verify/suite/``.
From the repo root:

.. code-block:: bash

   ./scripts/run-verify-tests.sh

Contributors can measure ``clang/lib/Verify`` region coverage with
``./scripts/coverage-sweep.sh`` (after a normal build) or ``./scripts/coverage-verify.sh``
(full instrumented rebuild). Use ``-DCPPVERIFY_ENABLE_COVERAGE=ON`` on ``clangVerify`` only.

Next: :doc:`ch16-when-verification-fails` for counterexamples and fixing failed proofs.