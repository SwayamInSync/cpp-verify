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
   * - **cvc5**
     - ``cpp-verify --backend=cvc5 file.cpp``
     - Independent solving through a standalone SMT-LIB2 encoding. Requires an
       installed cvc5 or ``--cvc5-path``.
   * - **Strict portfolio**
     - ``cpp-verify --backend=portfolio file.cpp``
     - Run Z3 and cvc5 over the same ordered canonical obligations. Use when a
       matching independent verdict is more important than accepting either
       solver alone.
   * - **Race**
     - ``cpp-verify --backend=race file.cpp``
     - Run Z3 and cvc5 at once and keep whichever settles a function first,
       as Frama-C's prover list. Use when the solvers' strengths differ, as
       with collections or nonlinear arithmetic, and either solver's word is
       enough.
   * - **BMC**
     - ``cpp-verify --backend=bmc --unroll=N file.cpp``
     - Small bounded loops: grow the unrolling from zero through ``N`` and stop
       at the first decisive frontier. Good when loop structure is simple and
       bounds are tiny.
   * - **Lean**
     - ``cpp-verify --backend=lean --lean-project=proof file.cpp``
     - Generate editable source-attributed goals from the same canonical
       semantics. Initial generation is ``Exported``; an admission-free pinned
       kernel build is ``Certified``.

BMC does not replace loop contracts on the default path; it is an alternate pipeline stage that
**expands** loops before passivization. You still write ``cppverify::invariant`` / ``cppverify::decreases`` for documentation
and for the Z3 backend.

BMC's result is also bounded explicitly. A counterexample inside the explored
prefix is ``Failed``. If safety holds but an unwinding assertion fails, the
result is ``BoundedSafe(N)``, never an unbounded proof. It reports ``Verified``
only when both safety and complete unwinding are proved at an explored bound.
Successful dependency-scoped prefix queries are reused in-process at later
bounds; failed, unresolved, and unwinding-frontier queries are always solved.
Text output lists the attempted bounds and reuse count, while JSON publishes
``explored_bounds`` and ``reused_queries``. Numbered loop events such as
``iteration 2`` reconstruct the counterexample depth at the original loop
source.

A bounded result that no execution reaches says nothing, so BMC runs the
same vacuity checks as Z3 on the program unrolled to the bound, as Kani
reports an unreachable check. When every execution runs a loop past the
bound, the result is ``BoundedSafe ... [vacuous]`` with
``warning: f: no execution finishes within 3 loop iterations, so its bounded
safety covers no complete run; raise --unroll``; an unsatisfiable
precondition is reported as on the default path.

Strict portfolio mode never votes or silently trusts the primary solver. Two
``unsat`` verdicts are ``Verified``; two ``sat`` verdicts are ``Failed`` and use
Z3's typed model/trace. Opposite verdicts, missing cvc5, unknown/timeout,
malformed process output, and unsupported encoding are ``Unresolved``. cvc5 is
not vendored because it is an optional independent implementation; install it
through the platform package manager or select an executable explicitly.

Race mode trusts each solver alone, which is sound: a proof is a proof, and
a counterexample is reported only once the certifier has checked it against
the true definitions, whichever solver found it. The first decisive answer
stops the other solver. When neither settles a function, each obligation one
of them proved counts as proved, since every obligation is a query of its
own; the function is ``Verified`` with ``[backend=z3+cvc5]`` when together
they cover all of them, and otherwise the unresolved ones are listed as for
Z3. Two decisive answers that differ, which a sound pair cannot give, are
``backend.inconsistent-results``.

Backend release fidelity
------------------------

Contributors can run the repeatable cross-backend release gate as a lit test
from the repository root, once the test tools that ``setup.sh`` does not build
exist:

.. code-block:: bash

   ninja -C build FileCheck not count split-file llvm-config
   ./build/bin/llvm-lit -sv clang/test/Verify/suite/backend_fidelity_gate.test

It requires cvc5 and Lean 4.35.0. The gate checks every canonical feature
family through Layer 3 and Z3/cvc5/portfolio/BMC, source-identical failures,
deterministic parallel execution, canonical and bounded archive replay, Lean
theorem/proof-module identity and generated-file compilation, and that
``cppverify::recommends`` warnings stay out of BMC and Lean replay
artifacts. cvc5 may conservatively return ``unknown`` for
designated valid quantified or inductive goals; every false matrix goal must
remain decisive, and any solver disagreement fails the gate.

Differential execution
----------------------

A verdict is also checked against the program it is about.
``clang/utils/cppverify-differential`` holds 484 contracted functions over
integers, ``_BitInt``, pointers and buffers, and records, each with its
precondition and postcondition restated in Python. For each one it:

- verifies the function with Z3 in each integer encoding and with cvc5, or
  with BMC at two bounds;
- compiles the same source with ``-fverify-contracts -fno-verify`` (contracts
  emit no code) and ``-fsanitize=undefined -fsanitize-trap=undefined``, and
  runs it on every input of small parameter types, otherwise on boundary
  values and samples seeded by the function's name, each buffer ending at an
  inaccessible page and then starting after one;
- judges every run the precondition admits by the Python restatement, over
  mathematical integers as contract arithmetic is.

It reports a problem when a function is ``Verified`` (or ``BoundedSafe`` for
an input within the bound) yet an admitted input has undefined behavior or
breaks the postcondition, when a counterexample's input is not admitted or
runs without either, and when two configurations decide differently. CI runs
every case each night; ``clang/test/Verify/differential.test`` runs the tool's
own cases on every change. From the repository root:

.. code-block:: bash

   ninja -C build clang cpp-verify
   python3 clang/utils/cppverify-differential/run.py \
     --cpp-verify build/bin/cpp-verify --suite integers --suite calls

Each line gives a function's verdict in each configuration, the inputs its
precondition admits, how many of them misbehave, and what each counterexample
showed when run:

.. code-block:: text

   u16mul_guard    z3=verified bv=verified int=verified cvc5=verified admitted=17225 violations=0
   long_plus_1u    z3=failed:overflow ... admitted=20380 violations=16 counterexamples: z3 confirmed: undefined behavior at (9223372036854775807,); ...

A failure is evidence relative to the contracts it uses, so not every
counterexample reproduces when the program runs. Here ``weak`` promises less
than it does:

.. cppverify-example: fails m_weak_post

.. code-block:: cpp

   int weak(int x)
     cppverify::post(cppverify::result >= x)
   { return x < 100 ? 100 : x; }

   int m_weak_post(int x)
     cppverify::post(cppverify::result >= 100)
   { return weak(x); }

``m_weak_post`` fails at ``x = 0`` relative to the contract of ``weak``, while
running it returns 100. The tool runs every counterexample it can read. One
that passes a call or an arbitrary loop iteration and does not reproduce is
reported as relative to that abstraction, and so is a failure that a run
cannot show: a check, an invariant, a measure, a frame, a callee's
precondition, an uninitialized read, or a contract that is undefined at the
input (only its body runs). A counterexample of a pointer function, or one
cvc5 found, carries no values to run.

Parallel solving and persistent proofs
--------------------------------------

For a translation unit with several proof obligations:

.. code-block:: bash

   cpp-verify --jobs=4 --proof-cache=.cppverify-cache file.cpp

``--jobs=0`` selects available physical cores. Each ordered obligation runs in
its own Z3 context or cvc5 process, but results are published in source order.
Frontend lowering, IR/archive output, Lean generation, and diagnostics remain
serial, so changing the job count does not change the first reported failure.

The cache stores only ``Verified`` individual obligations. Keys include the
goal's dependency-scoped semantic hash, backend/adapter identity, and exact Z3
version. A portfolio cache entry covers only its namespace-separated Z3
component; cvc5 always reruns. Standalone cvc5 rejects the proof cache. A BMC
cache entry is separate from an unbounded Z3 entry and retains its semantic
unroll provenance. Counterexamples, unknown/resource-limited
queries, and ``BoundedSafe`` results are never cached. Corrupt or unreadable
entries produce ``Unresolved`` instead of being trusted or silently replaced.
Use ``--proof-cache-max-mb`` and ``--proof-cache-max-entries`` to bound storage.
Pruning runs once, after a run's last lookup, and proceeds even when another
cache operation fails; capacity errors evict
an old record and retry once, and abandoned atomic-write files older than 24
hours are removed without disturbing newer concurrent writes.
The opt-in directory is trusted local memoization, not a portable certificate;
do not make it writable by untrusted users. Lean certification remains the
independent kernel-checking path.

Solver work can also be bounded explicitly:

.. code-block:: bash

   cpp-verify --timeout=30000 --solver-rlimit=500000 \
     --max-query-nodes=50000 file.cpp

Timeout, solver resource, and canonical query-size exhaustion remain non-success
results with distinct machine-readable reason codes.

Editable Lean fallback
----------------------

For an explicit interactive proof:

.. code-block:: bash

   cpp-verify --backend=lean --lean-project=proof file.cpp
   # complete proof/CppVerify/Proofs/*/*.lean; put shared lemmas in User.lean
   cpp-verify --backend=lean --lean-project=proof --lean-certify file.cpp

The generated modules (``Prelude.lean``, ``Specs.lean``, ``Goals/``,
``Generated.lean``, ``Auto.lean``, and ``Check.lean``) are machine-owned;
``Check.lean`` imports every proof, so ``lake build``, run in the project,
builds them all (see `One module of goals per function`_ below).
``User.lean`` is never overwritten, and each goal has a proof
file of its own: the proof ``cppverify_auto`` finds for it, or a stub (see
`Proofs cppverify_auto finds`_ below). cpp-verify rewrites that file only while
nobody has edited it; an edited one it never rewrites, but moves with its goal
(see `Proofs that follow their goals`_ below).
The project pins ``leanprover/lean4:v4.35.0``, which certification runs whatever
elan's default toolchain is; a project 0.1 generated, pinned to ``v4.32.2``, moves to
it with a warning. Certification builds the project
and compiles each proof file with admissions promoted to errors, then checks
the compiled modules as described in `What certification checks`_ below.

Each goal is a Lean proposition that means what the obligation means, so a proof of it is a proof of the obligation:

- every operator keeps its grouping under Lean's own precedence:
  ``(a ^ b) + 1`` is ``(a_0 ^^^ b_0) + 1``, since Lean reads
  ``a_0 ^^^ b_0 + 1`` as ``a_0 ^^^ (b_0 + 1)``, and a quantifier is closed
  before whatever follows it;
- a numeral has its type, as in ``(3 : Int)`` and ``(BitVec.ofInt 32 (3))``,
  since Lean reads a term of untyped numerals in ``Nat``, where ``2 - 3`` is
  0;
- a C++ ``int`` or ``unsigned`` is a ``BitVec 32``, a mathematical integer
  an ``Int``, and a Boolean a proposition, so ``return x < 5;`` in a
  function returning ``bool`` gives
  ``__result_1 ↔ (cppBvSlt x_0 (BitVec.ofInt 32 (5)))``;
- machine division by zero is SMT-LIB's, as in the solvers and the
  counterexample checker: ``BitVec.smtUDiv`` gives all ones and
  ``BitVec.smtSDiv`` gives ``-1`` or ``1``, where Lean's own ``/`` gives 0.
  Wherever C++ divides, another obligation proves the divisor nonzero, but
  each goal is read on its own, and Lean reads it as the solvers do;
- a spec application's definition is a hypothesis of the goal; under a
  quantifier it is stated for every value of the quantified variable, as in
  ``∀ (k : Int), total k = …``;
- a machine comparison is ``cppBvSlt``, ``cppBvSle``, ``cppBvUlt``, or
  ``cppBvUle``, which unfold to the Boolean comparison of ``BitVec``, so
  ``decide`` evaluates one at constants.

For example, the call in ``small`` must establish the precondition of
``nonnegative``:

.. cppverify-example: flags --backend=lean --lean-project={dir}/proof

.. code-block:: cpp

   void nonnegative(int n)
     cppverify::pre(cppverify::forall(k, 0, n, k >= 0) && n < 8)
   {
   }

   void small()
     cppverify::post(true)
   {
     nonnegative(3);
   }

``cpp-verify --backend=lean --lean-project=proof file.cpp`` exports four
goals, three of them ``True``, and ``cppverify_auto`` proves all four:

.. code-block:: text

   Exported: lean obligation: nonnegative (cppverify_auto proved 1 of 1 goals)
   Exported: lean obligation: small (cppverify_auto proved 3 of 3 goals)

The one for the call reads:

.. code-block:: lean4

   def cppverify_small_74ff94_precondition_4e324fa2 : Prop :=
     ∀
       (__heap_alloc_0 : CppHeap)
       (__heap_live_0 : CppHeap),
       ¬((heapSelectInt __heap_alloc_0 (0 : Int)) = (0 : Int)) ∨ (heapSelectBool __heap_live_0 (0 : Int)) ∨ ¬(∀ (__quant_0___cppverify_bound_0_k : Int), ((BitVec.ofInt 32 (0))).toInt ≤ __quant_0___cppverify_bound_0_k ∧ __quant_0___cppverify_bound_0_k < ((BitVec.ofInt 32 (3))).toInt → True) ∨ (∀ (__quant_2___cppverify_bound_0_k : Int), ((BitVec.ofInt 32 (0))).toInt ≤ __quant_2___cppverify_bound_0_k ∧ __quant_2___cppverify_bound_0_k < ((BitVec.ofInt 32 (3))).toInt → __quant_2___cppverify_bound_0_k ≥ (0 : Int)) ∧ (cppBvSlt (BitVec.ofInt 32 (3)) (BitVec.ofInt 32 (8)))

A goal is a disjunction: the negated facts it may assume, then what it must
show. The first two facts describe the null pointer (no object owns address
0, and none is live with identity 0); the third is that evaluating the
precondition at ``n = 3`` is defined; the last disjunct is the precondition
there, the quantifier for every ``k`` in ``[0, 3)`` and ``3 < 8``. A proof
by hand, written over the automatic one in its file,
``proof/CppVerify/Proofs/cppverify_small_74ff94/cppverify_small_74ff94_precondition_4e324fa2.lean``
(below its header), proves that disjunct:

.. code-block:: lean4

   import CppVerify.User

   theorem cppverify_small_74ff94_precondition_4e324fa2_proof :
       cppverify_small_74ff94_precondition_4e324fa2 := by
     unfold cppverify_small_74ff94_precondition_4e324fa2
     intro _ _
     have zero : (BitVec.ofInt 32 0).toInt = 0 := by decide
     exact Or.inr (Or.inr (Or.inr ⟨fun _ range => by rw [zero] at range; omega, by decide⟩))

With ``trivial`` for the three ``True`` goals,
``cpp-verify --backend=lean --lean-project=proof --lean-certify file.cpp``
prints:

.. code-block:: text

   Certified: nonnegative [backend=Lean]
   Certified: small [backend=Lean]

The spec collections of ``<cppverify.h>`` reach Lean too (see
`Collections in Lean`_ below).

To keep Z3 as the fast path and export only unresolved functions:

.. code-block:: bash

   cpp-verify --lean-fallback=proof file.cpp
   cpp-verify --lean-fallback=proof --lean-certify file.cpp

The first run reports ``Exported: lean fallback: f [z3: 18 of 20 proved; lean:
2 exported]``, which is not a proof. By default only the obligations the
solver did not prove individually are exported, under the goal names they have
in a complete export; each remaining obligation already has its own solver
proof. When every exported goal kernel-checks the function is
``Proved (z3+lean)``, or ``Proved (portfolio+lean)``, and JSON reports
``"status":"mixed-proof"`` with the per-obligation split. When Lean checked
every obligation, because ``--lean-fallback-scope=all`` exported them all or
the solver proved none on its own, the function is ``Certified``. A certified
counterexample stays a failure, and the project shows it false in Lean too
(`Counterexamples in Lean`_). A fallback run examines in Lean only what its solver
leaves unresolved, so the proofs of the obligations and functions the solver
settles stay where they are until Lean needs them again.

A Lean proof proves the goals it covers, and the verdict built from it rests
on the same facts as a solver's: the contracts of the functions it calls and
the definitions and postconditions of the specs it uses. Certification runs
first, whatever else in the file failed, and those facts are then settled as
for every verdict. A contract that nothing establishes leaves its caller
unresolved, whoever proves the caller:

.. code-block:: cpp

   int next(int x)
     cppverify::post(cppverify::result == 7);

   int seven(int x)
     cppverify::post(cppverify::result == 7)
   {
     return next(x);
   }

With both of ``seven``'s goals proved in Lean, ``cpp-verify --backend=lean
--lean-project=proof --lean-certify file.cpp`` reports:

.. code-block:: text

   warning: next has a contract but no definition, so its callers are not verified; mark the declaration [[cppverify::trusted]] to assume the contract
   Unresolved: seven [backend=Lean] [reason=callee.contract] (relies on the contract of next (no definition; mark it [[cppverify::trusted]] to assume it), which is not established)

In the same way, a spec whose termination is proved in Lean is defined only
once that proof is certified: until then, and when it fails, every proof that
uses the spec's definition is ``Unresolved`` with reason ``spec.termination``.
A function proved by Lean, or by Z3 and Lean together, establishes its
contract for its callers, and its result carries the qualifiers a verified
one does (``[trusts=f]``, ``[partial]``). It also gets the same vacuity
checks, run with Z3: a goal that holds only because no execution reaches it
is ``Certified: f [backend=Lean] [vacuous]``, with a warning.

Counterexamples in Lean
~~~~~~~~~~~~~~~~~~~~~~~

A counterexample the solver finds is a failure once the certifier has
evaluated the program's goal at it, with every spec at its true definition. A
fallback project shows each such failure false in Lean as well: its
refutation, ``CppVerify/Refutations/<function>/<goal>.lean``, states the
failing goal as the project would and proves it false at the values the
model gives its variables, machine integers as bit-vectors, memory as a
function of its runs of equal cells. ``--lean-certify`` checks it as it
checks a proof, with the kernel and Lean's foundations alone, and says so:

.. cppverify-example: flags --lean-fallback={dir}/proof --lean-certify

.. code-block:: cpp

   int add_one(int x)
     cppverify::pre(x == 4)
     cppverify::post(cppverify::result == x + 1)
   {
     return x + 2;
   }

.. code-block:: text

   example.cpp:3:37: error: verification failed: add_one [postcondition] [backend=z3] [reason=counterexample] (confirmed in Lean)
       3 |   cppverify::post(cppverify::result == x + 1)
         |                   ~~~~~~~~~~~~~~~~~~^~~~~~~~
   example.cpp:3:37: note: counterexample: x = 4, result = 6
   example.cpp:5:3: note: returns 6
       5 |   return x + 2;
         |   ^

The refutation applies the goal to the model's values and decides what is
left false, the definition instances the goal states with it, since they hold
of the spec functions Lean defines:

.. code-block:: lean4

   theorem cppverify_add_one_fc20c3_postcondition_8876761e_refuted : ¬ cppverify_add_one_fc20c3_postcondition_8876761e := by
     intro h
     have h₁ := h
       (fun (a : Int) => (0 : Int))
       (fun (a : Int) => (0 : Int))
       (BitVec.ofInt 32 (6))
       (BitVec.ofInt 32 (4))
     cppverify_refute h₁

``cppverify_refute`` decides the instance, or evaluates it first, the spec
functions that are Lean definitions (`Spec functions in Lean`_) by their
equations, a store to memory with ``grind``, since it relates two heaps at
every address, and a quantifier over a range of at most 4096 integers by
trying each one (a larger range is not decided: each integer is a level of
recursion, and a billion of them took Lean 58 GB).
A goal that applies a spec Lean leaves opaque, such as a ``cppverify::choose``,
cannot be decided there: the failure stands, and a warning says so (``the
counterexample of pick_one is not confirmed in Lean: Lean cannot decide the
goal at the counterexample``). Should Lean decide the goal true at the
values, the solver's counterexample and Lean would disagree about one goal;
the function is then ``Unresolved`` with reason
``backend.inconsistent-results``, as when two solvers disagree, never
``Failed``. Each attempt of ``cppverify_refute`` has the heartbeats of a step
of ``cppverify_auto``, so a goal Lean could decide only by trying a billion
integers is not decided rather than tried for hours. Only failures that stand
once every verdict is settled report their refutations: a counterexample
checked with a spec's postcondition that is not established is no failure
(``spec.post``), and nothing is said of its refutation. A refutation is the
project's, rewritten by every run and removed with its failure.

Goals as hypotheses
~~~~~~~~~~~~~~~~~~~

Next to each goal, its module states it as hypotheses and a
conclusion. Each hypothesis is an assumption the goal makes, named by where
it comes from, and a bridge from that form to the goal is proved in the same
file. For this file:

.. code-block:: cpp

   [[cppverify::trusted]] int next(int x)
     cppverify::pre(x < 100)
     cppverify::post(cppverify::result == x + 1);

   int twice(int x)
     cppverify::pre(x >= 0 && x < 50)
     cppverify::post(cppverify::result == x + 2)
   {
     int a = next(x);
     int b = next(a);
     return b;
   }

the postcondition of ``twice`` reads:

.. code-block:: lean4

   def cppverify_twice_edf933_postcondition_28de726e.readable : Prop :=
     ∀
       (__heap_alloc_0 : CppHeap)
       (__heap_live_0 : CppHeap)
       (__local_call_1_1 : BitVec 32)
       (__local_call_2_1 : BitVec 32)
       (__result_1 : BitVec 32)
       (a_1 : BitVec 32)
       (b_1 : BitVec 32)
       (x_0 : BitVec 32),
       (h_pre_1 : (cppBvSle (BitVec.ofInt 32 (0)) x_0) ∧ (cppBvSlt x_0 (BitVec.ofInt 32 (50)))) →
       (h_null_1 : (heapSelectInt __heap_alloc_0 (0 : Int)) = (0 : Int)) →
       (h_null_2 : ¬(heapSelectBool __heap_live_0 (0 : Int))) →
       (h_call_next_1 : ((x_0).toInt + (1 : Int) ≥ (-2147483648 : Int) ∧ (x_0).toInt + (1 : Int) ≤ (2147483647 : Int)) ∧ __local_call_1_1 = x_0 + (BitVec.ofInt 32 (1))) →
       (h_a_1 : a_1 = __local_call_1_1) →
       (h_call_next_2 : ((a_1).toInt + (1 : Int) ≥ (-2147483648 : Int) ∧ (a_1).toInt + (1 : Int) ≤ (2147483647 : Int)) ∧ __local_call_2_1 = a_1 + (BitVec.ofInt 32 (1))) →
       (h_b_1 : b_1 = __local_call_2_1) →
       (h_result_1 : __result_1 = b_1) →
       ((x_0).toInt + (2 : Int) ≥ (-2147483648 : Int) ∧ (x_0).toInt + (2 : Int) ≤ (2147483647 : Int)) ∧ __result_1 = x_0 + (BitVec.ofInt 32 (2))

The names say where each assumption comes from:

- ``h_pre_<n>``: a precondition the function states; ``h_entry_<n>``: one
  the verifier adds, such as an extent's; ``h_null_<n>`` and
  ``h_object_<n>``: the null object and where an object lies;
- ``h_<variable>``: the definition of that variable, here ``a_1`` and
  ``b_1`` and the value returned, ``__result_1``;
- ``h_call_<callee>_<n>``: what a call of the callee gives, numbered in
  order, here both calls of ``next``;
- ``h_inv_<n>``, ``h_cond_<n>``, ``h_exit_<n>``: a loop's invariant, the
  condition of an iteration, and how it ended;
- ``h_exact_<n>``: the exact value of a machine operation that does not
  overflow; ``h_keep_<n>``: the value of a variable on a path that skips its
  assignment;
- ``h_check_<n>``: a ``cppverify::check`` proved before;
  ``h_spec_<spec>_<n>``: a spec's proved postcondition at an application;
- in a goal that checks a contract is defined (``contract of f``),
  ``h_pre_<n>`` and ``h_post_<n>``: the clauses before the one checked, each
  shown defined first; ``h_ret_<n>``: what holds of the state a function
  without a verified body may return in, its frame and its result.

The numbers count within the goal, so a line added to the source renames no
hypothesis. A disjunction the program wrote, such as
``cppverify::post(!(x > 0) || cppverify::result > 0)``, stays in the
conclusion. The bridge,
``cppverify_twice_edf933_postcondition_28de726e.of_readable``, proves the goal
from this form; Lean checks it when it builds the generated file, so a
readable form that said less than its goal would fail there, not certify. A
stub, the file of a goal ``cppverify_auto`` does not prove (and of every goal
with ``--no-lean-auto``), starts from it, with every name introduced:

.. code-block:: lean4

   import CppVerify.User
   import CppVerify.Auto

   theorem cppverify_twice_edf933_postcondition_28de726e_proof : cppverify_twice_edf933_postcondition_28de726e := by
     apply cppverify_twice_edf933_postcondition_28de726e.of_readable
     intro __heap_alloc_0 __heap_live_0 __local_call_1_1 __local_call_2_1 __result_1 a_1 b_1 x_0 h_pre_1 h_null_1 h_null_2 h_call_next_1 h_a_1 h_call_next_2 h_b_1 h_result_1
     sorry

and a proof uses the hypotheses by name:

.. code-block:: lean4

     obtain ⟨_, first⟩ := h_call_next_1
     obtain ⟨_, second⟩ := h_call_next_2
     subst h_result_1 h_b_1 second h_a_1 first
     simp only [cppBvSle, cppBvSlt, BitVec.sle, BitVec.slt, decide_eq_true_eq] at h_pre_1
     have : (BitVec.ofInt 32 0).toInt = 0 := rfl
     have : (BitVec.ofInt 32 50).toInt = 50 := rfl
     refine ⟨by omega, ?_⟩
     rw [BitVec.add_assoc]
     rfl

``cppverify_auto`` proves all four goals of ``twice`` itself. With its
proofs, or with proofs by hand like this one,
``cpp-verify --backend=lean --lean-project=proof --lean-certify file.cpp``
prints:

.. code-block:: text

   file.cpp:1:28: Trusted: next (contract assumed, not verified)
   Certified: twice [backend=Lean] [trusts=next]

A proof of the goal itself, as the one for ``small`` above, checks as well.

Spec functions in Lean
~~~~~~~~~~~~~~~~~~~~~~

A spec function that a goal applies is a Lean definition when Lean proves
that it terminates, and opaque otherwise, when a goal knows it only through
the definition instances it states. For this file:

.. cppverify-example: flags --backend=lean --lean-project={dir}/proof

.. code-block:: cpp

   cppverify::spec int tri(int n)
     cppverify::decreases(n)
   {
     return n <= 0 ? 0 : tri(n - 1) + n;
   }

   cppverify::proof void tri_nonneg(int n)
     cppverify::post(tri(n) >= 0)
   {
   }

   cppverify::proof void tri_four()
     cppverify::post(tri(4) == 10)
   {
   }

``cpp-verify --backend=lean --lean-project=proof file.cpp`` prints:

.. code-block:: text

   Exported: decreases: tri (cppverify_auto proved 1 of 1 goals)
   Exported: lean obligation: tri_nonneg (cppverify_auto proved 1 of 2 goals)
   Exported: lean obligation: tri_four (cppverify_auto proved 2 of 2 goals)

and ``Specs.lean`` defines ``tri`` by its body:

.. code-block:: lean4

   def cppSpec_fn_5f5a3374726969 (n : Int) : Int :=
     if _h : n ≤ (0 : Int) then (0 : Int) else (cppSpec_fn_5f5a3374726969 (n - (1 : Int))) + n
   termination_by ((n) + 1).toNat
   decreasing_by all_goals cppverify_decreasing

The definition is the spec's body, with each condition that reaches a
recursive application a hypothesis there, ``if _h : c`` (a ``&&``, ``||``,
or bounded ``cppverify::exists`` whose later part applies the recursion
becomes such an ``if``), so that Lean can prove the decrease from it. Its
measure is its ``cppverify::decreases``, each ``m`` as ``(m + 1).toNat`` and
lexicographic over several: exactly the relation cpp-verify's termination
check proves, where a call's measure may be -1 below a caller's 0. Specs
that apply each other are one ``mutual`` block. The body is never guarded by
the measure as a whole, so the definition has the spec's value at every
argument.

Lean proves each decrease with ``cppverify_decreasing``, a prelude tactic:
``omega``, after unfolding the comparison and collection wrappers, or the
division and remainder of a measure that falls by a constant divisor
(``log2(n / 2)``), then ``simp_all`` and Lean's own ``decreasing_tactic``.

The export tries the definitions with the pinned Lean. One that Lean rejects
stays opaque, as when the decrease rests on another spec's postcondition,
and one that applies it is tried again against that opaque declaration.
Lean's verdict on each is kept in ``.cppverify/specs``, so a later export
tries nothing; without Lean every spec is opaque.

The goals are the same either way, since they state the same definition
instances. With the definition, ``cppverify_auto`` evaluates ``tri(4)``
(``cppverify_auto_eval``, below), and a proof may unfold ``tri`` or argue by
induction over its recursion, with the principle Lean generates for it:

.. code-block:: lean4

   theorem tri_nonneg (m : Int) : 0 ≤ cppSpec_fn_5f5a3374726969 m := by
     induction m using cppSpec_fn_5f5a3374726969.induct with
     | case1 x h => rw [cppSpec_fn_5f5a3374726969]; simp [h]
     | case2 x h ih => rw [cppSpec_fn_5f5a3374726969]; simp [h]; omega

   theorem cppverify_tri_nonneg_42a030_postcondition_053b1980_proof :
       cppverify_tri_nonneg_42a030_postcondition_053b1980 := by
     apply cppverify_tri_nonneg_42a030_postcondition_053b1980.of_readable
     intro _ _ n _ _ _
     exact tri_nonneg _

With that proof, ``--lean-certify`` prints ``Certified`` for ``tri``,
``tri_nonneg``, and ``tri_four``. A verdict still rests on the termination
cpp-verify itself establishes: a spec whose own check is unresolved leaves
the goals that rely on it ``spec.termination``, whatever Lean defines.

Collections in Lean
~~~~~~~~~~~~~~~~~~~

The spec collections of ``<cppverify.h>`` reach Lean as values of core Lean
types, and each operation is a function of the generated prelude, total as
``<cppverify.h>`` defines it:

.. list-table::
   :header-rows: 1

   * - C++
     - Lean
     - Operations
   * - ``seq``
     - ``List Int``
     - ``cppSeqEmpty``, ``cppSeqUnit``, ``cppSeqLength``, ``cppSeqAt`` (0
       outside the sequence), ``cppSeqPush``, ``cppSeqConcat``,
       ``cppSeqSubrange`` (bounds clamped), ``cppSeqContains``
   * - ``set``
     - ``Int → Bool``, its membership test
     - ``cppSetEmpty``, ``cppSetInsert``, ``cppSetRemove``,
       ``cppSetContains``, ``cppSetUnion``, ``cppSetIntersect``,
       ``cppSetDifference``, ``cppSetSubset``
   * - ``multiset``
     - ``Int → Nat``, its counts
     - ``cppMultisetEmpty``, ``cppMultisetInsert``, ``cppMultisetRemove``,
       ``cppMultisetCount``
   * - ``map``
     - ``Int → Option Int``, the value at each key it holds
     - ``cppMapEmpty``, ``cppMapInsert``, ``cppMapRemove``,
       ``cppMapContains``, ``cppMapGet`` (0 outside the domain)

A set is its membership test, not a finite set, since a set of
``<cppverify.h>`` may hold infinitely many integers; ``decide`` still
evaluates a membership of a set built from constants, as it evaluates a read
of a list. ``update`` and ``reverse`` are specs over these operations, as for
the solvers.

The prelude also states what each operation means, in lemmas that ``simp``
and ``grind`` use: ``cppSeqAt_push`` (``s.push(x)[i]`` is ``x`` at
``s.len()`` and ``s[i]`` elsewhere), ``cppSeqAt_concat``,
``cppSeqAt_subrange``, ``cppSeqLength_push``, ``cppSeqContains_push``,
``cppSeqSubrange_push`` (the subrange that drops a pushed element is the
sequence), ``cppSetContains_insert``, ``cppMultisetCount_remove``,
``cppMapGet_insert``, and the others for each operation. Two collections are
equal when they agree everywhere: ``cppSeq_ext`` (equal lengths and reads),
``cppSet_ext``, ``cppMultiset_ext``, and ``cppMap_ext``. For this file:

.. cppverify-example: flags --backend=lean --lean-project={dir}/proof

.. code-block:: cpp

   using cppverify::seq;

   cppverify::spec int total(seq s)
     cppverify::decreases(s.len())
   {
     return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
   }

   cppverify::proof void last(seq s, int x)
   {
     cppverify::check(s.push(x)[s.len()] == x);
     cppverify::check(s.push(x).subrange(0, s.len()) == s);
   }

   cppverify::proof void total_push(seq s, int x)
     cppverify::post(total(s.push(x)) == total(s) + x)
   {
   }

``cpp-verify --backend=lean --lean-project=proof file.cpp`` prints:

.. code-block:: text

   Exported: decreases: total (cppverify_auto proved 1 of 1 goals)
   Exported: lean obligation: last (cppverify_auto proved 3 of 3 goals)
   Exported: lean obligation: total_push (cppverify_auto proved 2 of 2 goals)

The postcondition of ``total_push`` needs the definition of ``total`` at
``s.push(x)``, which its goal states as the hypothesis
``cppverify_spec_axiom_1_1``; ``cppverify_auto`` unfolds it
(``cppverify_auto_unfold``, below), and the lemmas about ``push`` and
``subrange`` finish it. A proof by hand uses the same lemmas:

.. code-block:: lean4

   theorem cppverify_total_push_cdfd2d_postcondition_3a9fac6f_proof :
       cppverify_total_push_cdfd2d_postcondition_3a9fac6f := by
     apply cppverify_total_push_cdfd2d_postcondition_3a9fac6f.of_readable
     intro _ _ s x pushed _ _ _
     rw [pushed]
     unfold cppSpecBody_cdfd2da1_fn_5f5a35746f74616c4e396370707665726966793373657145_1
     have := cppSeqLength_nonneg s
     simp [BitVec.toInt_signExtend_of_le]
     omega

Either way, ``--lean-certify`` prints ``Certified`` for ``total``, ``last``,
and ``total_push``. ``total`` is a definition (`Spec functions in Lean`_), so
a goal that needs induction over it, as ``total(s + t) == total(s) +
total(t)`` does, takes a proof by induction over ``total``'s recursion.

Proofs cppverify_auto finds
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each new goal is first given to ``cppverify_auto``, a tactic the project
carries in ``CppVerify/Auto.lean``, with the pinned Lean if it is installed.
For this file:

.. cppverify-example: flags --backend=lean --lean-project={dir}/proof

.. code-block:: cpp

   int next(int x)
     cppverify::pre(x >= 0 && x < 100)
     cppverify::post(cppverify::result == x + 1)
   {
     return x + 1;
   }

   int square(int x)
     cppverify::pre(x >= 0 && x < 1000)
     cppverify::post(cppverify::result >= 0)
   {
     return x * x;
   }

``cpp-verify --backend=lean --lean-project=proof file.cpp`` prints:

.. code-block:: text

   Exported: lean obligation: next (cppverify_auto proved 3 of 3 goals)
   Exported: lean obligation: square (cppverify_auto proved 1 of 3 goals)

A goal it proves gets that proof, with a header that says so:

.. code-block:: lean4

      automation: cppverify_auto 3 proves it with cppverify_auto_grind
      cppverify_auto proves this goal. cpp-verify rewrites this file only while it
      is unedited; a proof you write here is yours, kept as any other. -/
   import CppVerify.Goals.cppverify_next_e1e917
   import CppVerify.User
   import CppVerify.Auto

   theorem cppverify_next_e1e917_postcondition_506f384e_proof : cppverify_next_e1e917_postcondition_506f384e := by
     apply cppverify_next_e1e917_postcondition_506f384e.of_readable
     intro __heap_alloc_0 __heap_live_0 __result_1 x_0 h_pre_1 h_null_1 h_null_2 h_exact_1 h_exact_2 h_result_1
     cppverify_auto_grind

Any other goal gets a stub, whose header says it was tried
(``automation: cppverify_auto 3 did not prove it``). Here those are the two
goals of ``square`` that need ``x * x`` bounded: nonlinear arithmetic, which
core Lean does not decide. Certification checks the automatic proofs like any
other, so ``--lean-certify`` prints ``Certified: next [backend=Lean]``, and
``square`` stays ``Unresolved`` until its two stubs are proved.

``cppverify_auto`` tries these steps in order, each with a budget of 50000
heartbeats of its own (``set_option cppverify.autoBudget``), and keeps the
first that proves the goal:

- ``cppverify_auto_grind``: ``grind``;
- ``cppverify_auto_heap``: every store of memory is turned into the function
  it defines, then as below;
- ``cppverify_auto_bv``: machine comparisons, constants, and overflow
  conditions are stated as facts about integers, then ``grind``;
- ``cppverify_auto_decide``: ``decide``;
- ``cppverify_auto_simp``: ``simp_all``;
- ``cppverify_auto_bveq``: equalities of machine values, such as the
  precondition ``x != y`` of two keys, and sign extensions are stated as
  facts about integers too, then as ``cppverify_auto_bv``;
- ``cppverify_auto_ext``: an equality of two collections, element by
  element (`Collections in Lean`_), then as ``cppverify_auto_bv``;
- ``cppverify_auto_unfold``: each definition instance the goal states, by
  the body it names, then as ``cppverify_auto_bveq``;
- ``cppverify_auto_eval``: the spec functions that are Lean definitions
  (`Spec functions in Lean`_), by their equations, and the division and
  remainder of contracts and specs by their definitions, so that an
  application at known arguments becomes its value;
- ``cppverify_auto_div``: the division and remainder of contracts and specs
  by their definitions, then ``grind``, which decides them by a constant
  divisor once their signs are split (``a / 2 >= 2`` for ``a >= 4``).

A step counts only when it proves the goal with Lean's foundations alone, so
an unfinished lemma of yours (proved by ``sorry``) never proves a goal, and a
goal counts as proved only when the kernel accepted its proof. A goal it
spends more than 20 seconds on, its kernel check included, gets a stub
(``did not prove it within 20 s``; ``--lean-auto-timeout`` sets the limit).
The steps and their order were chosen by trying candidates on every goal the
test suite exports: of the goals Z3 proves, ``cppverify_auto`` proves 93%;
most of the rest need nonlinear arithmetic, induction over a spec, or a
quantified frame.

A goal is tried once: a later export tries a stub again only if a later
release of cpp-verify brings a new revision of ``cppverify_auto`` (the ``3``
in the header), and never once you edit it. Revisions 2 and 3 added the last
five steps, after the others, so that a goal an earlier step proves keeps its
proof; a stub that an earlier revision wrote is tried again. You can help it: a lemma in
``User.lean`` tagged ``@[grind]`` or ``@[simp]`` is used by its steps, since
the proof files import ``User.lean``; delete a stub to have it tried again.
Your own proofs may use ``cppverify_auto``, any of its steps, and the parts
they are made of (``cppverify_norm``, ``cppverify_heap``). What it writes is not taken on trust: a file it
calls proved is still certified like any other, and a ``User.lean`` that
fooled it would only change what the file holds. ``--no-lean-auto`` writes
stubs only.

Proofs that follow their goals
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A goal is named by its function and its statement, never by its position:
``cppverify_small_74ff94_precondition_4e324fa2`` is the ``precondition``
obligation of ``small``, ``74ff94`` from the function's identity (which tells
overloads apart), and ``4e324fa2`` the first digits of the hash of what the
goal states, with the definitions it uses. A goal identical to another of
its function gets ``_2``. Its proof lives in a directory per function,
``CppVerify/Proofs/cppverify_small_74ff94/``, and starts with a header that
records the goal, the obligation, and the full hash. Reordering clauses or
adding functions changes no statement, so every proof stays where it is.

Each run puts every proof with the goal of its statement. Renaming ``small``
of the example above to ``tiny`` moves the proof written by hand, with the
names it uses; the automatic proofs are simply written again for the new
goals, and everything certifies again:

.. code-block:: text

   Certified: nonnegative [backend=Lean]
   Certified: tiny [backend=Lean]
   warning: the Lean proof of fn_5f5a3474696e7976::precondition@9:3 moved from CppVerify/Proofs/cppverify_small_74ff94/cppverify_small_74ff94_precondition_4e324fa2.lean to CppVerify/Proofs/cppverify_tiny_de8a22/cppverify_tiny_de8a22_precondition_4e324fa2.lean, the file of the goal with its statement

A changed statement never gets the old proof. With ``nonnegative(4)`` in
place of ``nonnegative(3)``, the precondition's goal is a new one, which
``cppverify_auto`` proves, and the old proof is kept:

.. code-block:: text

   Exported: lean obligation: nonnegative (cppverify_auto proved 1 of 1 goals)
   Exported: lean obligation: tiny (cppverify_auto proved 3 of 3 goals)
   warning: the Lean proof CppVerify/Proofs/cppverify_tiny_de8a22/cppverify_tiny_de8a22_precondition_4e324fa2.lean is kept in Stale/Proofs/cppverify_tiny_de8a22/cppverify_tiny_de8a22_precondition_4e324fa2.lean: the statement of fn_5f5a3474696e7976::precondition@9:3 changed; its goal is now cppverify_tiny_de8a22_precondition_2596f63f

The kept file ends with that note. The proof comes back by itself once a goal
has its statement again, as it would if the call were ``nonnegative(3)``
again, and so do the proofs of a function that is removed and later
restored. A file nobody edited, a stub or an automatic proof, is simply
removed. Nothing else is ever deleted: ``--lean-prune-stale`` deletes what ``Stale/`` keeps, once the run
has taken back what it needs (``warning: removed the 4 Lean proofs kept in
Stale/, as --lean-prune-stale asks``).

A project 0.1 generated, with its ``Proofs/Goal_*.lean`` files, moves to these
names the next time cpp-verify writes it: each proof moves to the file of its
goal, with the goal and the spec definitions it names renamed, and a warning
such as ``warning: the Lean proof CppVerify/Proofs/Goal_b054b023e3576f6e.lean
that cpp-verify 0.1 wrote for fn_5f5a3373697876::postcondition@8:37 is now
CppVerify/Proofs/cppverify_six_6a2cf3/cppverify_six_6a2cf3_postcondition_198bc076.lean``.
A 0.1 proof of a goal the source no longer has is kept in ``Stale/``.

One module of goals per function
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each function's goals have a Lean module of their own, so that a change to
one function builds again only what depends on it. For this file:

.. cppverify-example: flags --backend=lean --lean-project={dir}/proof

.. code-block:: cpp

   cppverify::spec int tri(int n)
     cppverify::decreases(n)
   {
     return n <= 0 ? 0 : tri(n - 1) + n;
   }

   int inc(int x)
     cppverify::pre(0 <= x && x < 1000)
     cppverify::post(cppverify::result == x + 1)
   {
     return x + 1;
   }

   int tri_zero()
     cppverify::post(cppverify::result == tri(0))
   {
     return 0;
   }

``cpp-verify --backend=lean --lean-project=proof file.cpp`` prints:

.. code-block:: text

   Exported: decreases: tri (cppverify_auto proved 1 of 1 goals)
   Exported: lean obligation: inc (cppverify_auto proved 3 of 3 goals)
   Exported: lean obligation: tri_zero (cppverify_auto proved 2 of 2 goals)

and writes:

.. code-block:: text

   proof/
     lakefile.toml
     lean-toolchain
     CppVerify.lean           the library's root, which imports Check
     CppVerify/
       Prelude.lean           the heap model, the comparisons, the bridge lemmas
       Specs.lean             each spec the goals apply, declared once
       Goals/
         cppverify_tri_decreases_f55d4c.lean
         cppverify_inc_c0810e.lean
         cppverify_tri_zero_e086e9.lean
       Generated.lean         imports every goal module
       Auto.lean              cppverify_auto
       User.lean              your lemmas, never rewritten
       Proofs/
         cppverify_inc_c0810e/
           cppverify_inc_c0810e_postcondition_e4ef4574.lean
           ...
       Check.lean             imports every proof

``Specs.lean`` declares each spec function the goals apply once, ``tri``
here, by its definition (`Spec functions in Lean`_). Each goal module imports
it and defines the bodies its goals unfold under its own prefix, as in
``cppSpecBody_e086e9ab_fn_5f5a3374726969_1``, so any goal modules can be
imported together. A proof imports its function's goals, your lemmas, and
the automation:

.. code-block:: lean4

   import CppVerify.Goals.cppverify_inc_c0810e
   import CppVerify.User
   import CppVerify.Auto

A new ``User.lean`` imports ``CppVerify.Specs``, so a lemma there may speak
of the specs and of the prelude; a lemma about one function's goals belongs
in a module of yours that imports that function's goals. A ``User.lean`` of
an earlier release imports ``CppVerify.Generated``, which still imports every
goal module: its proofs keep working, but each then depends on every goal.

A generated file is written only when its text changes, so exporting an
unchanged source writes nothing, and ``lake build`` or your editor builds
again only what a change reaches. Certification builds the generated
modules, ``User.lean``, and ``Auto.lean`` with Lake, then compiles each proof
file with admissions promoted to errors, unless nothing it is built from
changed since it last passed: its text and the compiled modules of the
project it imports. After a change to the postcondition of ``inc``, it
compiles again the goal module of ``inc``, ``Generated.lean``, and the three
proofs of ``inc``, and none of the others.

A run writes the goal module of each function it exports, and removes any
other: a function you delete takes its module with it, and so does a
function that a ``--lean-fallback`` run leaves to its solver, since
``Specs.lean`` then declares only what the exported functions apply. The
proofs of such a function stay where they are, and build again once its
goals are exported again.

What certification checks
~~~~~~~~~~~~~~~~~~~~~~~~~

``Certified`` holds against a proof author in bad faith, so it cannot rest on
anything the user's Lean source does. After the build, a checker that
cpp-verify ships runs on the compiled modules and elaborates none of the
user's source. For each goal:

- the kernel replays every declaration of every module of the project the
  proof imports, as ``leanchecker`` does, so nothing escaped the kernel; only
  the pinned toolchain's own modules are trusted, and they are imported once
  for all the goals, however many of their proofs import ``Lean``;
- no module may declare a name that an earlier one declares otherwise, and
  the goal modules come first, so a proof file that defines a goal of its
  own under the goal's name is rejected;
- the proof ``G_proof`` must be a theorem whose type is exactly the goal
  ``G`` that its function's goal module defines;
- the axioms it depends on, collected from the constants it uses, must be
  among ``propext``, ``Quot.sound``, and ``Classical.choice``;
- no declaration of ``User.lean`` may use ``sorry``: an admitted lemma there
  fails every goal.

Each function is certified on its own goals. For this file, where ``one``
claims a false postcondition:

.. cppverify-example: fails one

.. code-block:: cpp

   int fine()
     cppverify::post(cppverify::result == 1)
   {
     return 1;
   }

   int one()
     cppverify::post(cppverify::result == 2)
   {
     return 1;
   }

a ``User.lean`` that rewrites what a check file would print,

.. code-block:: lean4

   import CppVerify.Generated

   macro_rules
     | `(command| example : $_ := $_) => `(command| #eval pure ())
   macro_rules
     | `(command| #print axioms $_) => `(command| #eval IO.println "does not depend on any axioms")

with a proof of ``True`` for the postcondition of ``one`` and true proofs
for the rest, gives:

.. code-block:: text

   Certified: fine [backend=Lean]
   Unresolved: lean obligation: one (Lean certification failed: the proof of fn_5f5a336f6e6576::postcondition@8:37: cppverify_one_99bcee_postcondition_646d2761_proof proves True, not cppverify_one_99bcee_postcondition_646d2761)

A theorem of the goal added by a command with ``debug.skipKernelTC``, which
skips the kernel, is rejected at its replay (``the kernel rejects
CppVerify.Lemmas: while replaying declaration 'cheat': (kernel) declaration
type mismatch``), a proof file that defines a goal of its own under the
goal's name at its replay too (``...cppverify_one_99bcee_postcondition_646d2761 declares
cppverify_one_99bcee_postcondition_646d2761, which
CppVerify.Goals.cppverify_one_99bcee declares``), and a user axiom behind a lemma by its name (``depends on the
axiom escape, which is not one of Lean's foundations``).

Portable obligation archives
----------------------------

The canonical backend boundary can be persisted and replayed:

.. code-block:: bash

   cpp-verify --lower-only --obligation-out=goals.cpv file.cpp
   cpp-verify --obligation-in=goals.cpv --backend=z3
   cpp-verify --obligation-in=goals.cpv --backend=portfolio
   cpp-verify --obligation-in=goals.cpv --lower-only --dump-ir=3,4
   cpp-verify --obligation-in=goals.cpv --backend=lean --lean-out=goals.lean
   cpp-verify --obligation-in=goals.cpv --lean-project=proof --lean-certify

Each ``cppverify.obligation/5`` record uses stable wire tags, defensive bounds,
portable source points, and path-independent SHA-256 semantic hashes. Replay
revalidates every sort, expression, logical declaration, call signature,
feature declaration, and identity before backend dispatch. Multiple records may
be concatenated. Parsing has explicit depth/node/collection budgets and a
4096-bit integer-width ceiling; malformed terms, non-canonical payloads,
ill-scoped variables, and contradictory complete/ordered goals fail closed.
Different records may request different reveal fuel for one logical function,
but its shared parameter/result signature must remain compatible.

Replay proves each module's obligations alone. What a source verdict also
rests on is not archived: the callee and trusted contracts and spec facts it
uses, ``[partial]``, and the vacuity checks. Where the source run reports
``Verified``, replay therefore reports ``Proved obligations: f (dependencies
not checked in replay)``, with JSON status ``proved-obligations``. A
counterexample is checked against the definitions alone and is still a
failure. The archive section of :doc:`../../language/tooling` shows a source run
and its replay side by side.

Source-built and replayed records pass through the same conservative
canonicalizer before hashing and dispatch. It folds only trivial Boolean
structure and reflexive equality/inequality, removes transitively unreachable
logical declarations (a declaration reaches what its definition and its
termination measures apply), rebuilds exact ordered and complete queries plus feature
metadata, and revalidates. It does not rewrite arithmetic, quantifiers,
pointers, heaps, or assumptions. Canonicalization introduced semantic-hash
format v2; format v3 removed diagnostic obligation identities from the
preimage, and format v4 removes every obligation kind except ``unwinding``.
Schema v2 adds precise obligation kinds, and schema v3 each spec function's
termination measures and where each assumption of a goal comes from (what a
Lean project needs to define a spec and to name a goal's hypotheses); none
of these is hashed, and records of schemas v1 and v2 remain readable.

BMC source verification archives only the terminal module for each function.
Those records retain their exact explored unroll bound. Replay is fixed-bound
and uses BMC unwinding aggregation, so an incomplete frontier remains
``BoundedSafe(N)`` rather than rerunning the incremental source strategy. BMC
cannot be applied to an untransformed record because loop unrolling is a VCR
transformation that occurs before canonical obligation construction.
Failure-only ``cppverify::recommends`` checks are not archived, so bytes do not depend on
whether a prior solver run succeeded or failed.
The dependency-scoped proof cache is shared by direct verification and replay,
so identical canonical goals reuse proofs without trusting source paths or
diagnostic identities.

Archives in a Lean project
~~~~~~~~~~~~~~~~~~~~~~~~~~

``--lean-project`` with ``--obligation-in`` writes the archive's modules to a
Lean project as a source run writes its functions: each goal has the name,
module, and proof file the same obligation has from source, since both name
it by its statement, and the specs are the same Lean definitions. A proof
written for the source certifies the archive's goal. For the specs of
`Spec functions in Lean`_,

.. code-block:: bash

   cpp-verify --lower-only --obligation-out=goals.cpv file.cpp
   cpp-verify --obligation-in=goals.cpv --lean-project=replay

prints

.. code-block:: text

   Exported: lean obligation: tri.decreases (cppverify_auto proved 1 of 1 goals) [backend=lean] [semantic-hash=sha256:...]
   Exported: lean obligation: tri_nonneg (cppverify_auto proved 1 of 2 goals) [backend=lean] [semantic-hash=sha256:...]

and ``replay`` has the goals, ``Specs.lean``, and proof files of
``cpp-verify --backend=lean --lean-project=proof file.cpp``. With the proof of
``tri_nonneg`` by induction in its file, ``--lean-certify`` prints

.. code-block:: text

   Proved obligations: tri.decreases (dependencies not checked in replay) [backend=lean] [semantic-hash=sha256:...]
   Proved obligations: tri_nonneg (dependencies not checked in replay) [backend=lean] [semantic-hash=sha256:...]

As with a solver, replay checks each module alone, so a module whose goals
all certify has its obligations proved, never ``Certified``, which would
also say that what the verdict rests on is established. Automation, moving
and keeping proofs in ``Stale/``, ``--lean-prune-stale``, and ``--jobs`` work
as for a source project; ``--lean-fallback`` is for source verification
only.

A bounded record of BMC exports too, to a project or to the scratch-pad.
The goals of each bounded module say its bound:

.. code-block:: lean4

   /- function: count_up -/
   /- required logic: mathematical-integers, bit-vectors, pointers, heap-arrays -/
   /- bound: 3 loop iterations, by unrolling: these goals speak only of the
      executions within them, and an unwinding goal says that every loop
      ends within them -/

Its result is read as BMC reads one: every goal certified, its unwinding
goals included, proves the obligations, and every goal but some unwinding
goal certified is ``BoundedSafe``: no execution within the bound fails. Lean
proves goals and never refutes one, so a Lean ``BoundedSafe`` says that the
unwinding goals are not certified, not that they fail. For two loops
archived by ``cpp-verify --backend=bmc --unroll=3``,

.. cppverify-example: flags --backend=bmc --unroll=3

.. code-block:: cpp

   int sum_small(int n)
     cppverify::pre(0 <= n && n <= 2)
     cppverify::post(cppverify::result >= 0)
   {
     int s = 0;
     for (int i = 0; i < n; i = i + 1)
       s = s + i;
     return s;
   }

   int count_up(int n)
     cppverify::pre(0 <= n && n <= 1000)
     cppverify::post(cppverify::result == n)
   {
     int c = 0;
     while (c < n)
       c = c + 1;
     return c;
   }

``--lean-certify`` prints

.. code-block:: text

   Proved obligations: sum_small (dependencies not checked in replay) [backend=lean, bound=2] [semantic-hash=sha256:...]
   loops.cpp:16:3: BoundedSafe: count_up (every goal is certified but the unwinding: no execution within 3 loop iterations fails (the proof of fn_5f5a38636f756e745f757069::unwinding@16:3: ...)) [backend=lean, bound=3] [reason=bmc.incomplete-bound] [semantic-hash=sha256:...]

``count_up`` loops up to 1000 times, so its unwinding goal at the bound 3 is
false, as BMC finds (``BoundedSafe: count_up [backend=bmc, bound=3]``).

Modular function calls
----------------------

Functions with ``cppverify::pre`` / ``cppverify::post`` are verified **modularly**: the caller must prove the callee’s
precondition at the call site and may then assume its postcondition (and frame conditions) without
re-analyzing the callee body.

Simple call:

.. cppverify-example: fragment

.. code-block:: cpp

   int y = abs_val(x);

Chained calls in one expression are supported by lowering inner calls to temporaries first:

.. code-block:: cpp

   int inc(int x) cv::pre(x >= 0 && x < 100) cv::post(cv::result == x + 1) { return x + 1; }

   int twice(int x)
     cv::pre(x >= 0 && x < 98)
     cv::post(cv::result == x + 2)
   {
     return inc(inc(x));   // inner inc, then outer inc
   }

The converter emits ``VCallStmt`` for each exec or proof call site; passivization substitutes callee
contracts in order. A call to a proof function is therefore a modular contract call like an exec
call: its precondition is asserted and its postcondition assumed. Spec functions are inlined or
axiomatized. Neither spec nor proof functions are emitted at runtime.

Preconditions, ``cppverify::old(parameter)``, and a parameter named in a
postcondition all denote the argument's entry value, as in ACSL, even when the
callee reassigns its by-value parameter; the caller substitutes its argument.
A function that sets its parameter ``p`` to null and returns therefore does
not prove ``cppverify::post(p == nullptr)`` for a non-null argument.

A call changes the caller's heap only inside the callee's ``cppverify::modifies``
footprints, instantiated with the arguments: a cell (``p[i]``, ``p->field``)
or a range (``p[lo : n]``) is exactly those cells, and a region (``*p``) is
the object the argument addresses, its ``valid`` extent or else one object.
Every other cell keeps its value, and the postcondition then re-establishes
whatever the caller may rely on inside the footprints. Each footprint must
also lie within the caller's own ``cppverify::modifies``, read in the caller's entry
state: its cells must be cells the caller may write, whichever pointer reaches
them. A callee without ``cppverify::modifies`` whose body (or a callee of it) may write
is treated as writing the whole heap; a conservative body scan keeps the heap
for verified, acyclic read-only callees.
A function that allocates or deallocates storage is verified as a standalone
body. A call to it is supported only when it is an inferred fresh-owned scalar
factory (see "Returning fresh ownership" in :doc:`ch19-dynamic-storage`); a
call to a function that deallocates, or that has any other lifetime effect,
fails closed (``Unresolved`` with reason ``construct.unsupported``).

``valid(p, n)`` extents also cross calls as checked sub-slices. Passing an
argument to a ``valid(q, length)`` formal asserts that its ``length``
elements lie in one of the caller's objects: for ``p + offset``, a
nonnegative offset and length and ``offset + length <= n``. A copy, a choice,
or a pointer stepped in a loop is checked against the objects it may
address. Empty one-past slices,
exact-cell writes, ranges ``cppverify::modifies(q[lo : n])``, and whole-slice
``cppverify::modifies(*q)`` are supported; the call changes only the written cells of
the slice.

A caller-owned dynamic scalar may be passed in the other direction to a
verified, non-allocating executable callee. Its direct matching pointer
parameter may be compared or dereferenced, including a write authorized by
``cppverify::modifies(*p)``. The call substitutes the caller's lifetime identity into
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

Where verification stops: trusted contracts
-------------------------------------------

Modular verification proves each function against its callees' contracts.
At the edge of the program there are functions it cannot see into: a
library compiled elsewhere, a system call, a routine written in assembly.
Their contracts can only be assumed, and CppVerify assumes a contract only
when you say so, with the standard attribute syntax:

.. code-block:: cpp

   [[cppverify::trusted]] int clamp_byte(int v)
     cv::post(0 <= cv::result && cv::result <= 255);

   [[cppverify::trusted]] int read_sensor(int channel)
     cv::pre(channel >= 0 && channel < 4)
     cv::post(cv::result >= 0 && cv::result <= 1023)
   {
     return channel * 300;   // stands for hardware access
   }

   int sample(int c)
     cv::pre(c >= 0 && c < 4)
     cv::post(0 <= cv::result && cv::result <= 255)
   {
     int r = read_sensor(c);
     return clamp_byte(r);
   }

   int twice(int c)
     cv::pre(c >= 0 && c < 4)
     cv::post(0 <= cv::result && cv::result <= 510)
   {
     int a = sample(c);
     int b = sample(c);
     return a + b;
   }

``clamp_byte`` has no definition here; ``read_sensor`` has one, which is
compiled but not verified. Each reports ``Trusted: ... (contract assumed, not
verified)``, and every proof that relies on either names it, through any
number of verified callers:

.. code-block:: text

   trusted.cpp:1:28: Trusted: clamp_byte (contract assumed, not verified)
   trusted.cpp:4:28: Trusted: read_sensor (contract assumed, not verified)
   Verified: sample [backend=z3] [trusts=clamp_byte,read_sensor]
   Verified: twice [backend=z3] [trusts=clamp_byte,read_sensor]

The ``[trusts=...]`` list is the trusted computing base of that one proof:
the verdict is exactly as reliable as those contracts. Keep it short. A
trusted contract should state what the function guarantees and nothing more,
and a function whose body is in the verified subset should be verified
instead.

On a ``cppverify::proof`` function the mark makes an axiom: its postcondition is assumed
for every argument that meets its precondition. That is occasionally the
right tool, for a mathematical fact that the solver cannot prove and that
you would rather cite than prove. It is also the easiest way to make every
proof true, so an axiom that a call cannot satisfy is reported as
``[vacuous]`` (see :doc:`ch16-when-verification-fails`).

A contract with neither a definition nor the mark is not assumed: its callers
are ``Unresolved`` with reason ``callee.contract``, and a warning points at
the declaration. A forgotten definition therefore cannot silently turn into
an axiom.

Where the definition is in another file, verify the files together:
``cpp-verify src/a.cpp src/mathx.cpp -- -Iinclude``. The run settles the
contract a header declares against the verification of its definition, so
``a.cpp``'s callers of ``clamp100`` are verified when ``mathx.cpp``'s body
meets the contract, and ``Unresolved`` when it does not. A build that verifies each object
records them instead (``-fverify-contracts-out=FILE``) and checks the
records together at the end (``cpp-verify --check-contracts``). Mark a
header's declaration trusted only for a definition outside the program: on
the definition, which inherits the mark, the body is still verified.

The same boundary exists in other verifiers. Verus assumes the specification
of a function marked ``#[verifier::external_body]``. Frama-C assumes the
contract of a function without a body when it proves the callers. CppVerify
makes the assumption an explicit mark on the declaration and carries it into
every verdict that depends on it.

Z3 result discipline
--------------------

Passive SSA is lowered once into a typed, source-attributed
``ObligationModule``. Layer 3 dumps this exact module and all backends consume
it. It contains one complete counterexample query plus equivalent ordered
queries with deterministic internal IDs, a precise kind per obligation
(for example ``precondition``, ``overflow``, or ``bounds``),
source-anchored public IDs/ranges, original-name typed model metadata, and
guarded trace events. Display-only diagnostic metadata persists through
archives but is excluded from semantic hashes, including both positional and
source-anchored obligation IDs. With one job and no proof cache, the backend
submits the complete query first, then the ordered queries if it does not
settle the module. With more than one job (the default uses the available
physical cores) and more than one obligation, the ordered queries run beside
the complete query, and a proof by either interrupts the other. With a proof
cache, only the ordered queries run, since the cache holds proofs of single
obligations.
``unsat`` means verified. A ``sat`` model is reported as a counterexample only
once the certifier has checked it against the true definitions; otherwise the
function is ``Unresolved`` with a reason, such as
``counterexample.unchecked``. When the complete query ends ``unknown`` or with
an unchecked model, the ordered queries check the module-owned assertions
separately in source order, using only entry facts and assumptions that
precede each obligation. They do not rebuild a second VC. This helps
quantified heap programs without letting a later assumption prove an earlier
assertion. If they still cannot discharge every obligation, the function is
``Unresolved`` and is not certified unless the user opted into the Lean
fallback and its current project passes the admission-free kernel check.

Model extraction never uses Z3 model completion. Undetermined values and path
guards stay explicitly unknown. When a complete-query model makes a particular
ordered counterexample query true, CppVerify attributes the failure and its
trace to that narrow obligation rather than reporting an anonymous whole-query
counterexample.

Parallel verify + compile
-------------------------

.. code-block:: bash

   clang++ -std=c++17 -fverify-contracts -c module.cpp -o module.o

With ``-fverify-contracts``, the contract constructs parse as part of the language. Unless you pass
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

``cppverify::recommends`` and soft checks
-----------------------------------------

``cppverify::recommends`` on spec functions is optional advice. If verification **fails**, the tool may
report that a ``cppverify::recommends`` clause at a call site was not implied by the caller’s precondition —
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

Next: :doc:`ch18-undefined-behavior` for proving freedom from undefined behavior.