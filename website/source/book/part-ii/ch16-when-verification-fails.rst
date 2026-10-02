Chapter 16 — When verification fails
====================================

A failed proof means the verifier found inputs or paths that break your stated properties—treat
that as actionable feedback on the code, the contracts, or both.

Understanding the report
------------------------

Diagnostics name the source-anchored obligation that failed and often include a
**counterexample**: typed source-name values that violate the claim, followed by
guarded branch, call, loop, heap/provenance, lifetime, and return events. Use
those values and events to see which assumption or branch is wrong. Values that
Z3 does not determine remain ``<unknown>``; CppVerify does not complete the
model by inventing them.

For editor, CI, and agent integration, run:

.. code-block:: bash

   cpp-verify --diagnostics-format=json file.cpp

Each verification result is one ``cppverify.diagnostic/1`` JSON object with a
stable reason code, backend and optional BMC bound, inclusive source range,
obligation ID/kind, typed model values, and trace. An unknown model value is
JSON ``null``. An undetermined path guard is ``"active": null`` rather than an
arbitrary branch choice. Command-line and frontend parse errors may still be
text, and IR dumps intentionally make the stream mixed. Malformed display bytes
are replaced with the Unicode replacement character, so JSON output remains
valid UTF-8.

``unknown`` is different from a counterexample. It means Z3 timed out, exhausted
an explicit resource/query budget, or entered a fragment it could not decide,
often because the VC combines bounded
quantifiers with heap arrays. CppVerify may retry smaller ordered obligations,
but if those also remain unknown it reports the function as **not verified**.
It never treats solver uncertainty as success.

A recursive spec applied beyond its unfolding fuel, or a spec you ``hide``, is
an opaque value that a solver model may choose freely, so a model is a
counterexample only if it still fails under the spec's real definition.
CppVerify checks every model from every solver against the definitions. When
the check refutes it, CppVerify gives the solver the definition at the
disputed arguments and solves again, which can also prove the obligation. If
that does not settle the query, the result is not verified with reason
``spec.fuel`` rather than a counterexample. When the solver's counterexamples
need the spec at ever larger arguments, the message says no finite unfolding
settles it: that goal is an induction, and the fix is a lemma (see
:doc:`ch13-spec-and-proof-functions`). Otherwise raise ``reveal_with_fuel``,
bound the argument, or state a lemma. For a hidden spec the reason is
``spec.hidden``: the definition would settle the query, but ``hide`` keeps it
out of proofs, so reveal it or state a lemma. A model that cannot be checked
within the checker's limits is reported as ``counterexample.unchecked``: for
quantifiers, that is a body that multiplies or divides bound variables or
applies a spec to one. Nested quantifiers over linear terms and reads, such as
"every element has a larger one", are always checked.

Other results that are not counterexamples:

- ``solver.timeout`` with ``the function's time (--function-timeout) is
  spent``: every query of the function together used its budget (ten times
  ``--timeout`` by default), so the remaining ones did not start. Split the
  function, help it with lemmas or assertions, or raise
  ``--function-timeout`` (``0`` disables it).
- ``decreases.missing``: a loop has no termination measure. Give it
  ``decreases``, or ``decreases(*)`` to allow divergence, after which the
  function and its callers report ``Verified ... [partial]``: proved for the
  executions that terminate.
- ``callee.contract``: the proof relies on a callee contract that nothing
  establishes: the callee's own verification failed, or the callee has a
  contract but no definition. Fix the callee first; for a library function
  whose contract you accept, mark the declaration ``[[cppverify::trusted]]``.
- ``construct.unsupported``: the failed obligation stands for a construct the
  verifier does not model, so it says nothing about the program. The message
  names the construct, such as a pointer difference between two parameters'
  objects or a call that keeps a pointer to local storage.
- ``[trusts=f]`` on a verified result: the proof relies on the contract of
  ``f``, marked ``[[cppverify::trusted]]`` (see
  :doc:`ch17-backends-modular-calls`).
- ``[vacuous]`` on a verified result, with a warning: no execution reaches
  the claim. See the next section.
- ``(its precondition is assumed, not checked, at calls from unverified g)``
  on a verified result: ``g`` is not verified (it has no contract, assertion,
  ghost code, or loop contract), so nothing checks that it establishes the
  precondition when it calls. The proof holds for every call that does; give
  ``g`` a contract to have its calls checked (JSON ``unverified_callers``).

When a proof is too easy
------------------------

An implication with a false premise is true. If no execution can reach a
claim, the verifier proves the claim, whatever it says. That happens when an
assumption contradicts itself or the program:

.. code-block:: cpp

   int never(int x)
     pre(x > 0 && x < 0)       // no x satisfies this
     post(result == 42)
   {
     return 0;
   }

.. code-block:: text

   Verified: never [backend=z3] [vacuous]
   warning: never: the precondition is unsatisfiable, so every claim about it
     holds vacuously

``return 0`` "establishes" ``result == 42`` because no call can reach it. The
mark is there so that such a result is never read as a proof. Every
``Verified`` result is checked at the places an assumption can enter: the
preconditions and type invariants, each behavior's assumption, and each call
of a trusted contract, whose postcondition is assumed without proof:

.. code-block:: cpp

   [[cppverify::trusted]] int impossible(int x)
     post(result > x && result < x);

   int sometimes_calls(int x)
     pre(x >= 0 && x <= 10)
     post(result >= 0)
   {
     if (x == 3) {
       int y = impossible(x);   // no result satisfies the contract
       return -1;               // so this "satisfies" result >= 0
     }
     return x;
   }

.. code-block:: text

   vacuity.cpp:1:28: Trusted: impossible (contract assumed, not verified)
   Verified: sometimes_calls [backend=z3] [vacuous] [trusts=impossible]
   vacuity.cpp:9:5: warning: sometimes_calls: the trusted contract of
     impossible contradicts the state of this call, so everything after it
     holds vacuously

A behavior whose assumption no admitted input satisfies is reported too: its
postconditions are never checked.

.. code-block:: cpp

   int clipped(int x)
     pre(x >= 0 && x <= 10)
     behavior(small, x < 5)
       post(result == x)
     behavior(huge, x > 20)      // contradicts the precondition
       post(result == 1000)
     behavior(large, x >= 5)
       post(result == x)
     complete_behaviors
   {
     return x;
   }

.. code-block:: text

   Verified: clipped [backend=z3]
   vacuity.cpp:5:20: warning: clipped: behavior huge never applies: its
     assumption contradicts the preconditions, so its postconditions are
     never checked

Dead code alone is not flagged. A defensive branch such as ``if (p ==
nullptr) return -1;`` under ``pre(p != nullptr)`` is unreachable for a good
reason, and every claim of the function is still checked on the paths that
remain. Only an assumption that removes the paths a claim needs is a
problem, and those are exactly the places checked above: a verified callee
always returns, so ordinary calls cannot cut paths.

Quantifiers that run away
-------------------------

A query that times out with quantifiers in it is often a matching loop: each
instance of a quantifier creates a term that triggers another instance. Run
with ``--profile-quantifiers`` to see which quantifier the solver kept
instantiating:

.. code-block:: text

   note: the quantifier at 43:7 was instantiated 2914 times, up to generation 41

The fix is usually a better trigger. ``trigger(term)`` inside a quantifier body
makes ``term`` the pattern that instantiates it (see
:doc:`ch13-spec-and-proof-functions`); choose a term that the instance does not
recreate at a larger argument.

A requested proof cache is also fail-closed. ``cache.corrupt`` means an entry
did not exactly match its semantic/backend identity; ``cache.io-failed`` means a
requested entry could not be read. Neither is treated as a cache miss or a
proof. A post-proof write or pruning failure is instead explicit cache-error
telemetry and does not erase the fresh solver proof. Text diagnostics report
cache hits/queries, while JSON includes ``cache.hits``, ``cache.misses``, and
``cache.errors``.

For a deliberately invalid program, both outcomes are sound:

- ``error: verification failed`` means Z3 found a concrete model;
- ``unknown`` means the verifier conservatively refused to certify it;
- only ``Verified`` is a proof result.

``Lowered`` is not a fourth solver outcome. It is emitted only by
``cpp-verify --lower-only`` and says that Clang AST conversion, VCR, passive
SSA, canonical Obligation IR generation, and backend encoding succeeded without running
satisfiability. This is useful when isolating a frontend or lowering bug from a
slow quantified/heap query, but it never certifies the program.

``Exported`` is also not a proof result. A standalone Lean scratch-pad contains
``sorry``. An editable project separates generated semantics from preserved
user proofs, but its initial proof files are still admitted. Only
``--lean-certify`` compiling every active proof under the pinned toolchain,
with no ``sorry`` or undocumented proof axiom, reports ``Certified``.

For automation that remains unresolved, use:

.. code-block:: bash

   cpp-verify --lean-fallback=proof file.cpp
   # edit proof/CppVerify/User.lean and proof/CppVerify/Proofs/*.lean
   cpp-verify --lean-fallback=proof --lean-certify file.cpp

The first command remains non-success because export is not proof. It exports
only the obligations Z3 did not prove and reports the split, for example
``[z3: 18 of 20 proved; lean: 2 exported]``. Once those proofs kernel-check,
the function is ``Proved (z3+lean)``, never ``Verified`` or ``Certified``. A Z3
counterexample is not routed through this fallback.

Trusting a new feature
----------------------

Do not use one successful Z3 result as the only implementation oracle. A
feature regression should combine:

- realistic C++ programs that must verify;
- nearby false programs that must be rejected;
- exact VCR and passive-SSA checks;
- critical typed Obligation IR and Z3-encoding checks;
- boundary cases for mathematical integers and machine integers.

This split answers two independent questions. ``--lower-only`` checks whether
the program became the intended formula. Ordinary verification checks whether
that formula is valid. A timeout can block the second answer without hiding a
malformed first answer.

Proof failure versus unsupported C++
------------------------------------

A source program can also be outside CppVerify's current semantic subset. That
is different from a failed proof:

- a **conversion/unsupported error** means the relevant C++ semantics are not
  modeled and verification stopped fail-closed;
- **verification failed** means the semantics were lowered and a
  counterexample violates an obligation;
- **unknown** means the obligation was lowered but automation did not decide it.

Do not work around an unsupported diagnostic by replacing a C++ operation with
an unchecked integer or external axiom. Either reformulate the program within
the documented subset or add the missing semantics through Clang, VCR,
passivization, backend encoding, and positive/false-proof tests.

The full feature matrix, memory/object-model boundaries, missing induction and
solver tactics, performance work, library models, and raw-C++ readiness gates
are maintained in :doc:`../../language/limitations`.

Adjusting contracts
-------------------

.. list-table::
   :header-rows: 1
   :widths: 32 68

   * - Situation
     - Response
   * - Precondition too weak
     - Strengthen ``pre`` so callers cannot supply bad inputs
   * - Postcondition too strong
     - Weaken ``post`` or fix the implementation
   * - Loop invariant too weak
     - Add facts to ``invariant`` so preservation holds
   * - Spec vs machine integers disagree
     - Use ``spec`` for mathematical integers; ``constexpr`` for machine semantics
   * - Recursive specification
     - Use the smallest sufficient ``reveal_with_fuel`` depth; after importing
       finite lemma facts, ``hide`` an irrelevant recursive definition to keep
       the VC tractable
   * - Pointer aliasing
     - Prove distinct pointers or declare ``aliases``
   * - Overflow / divide-by-zero
     - Add the precondition the counterexample points to (see :doc:`ch18-undefined-behavior`)
   * - Indexed access or pointer step is out of bounds (``bounds``)
     - Declare the correct ``valid(p, n)`` extent and prove the index lies in
       ``[0, n)``; a pointer without an extent addresses one object
   * - Heap fact disappears after a call
     - Give the callee a ``modifies`` with exact cells, a range
       ``p[lo : n]``, or a region; a pointer-taking callee without
       ``modifies`` forgets the whole heap
   * - Heap fact disappears after a loop
     - Add a loop ``modifies`` naming what the loop writes, read in each
       iteration (``a[0 : i]`` for a prefix)

Further reference: :doc:`../../language/index`.