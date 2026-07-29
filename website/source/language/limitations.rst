Current limitations and C++ readiness
=====================================

CppVerify faithfully verifies a documented, growing C++ subset and fails closed
outside it. It is strongest on integer programs, contracts, modular free
functions, loops/recursion, flat values, abstract buffers, and constrained
pointer lifetimes. It does **not** yet verify arbitrary existing C++.

This page separates four different situations:

.. list-table::
   :header-rows: 1
   :widths: 23 77

   * - Classification
     - Meaning
   * - **Supported**
     - The construct has defined verifier semantics plus positive and
       false-proof regressions.
   * - **Partial**
     - A documented fragment works; neighboring forms are rejected.
   * - **Trusted**
     - An interface contract is assumed because its body is unavailable, not
       proved by CppVerify.
   * - **Incomplete automation**
     - The semantics are represented soundly, but Z3 may need user lemmas or
       return ``unknown``.

Meaning of a result
-------------------

``Verified`` means the selected backend proved the generated verification
condition. It does not certify uncontracted functions, linked libraries, the
operating system, or any explicit external contract.

Distinct pointer/reference address parameters are **non-aliasing by default**
whenever at least one pointee or referent is mutable. CppVerify generates a
complete-object disjointness precondition. Verified callers must prove it;
unverified external callers must honor it like a written ``pre``.
``aliases(p, q)`` permits same-object aliasing.

``Lowered`` is emitted by ``--lower-only``. It means Clang AST conversion, VCR,
passive SSA, canonical obligation construction, and backend encoding succeeded
**without** a solver call. It is a translation check, not a proof.

``unknown`` means the solver did not establish the obligation, commonly because
of a timeout or difficult quantified heap formula. It is never treated as
success. Unsupported AST, type, storage, or encoding cases similarly produce
errors rather than proof-shaped defaults.

Current verified core
---------------------

The most mature current fragment includes:

- free functions over booleans, enums, and target-width integers;
- mathematical ``spec`` functions connected to machine-integer code;
- ``if``, conventional ``while``/``for``, loop invariants, and ``decreases``;
- direct recursion with a well-founded termination measure;
- ``pre``, ``post``, ``old``, ``result``, ``modifies``, and ``aliases``;
- scalar ``T&``/``const T&`` parameters with address-preserving reads, writes,
  contracts, and direct forwarding;
- proof functions, ghost code, bounded quantifiers, and controlled recursive
  unfolding;
- flat trivial standard-layout records with scalar fields;
- fixed local arrays and promoted trivial local records with nested record,
  pointer, and fixed-array members;
- one-level typed pointers, abstract indexed buffers, and heap framing;
- constrained direct scalar ``new``/``delete`` with liveness, initialization,
  and provenance.

C++ feature boundaries
----------------------

.. list-table::
   :header-rows: 1
   :widths: 22 32 46

   * - Area
     - Current fragment
     - Missing boundary
   * - Scalar types
     - ``bool``, integral types, and enums preserve target width and signedness.
     - Floating point, ``volatile``, and other non-integral scalar semantics.
   * - Pointers
     - One pointer level to supported complete objects. The type gate admits
       ``void*``, but no general erasure/ownership model is claimed.
     - Pointer-to-pointer, function pointers, type erasure/recovery, and general
       reinterpretation.
   * - References
     - Scalar ``T&``/``const T&`` parameters on contracted executable free
       functions, initialized ordinary scalar local actuals, local aliases for
       boolean, integral, and enum referents, and bindings to a field or fixed
       array element of a promoted local object.
     - Conditional bindings, reference returns, non-scalar referents, rvalue
       references, temporaries/lifetime extension, reference members, and
       forwarding.
   * - Arrays
     - Pointer-parameter indexing, quantified abstract buffers, and fixed
       local arrays (including arrays of records and multidimensional arrays)
       modelled as byte-addressed automatic objects up to 256 bytes.
     - Array parameters/fields carried by value, array references,
       ``new[]``/``delete[]``, loop-local arrays, and raw pointers derived from
       a local array.
   * - Records
     - Flat trivial standard-layout values with scalar fields; trivial
       standard-layout records with nested record, pointer, and fixed-array
       members as promoted local objects.
     - Non-trivial, inherited, polymorphic, union, and bit-field records, and
       nested/pointer/array-bearing records used by value.
   * - Functions
     - Free functions, overloads, namespaces, contracts, direct calls, and
       scalar-state direct recursion.
     - Member functions, templates, variadics, indirect calls, mutual
       recursion, heap-mutating executable recursion, and general link-time
       summaries.
   * - Storage
     - Supported locals, constrained scalar dynamic storage, and inferred
       acyclic fresh-owned scalar factory results.
     - Globals, static locals, thread-local storage, general returned
       allocations, and user-declared modular allocation effects.
   * - Structured control flow
     - ``if`` (including C++17 initializer), conventional ``while``/``for``,
       blocks, and ``return``.
     - ``switch``, ``do``, range-``for``, ``break``, ``continue``, ``goto``,
       labels, conditionless ``for``, and loop condition declarations.
   * - Advanced C++
     - Not in the verified core.
     - Exceptions, lambdas, coroutines, RTTI, virtual dispatch, multiple
       inheritance, inline assembly, concurrency, and atomics.

An unsupported syntax case is not considered implemented merely because Clang
can parse it. It also needs VCR semantics, C++ definedness rules, modular
effects, backend encoding, and false-proof coverage.

Objects, classes, and RAII
--------------------------

Flat records are currently value aggregates, not a general C++ object model.
CppVerify does not yet model:

- constructors, destructors, copy/move special members, or RAII cleanup;
- ``this`` and member-function cv/ref qualifiers;
- class invariants over aliased mutable objects;
- base subobjects, vtables, or virtual dispatch;
- temporary materialization and lifetime extension;
- exception cleanup and exactly-once destruction;
- placement construction, lifetime restart, or ``std::launder``.

Scalar parameter references, local scalar aliases, and scalar field/element
bindings into promoted local objects are addressable aliases. General aggregate
references, raw automatic pointers, temporary binding, and pointer-bearing
aggregates across modular interfaces remain prerequisites for idiomatic C++
classes, containers, and ownership types.

Pointers, buffers, and provenance
---------------------------------

Abstract pointer parameters
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Typed pointer arithmetic uses mathematical target-byte addresses: every ``T*``
step is multiplied by Clang's target ``sizeof(T)``, and fields use the target
record-layout byte offset. Supported code can reason about ``*p``, ``p[i]``,
``*(p + i)``, exact footprints such as ``modifies(p[i])``, and region
footprints such as ``modifies(*p)``.

With ``--check-ub``, a syntactically restricted ``valid(p, n)`` precondition
declares an abstract extent. It remains a caller promise rather than evidence
derived from a concrete caller allocation; it does not supply general lifetime,
alignment, provenance, or initialization. Bounds follow exact conditional and
short-circuit evaluation, and fresh represented storage is kept disjoint from
the complete declared incoming extent.

For pairs involving mutable pointees, CppVerify adds a generated
complete-object disjointness precondition. ``aliases(p, q)`` opts a pair into
same-object aliasing; it does not establish arbitrary partial overlap or create
provenance.

Scalar lvalue references and automatic locals
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contracted executable free functions may accept ``T&`` and ``const T&`` when
``T`` is ``bool``, integral, or enum. VCR retains the binding as an immutable
address: reading loads the referent, assignment stores through that address,
and ``old(ref)`` selects the entry heap. Every reference receives an implicit
non-null, live, and initialized precondition.

``modifies(ref)`` is an open region rooted at the referent, like
``modifies(*p)``. Default object-range disjointness and ``aliases`` apply across
pointer and reference parameters. A call may bind a reference from another
supported reference, an initialized ordinary scalar local, or a direct
dereference such as ``set(*p, value)``. Local references may bind those direct
forms and chain through other local aliases; a pointer-derived binding
snapshots the address.

Address-required scalar locals, fixed local arrays, and supported enclosing
records are promoted to one heap representation. They receive fresh automatic
lifetime identities, target size/alignment, byte ownership, liveness, and
per-leaf initialization. Fixed-array loads, stores, copies, and reference
bindings carry every nested bound at the access site. Automatic lifetimes end at
the lexical closing brace or on each early return, in reverse construction
order; heap-reading return values are materialized before teardown.

Scalar references may bind supported fields and fixed-array elements of these
promoted objects. Conditional bindings, temporaries, reference returns, general
raw address-taking/array decay, rvalue references, and non-scalar referents
remain fail-closed. Addressable declarations inside loops and ``old`` of local
objects/bindings are also rejected; outer automatic locals and loop-local aliases
are supported. Pointer leaves may retain abstract pointer values, but storing a
provenance-bearing local dynamic pointer fails closed until pointer provenance is
represented in a parallel heap.
The initialized-entry rule excludes output-only references to indeterminate
storage. Reference reads participate in the existing argument-order safety
check.

Local scalar dynamic storage
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A direct scalar ``new``/``delete`` additionally carries
SSA-versioned metadata for:

- owning lifetime identity;
- base, size, alignment, and liveness;
- byte ownership and initialization;
- a provenance companion for supported local pointer values.

Matching-type copies, reassignment, conditional selection, branch merges,
``nullptr``, deletion through a valid alias, constrained non-allocating modular
calls, and inferred fresh-owned scalar factory results are supported. A
body-present acyclic factory may return its sole live initialized allocation or
null; callers receive fresh metadata and may forward, mutate, or delete it.

Still rejected are uninitialized, freed, arithmetic-derived, multiply
allocated, secondarily escaped, external, recursive, indirect, or type-erased
ownership results; general ownership parameters; dynamic allocation in loops;
placement/nothrow allocation; non-scalar objects; ``new[]``; and allocation in
functions that also accept pointer parameters.

Pointer difference
~~~~~~~~~~~~~~~~~~

A bounded executable same-array pointer-difference fragment is supported:

- both operands have one matching complete pointee type;
- operands may contain compositional arithmetic rooted at one pointer;
- a ``valid(p, n)`` extent admits element positions in ``[0, n]``, including
  the one-past endpoint; without an extent, direct abstract and represented
  scalar-dynamic pointers retain only complete-object positions ``0`` and ``1``;
- abstract operands use one syntactic SSA base, or dynamic aliases carry one
  shared live lifetime identity;
- target-byte difference is divided by ``sizeof(T)`` and converted to target
  machine ``ptrdiff_t`` only after proving representability.

Stored or indirect positions whose root cannot be recovered, merely equal
abstract addresses, distinct allocations, null/dangling operands, out-of-range
positions, explicit ``spec`` bodies, and lifted ``constexpr`` specs fail closed.
Specs still need first-class ``(object origin, extent, element position)``
metadata that survives substitution, quantifiers, and recursion.

Missing low-level memory semantics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The verifier does not yet generally represent strict aliasing/effective type,
union punning, byte-wise object representation access, arbitrary pointer
alignment, placement lifetime restart, transparent replacement, or provenance
through pointer/integer casts. These require an object-and-storage model rather
than treating every address operation as plain integer arithmetic.

Modular calls and effects
-------------------------

Calls assert callee preconditions, apply declared effects, and assume
postconditions. Exact footprints such as ``modifies(p[i])`` and
``modifies(p->field)`` preserve other addresses. An open region
``modifies(*p)`` may conservatively forget the whole value heap at an abstract
call because its finite extent is unknown.

With ``--check-ub``, a callee ``valid(q, length)`` extent can be instantiated
from a caller ``valid(p, n)`` extent only after proving a same-root,
nonnegative subrange contained in ``[0, n]``. Empty one-past slices, transitive
read-only forwarding, and exact-cell slice writes are supported. Symbolic
writable-range summaries and unbounded region writes through a sub-slice remain
fail-closed.

Checked local dynamic identities can cross a narrow scalar call/return boundary
when the caller owns the identity. Body-derived fresh-owned returns additionally
transfer one initialized scalar allocation through acyclic in-translation-unit
factories; external contracts cannot claim this effect. Missing effect concepts
include general allocation/deallocation contracts, parameter ownership
transfer, escape sets, separate read footprints, global state, exceptional
cleanup, lock state, and concurrency interference.

External contracts are trusted interfaces. CppVerify checks callers against
their preconditions but cannot prove an unavailable implementation satisfies
its postconditions or frame.

Specifications, recursion, and induction
----------------------------------------

Recursive specs are termination-checked and fuel-controlled. Fuel exposes a
finite number of defining-equation steps and prevents uncontrolled SMT matching
loops.

Recursive ``proof`` functions with ``decreases`` already provide manual
well-founded induction: the recursive call is legal only at a smaller measure,
and its postcondition is the guarded induction hypothesis. Fuel and induction
have different jobs; increasing fuel is not a proof for all inputs.

Current proof-language limitations include:

- no first-class ``induction`` syntax generating explicit base/step obligations;
- no ``calc``-style equational chains or named rewrite sets;
- bounded quantifiers only, without user trigger syntax or trigger profiling;
- user-written loop invariants, with no candidate-invariant/Houdini pass;
- no automatic termination-measure or lemma discovery;
- no heap-reading mathematical specs or aggregate-returning specs;
- no mutual recursion for spec/proof/executable functions.
- no heap-mutating executable recursion: stores, allocation/deallocation, and
  separate heap-modifying calls fail the termination check conservatively.

These are mainly automation and usability limits. They do not permit an
unproved recursive property to become ``Verified``.

C++ definedness coverage
------------------------

Always-on obligations currently cover signed arithmetic overflow, invalid
division/remainder, invalid shifts, non-null/live represented dereferences,
supported local definite initialization, and local scalar dynamic lifetime
errors.

``--check-ub`` additionally adds the restricted ``valid(p, n)`` extent layer
for buffer accesses, modular sub-slices, and same-array pointer positions. It
is not yet comprehensive C++ undefined-behavior checking.

Missing general UB semantics include object provenance outside the represented
fragment, strict aliasing, arbitrary alignment, unsequenced side effects and
all unspecified evaluation-order alternatives, object lifetime restart,
exception unwinding, floating-point environment, volatile/atomics, and data
races.

Solver and automation limitations
---------------------------------

The Z3 backend supports bit-vectors, mathematical integers, arrays,
quantifiers, models, timeouts, module-owned ordered-obligation fallback, and
full SMT dumps. Layer 3 now provides deterministic obligation IDs and raw
source encodings from the exact canonical module solved by the backend.
Hard quantified recursive/heap formulas can still leave decidable fragments and
return ``unknown``.

Important missing optimizations and tactics are:

#. richer source-level obligation categories, VC slicing, and independent
   resource reports beyond the current IDs/raw source encodings;
#. a verifier-specific simplifier before SMT;
#. source-level path/heap/provenance counterexamples instead of raw SSA models;
#. content-addressed proof caching and affected-function invalidation;
#. parallel per-function solving in the standalone tool;
#. induction and ``calc`` proof ergonomics;
#. quantifier trigger inference, manual override, and profiling;
#. candidate invariants with Houdini-style elimination;
#. solver-resource stability measurement across seeds;
#. broader portfolio model extraction and optional CHC/PDR invariant discovery.

Candidate invariants, assertion batching, parallel solving, caching, and
trigger control are production-proven techniques in systems such as
Boogie/Dafny, Verus, Why3, and Frama-C. Fully automatic invariant/lemma
synthesis and heap CEGAR remain research-heavy.

Backend-specific boundaries
---------------------------

**BMC** incrementally explores finite loop bounds and is useful for shallow
counterexamples. An unwinding assertion prevents an insufficient maximum bound
from silently becoming an unbounded proof. Successful prefix queries are reused,
and numbered source loop events identify the failing iteration. Path explosion,
concurrency schedules, solver-state push/pop reuse, and broad runtime semantics
remain future work.

**cvc5 and strict portfolio** consume the same canonical obligations as Z3
through an independent SMT-LIB2 emitter. cvc5 is optional, system-installed,
and currently supplies verdicts rather than source-level models. Strict
portfolio mode requires matching decisive results and preserves Z3's model only
after both solvers report ``sat``. cvc5 may return ``unknown`` on quantified or
heap-heavy formulas that Z3 solves; strict mode then remains ``Unresolved``.
BMC-transformed archive replay still uses the Z3-backed BMC aggregator.

**Lean** consumes the same typed canonical obligation as Z3. Standalone export
is an unchecked scratch-pad and reports ``Exported``. Project mode emits
faithful definitions for the current integer, bit-vector, pointer, total-heap,
quantifier, overflow, and finite spec-fuel theories, plus one source-attributed
goal per ordered obligation. Generated files are separated from preserved user
lemmas/proofs. The pinned admission-free kernel path reports ``Certified`` only
after every active proof checks and rejects user axiom/opaque shortcuts.
``--check-ub`` buffer extents are lowered on this path as well as on
Z3/cvc5/portfolio/BMC.
Automation, proof ergonomics, semantic simplification, dependency-aware
caching, and broader future C++ theories remain incomplete.

The repository's backend release gate differentially checks all current
canonical feature families, decisive false goals, source IDs, deterministic
parallel results, canonical and BMC archive replay, Lean theorem/proof-module
identity, generated Lean compilation, and fail-closed solver processes. Valid
quantified or inductive goals may conservatively remain ``solver.unknown`` in
cvc5, but disagreement and false proof are never accepted.

There is currently no CHC backend, separation-logic backend, or independently
checked Z3 proof-object pipeline. Portfolio agreement is independent solver
evidence, not a portable proof certificate.

Portable obligation schema v1 bounds imported integer sorts to 4096 bits and
uses explicit parser depth/node/collection budgets. Supporting wider backend
sorts requires a deliberate schema/capability revision, not unbounded resource
allocation from an archive.

Libraries and real programs
---------------------------

CppVerify does not yet ship comprehensive libc or C++ standard-library models.
An uncontracted call fails closed; an explicit external contract is trusted.

Broader application verification needs:

- memory/string primitives such as ``memcpy``, ``memmove``, and ``memset``;
- mathematical sequence/set/map views for contracts;
- ``std::array``, ``std::span``, smart pointers, optionals, and string views;
- vectors, strings, associative containers, iterators, invalidation, and
  allocator effects;
- contracts for searching, copying, permutation, partition, and sorting.

Models should expose abstract values (for example, a container ``view()``)
rather than force each user to verify library internals. Trusted models also
need executable conformance and false-model tests.

Diagnostics and developer tooling
---------------------------------

Current diagnostics identify failed functions and often include a Z3 model.
Production readiness still needs:

- exact source ranges and stable IDs for each contract/frame/UB obligation;
- original variable names and entry/current values instead of SSA names;
- branch, call, loop, heap, lifetime, and provenance traces;
- useful ``unknown`` explanations and quantifier/unfolding statistics;
- JSON/SARIF, LSP/editor integration, and affected-function verification;
- reproducible proof-resource budgets and CI regression reports.

Assurance and testing gaps
--------------------------

Every current checkpoint uses positive programs, nearby false programs, and
layered lowering checks. Broader trust additionally requires:

- grammar-guided fuzzing of supported and neighboring unsupported C++;
- metamorphic and AST/VCR/SMT translation-validation tests;
- bounded differential execution against compiled Clang programs;
- X86-64/AArch64 target-layout and language-mode matrices;
- solver-time, memory, VC-size, and random-seed stability benchmarks;
- stale-cache, timeout, quantifier, aliasing, and model-adversarial tests;
- a reproducible independent proof-replay path for high-assurance use.

Coverage alone is not a soundness proof. Every new semantic feature must include
a nearby invalid program that would verify if its encoding were too strong.

Priority order toward broad C++
-------------------------------

P0 — preserve the sound kernel
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Keep unsupported behavior fail-closed, maintain exact lowering and false-proof
oracles, improve source-attributed obligations, and never convert timeout,
``unknown``, unsupported encoding, or a bounded run into ``Verified``.

P1 — general addressable objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The bounded exit gate is complete: promoted pointer-bearing local objects,
scalar field/element references, modular slices, same-array difference, and
inferred fresh-owned scalar factory results retain exact lifetime/provenance
and reject paired invalid programs. Remaining generalizations are aggregate,
rvalue, and temporary references; by-value pointer-bearing interfaces; stored
and spec pointer positions; ownership-taking parameters; general
allocation/deallocation/escape contracts; non-scalar allocation; and
RAII-ready lifetime transitions.

P2 — core idiomatic C++
~~~~~~~~~~~~~~~~~~~~~~~

Add member functions, constructors/destructors, copy/move, templates after
instantiation, structured control flow, floating point, controlled globals,
nested/base subobjects, and closed-target indirect calls.

P3 — automation and scale
~~~~~~~~~~~~~~~~~~~~~~~~~

Add induction/calculation ergonomics, triggers/profiling, candidate invariants,
VC splitting/slicing/simplification, source counterexamples, caching,
parallelism, stability gates, and solver diversity.

P4 — libraries and application ecosystem
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Add verified/conformance-tested standard-library models, mathematical views,
build-system and IDE integration, machine-readable diagnostics, and stable
multi-file incremental verification.

P5 — advanced systems C++
~~~~~~~~~~~~~~~~~~~~~~~~~

Add virtual dispatch/RTTI, exceptions and cleanup, unions/object
representation/placement lifetime, atomics/threads/memory orders, coroutines,
and selected compiler extensions only with explicit operational/effect models.

Before claiming arbitrary C++ verification
------------------------------------------

CppVerify should not claim raw/arbitrary C++ verification until:

#. references, arrays, object lifetime, RAII, methods, and instantiated
   templates are first-class in VCR;
#. provenance, effective type, subobjects, allocation effects, and exceptional
   cleanup compose across modular calls;
#. common standard-library ownership, container, view, and algorithm models
   exist;
#. automation scales across a public real-program benchmark suite;
#. failures and trusted assumptions are source-visible;
#. cross-target, fuzzing, differential, and proof-stability gates run
   continuously;
#. high-assurance users have reproducible proof replay or certificates.

The detailed contributor inventory, dependencies, and acceptance gates live in
`LIMITATIONS.md on GitHub
<https://github.com/SwayamInSync/cpp-verify-roadmap/blob/main/extras/docs/LIMITATIONS.md>`_.
