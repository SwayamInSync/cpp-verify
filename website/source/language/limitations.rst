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
     - An interface contract marked ``[[cppverify::trusted]]`` is assumed, not
       proved by CppVerify: on a declaration, on a definition (whose body is
       compiled but not verified), or on a proof function (whose
       postcondition is an axiom).
   * - **Incomplete automation**
     - The semantics are represented soundly, but Z3 may need user lemmas or
       return ``unknown``.

Outside the supported subset the verifier *fails closed*: it never reports a
proof for what it does not model. A construct it does not represent is an
error at the construct, and its function is ``Unresolved`` with reason
``construct.unsupported`` while every other function of the file is verified
(callers that rely on its contract are ``callee.contract``, and functions
that reach a spec it cannot represent are ``construct.unsupported`` too); one
it represents but does not model, such as a pointer difference between two
parameters' objects, makes the obligation that stands for it unsupported, and
the function is ``Unresolved`` with the same reason. A counterexample is never
a way of failing closed: ``Failed`` always means a checked counterexample.

Meaning of a result
-------------------

``Verified`` means the selected backend proved the generated verification
condition. It does not certify uncontracted functions, linked libraries, the
operating system, or any contract marked ``[[cppverify::trusted]]``. Proofs
are of total correctness: every executable loop needs ``cppverify::decreases``,
unless its condition is the constant false. A proof
that holds only for terminating executions (after ``cppverify::decreases(*)``) is marked
``[partial]``, one that relies on a trusted contract ``[trusts=f]``, and one
that no execution reaches ``[vacuous]``. A caller whose proof relies on a
callee contract that is neither established by the callee's own verification
nor marked trusted (including a contract without a definition) is
``Unresolved`` with reason ``callee.contract``.

Distinct pointer/reference address parameters are **non-aliasing by default**
whenever at least one pointee or referent is mutable. CppVerify generates a
complete-object disjointness precondition. Verified callers must prove it;
unverified external callers must honor it like a written ``cppverify::pre``.
``cppverify::aliases(p, q)`` permits same-object aliasing.

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
- mathematical ``cppverify::spec`` functions connected to machine-integer code;
- ``if``, conventional ``while``/``for``, contracted ``do`` loops, loop
  invariants, loop ``cppverify::modifies``, and ``cppverify::decreases`` (required on executable
  loops; ``cppverify::decreases(*)`` opts out);
- direct and mutual recursion with a well-founded termination measure;
- ``cppverify::pre``, ``cppverify::post``, ``cppverify::old``, ``cppverify::result``, ``cppverify::modifies`` (cells, ranges
  ``p[lo : n]``, and regions), ``cppverify::aliases``, and ACSL-style behaviors;
- scalar ``T&``/``const T&`` parameters with address-preserving reads, writes,
  contracts, and direct forwarding;
- proof functions, ghost code and ghost locals, ``cppverify::check ... by``
  and ``cppverify::calc``, bounded and unbounded quantifiers with triggers, ``cppverify::choose``,
  spec collections (``seq``, ``set``, ``multiset``, ``map``), and controlled
  recursive unfolding;
- mutable globals of integral, record, and array types, each one object at
  a fixed address, and integral ``const`` globals;
- flat trivial standard-layout records with scalar fields;
- fixed local arrays and promoted trivial local records with nested record,
  pointer, and fixed-array members;
- the fields and fixed-array elements of a record a pointer addresses, at any
  depth (``p->buf[i]``, ``p->inner.arr[j]``, ``p[k].items[i].v``), and
  pointers into them, each bounded by the array, field, or record it points
  into;
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
   * - Expressions and declarations
     - ``assert``, calls that do not return (an obligation that they are
       not reached), ``[[assume(e)]]`` and ``__builtin_assume(e)`` (proved,
       then assumed), discarded values (``x + 1;``, ``c && f(x);``),
       character literals (``'0'``, ``L'A'``), constants Clang evaluates (a
       ``consteval`` call, an ``if constexpr`` condition, ``noexcept(e)``, a
       requires-expression, a concept, a type trait, ``offsetof``,
       ``__builtin_LINE()``), template value
       parameters, default arguments and default member initializers,
       ``__builtin_expect``, the bit builtins (``__builtin_clz``,
       ``__builtin_ctz``, ``__builtin_popcount``, ``__builtin_parity``,
       ``__builtin_ffs``, their ``l`` and ``ll`` forms, and
       ``__builtin_bswap16/32/64``), a record returned from an initializer list
       (``return Pt{a, b};``), structured bindings that copy a record,
       declarations that do nothing (``static_assert``, type aliases,
       using-declarations, local classes and enumerations), and the value of
       an assignment, an increment or decrement, or a comma expression in
       executable code (``a = b = 0``, ``*dst++ = *src++``,
       ``while (k-- > 0)``), in C++'s order of evaluation.
     - Such a value in ghost and proof code, or of an assignment of a pointer
       to dynamic storage; a write that another unsequenced operand may read
       (an error, as C++ leaves it undefined); a pointer into a
       string literal (its characters are read by index);
       other builtins; structured bindings of an array, of a tuple-like type,
       or by reference.
   * - Pointers
     - One pointer level to supported complete objects. The type gate admits
       ``void*``, but no general erasure/ownership model is claimed.
     - Pointer-to-pointer, function pointers, type erasure/recovery, and general
       reinterpretation.
   * - References
     - Scalar ``T&``/``const T&`` parameters on contracted executable free
       functions, initialized local actuals (scalars and records, and
       ``&x`` of one passed to a pointer parameter, when the callee keeps no
       address of it), local aliases for
       boolean, integral, and enum referents, and bindings to a field or fixed
       array element of a promoted local object, or to a field or element of
       a parameter's buffer or of a record a pointer addresses
       (``int &alias = p->second;``, ``p[i]``, ``p->buf[i]``). References to
       records (``Counter &``, ``const Counter &``) as parameters and locals:
       a pointer never null or reseated, whose fields and elements are cells
       of the object it names (:doc:`structs`).
     - Conditional bindings, reference returns, rvalue references,
       temporaries/lifetime extension, reference members, and forwarding; a
       local not fully initialized passed to a callee
       (``construct.unsupported``), the address of a local stored in a
       variable or taken in ghost code, and a pointer formed through a local
       reference to a local record.
   * - Arrays
     - Pointer-parameter indexing, quantified abstract buffers, fixed
       local arrays (including arrays of records and multidimensional arrays)
       modelled as byte-addressed automatic objects up to 256 bytes, and the
       fixed-array members of a record a pointer addresses, each index
       checked against its own array, and pointers into them
       (``int *q = p->buf;``, ``&p->buf[i]``), bounded by the array.
     - Array parameters/fields carried by value, array references,
       ``new[]``/``delete[]``, loop-local arrays, and raw pointers derived from
       a local array; a pointer into a record a pointer addresses that leaves
       the function (returned or stored in memory).
   * - Records
     - Flat trivial standard-layout values with scalar fields; trivial
       standard-layout records with nested record, pointer, and fixed-array
       members as promoted local objects, and through pointers, where each
       scalar field and element is a heap cell.
     - Records that are not trivially copyable, inherited, polymorphic,
       union, and bit-field records, nested/pointer/array-bearing records
       used by value, and a whole record holding an array or a record read
       through a pointer (``Ring copy = *r;``).
   * - Functions
     - Free functions, member functions of classes without bases or virtual
       functions (:doc:`structs`), function and class templates in each
       specialization the translation unit instantiates
       (:doc:`functions-loops`, :doc:`structs`),
       overloads, namespaces, contracts, direct calls anywhere in an
       expression or condition (:doc:`functions-loops`), calls of functions
       without contracts, whose bodies are inlined (:doc:`functions-loops`),
       and
       direct and mutual recursion, also through stores to pointer and
       reference parameters and through automatic objects, with mutual
       recursion among functions of one kind (spec, proof, or executable).
     - Functions without contracts that are recursive, return a record by
       value, allocate, or whose loop invariants use ``cppverify::old``
       (each needs a contract), virtual functions, member functions of
       classes with bases, destructors, delegating constructors and the
       other constructors
       :doc:`structs` lists, conversion functions,
       templates and members of class templates that nothing instantiates
       (reported), variadics, indirect calls,
       recursion through a
       function that allocates or frees storage, and general link-time
       summaries. A function whose proof obligations would take more than
       ``--max-query-nodes`` expression nodes (4 million by default) is
       ``Unresolved`` with reason ``query.size-limit``: each check restates
       every assumption before it, so a long function with many checks grows
       fastest. See the memory limits of :doc:`tooling`.
   * - Storage
     - Supported locals, constrained scalar dynamic storage, inferred
       acyclic fresh-owned scalar factory results, and mutable globals and
       static locals of integral, record, and array types (:doc:`pointers`).
     - Globals that are themselves pointers, globals of a class with an
       invariant, static locals with an initializer that runs code or whose
       address is taken, pointers into constant tables,
       thread-local storage, general returned allocations, and user-declared
       modular allocation effects. Constant tables (``const`` and
       ``constexpr`` arrays with constant initializers, and string literals)
       are read by index (:doc:`pointers`).
   * - Structured control flow
     - ``if`` (including C++17 initializer), ``while``, ``for`` (with or
       without a condition), contracted ``do`` loops, condition declarations,
       ``switch`` (fallthrough, a ``default`` anywhere, GNU case ranges, an
       init statement), range-based ``for`` over an array (with
       ``cppverify::index``), blocks, ``return``, ``break``, and ``continue``
       anywhere, and comma expressions as statements.
     - A range-based ``for`` over a class (through ``begin`` and ``end``)
       or over an array of arrays, ``goto``, labels, and a ``case`` label inside another statement of its
       switch (Duff's device). An
       expression or statement nested more than 256 operations
       deep (a sum of 300 terms, say) is reported where it is, and the file
       stops: ``error: total: the expression at 4:276 nests more than 256
       operations deep, which the verifier does not support; split it into
       intermediate variables``. Before 0.2, such an expression could crash
       the verifier.
   * - Advanced C++
     - Not in the verified core.
     - Exceptions, lambdas, coroutines, RTTI, virtual dispatch, multiple
       inheritance, inline assembly, concurrency, and atomics.

An unsupported syntax case is not considered implemented merely because Clang
can parse it. It also needs VCR semantics, C++ definedness rules, modular
effects, backend encoding, and false-proof coverage.

A contracted function that uses an unsupported construct (a ``goto``, say)
fails closed: the construct is reported as an error where it is, and the
function is ``Unresolved`` with reason ``construct.unsupported``, while the
other functions of the file are verified (:doc:`tooling`). A few forms are
rejected this way inside otherwise supported code:

- storing a whole record through a pointer, ``*p = r`` (``unsupported
  aggregate assignment``): assign its fields; assigning one local record to
  another is supported;
- ``cppverify::aliases`` between pointers to different types (``aliases
  between different pointee types are unsupported``).

A template is verified in each specialization the translation unit
instantiates; one that nothing instantiates, and a member of a class
template that no specialization uses, is reported with a warning and not
verified, and the run continues with the other functions.

Objects, classes, and RAII
--------------------------

Flat records are currently value aggregates, not a general C++ object model.
CppVerify does not yet model:

- destructors, copy/move special members of their own, or RAII cleanup
  (constructors are verified, :doc:`structs`);
- ``this`` and member-function cv/ref qualifiers;
- class invariants over aliased mutable objects;
- base subobjects, vtables, or virtual dispatch;
- temporary materialization and lifetime extension;
- exception cleanup and exactly-once destruction;
- placement construction, lifetime restart, or ``std::launder``;
- spec member functions (``cv::spec int at(int i) const``), and spec
  parameters of class reference type (``const Ring<N> &``): a view of a
  class is a free spec function that takes a pointer, a friend when it reads
  private fields (:doc:`../case-studies/ring-buffer`).

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
``*(p + i)``, exact footprints such as ``cppverify::modifies(p[i])``, ranges such as
``cppverify::modifies(p[lo : n])``, and region footprints such as ``cppverify::modifies(*p)``.

Memory accesses are checked by default (``--no-check-ub`` turns it off). A
pointer without a declared extent addresses one object; accesses and pointer
arithmetic must stay in it. A syntactically restricted ``valid(p, n)``
precondition declares an abstract extent. It remains a caller promise rather than evidence
derived from a concrete caller allocation; it does not supply general lifetime,
alignment, provenance, or initialization. Bounds follow exact conditional and
short-circuit evaluation, and fresh represented storage is kept disjoint from
the complete declared incoming extent. Outside a precondition the marker
means nothing and is rejected (:doc:`pointers`), so an extent cannot yet be
stated for a returned pointer. A pointer field of a parameter's object may
take an extent (``valid(s->data, s->len)``, :doc:`structs`); a field of an
array element (``s->items[k].data``) may not yet.

For pairs involving mutable pointees, CppVerify adds a generated
complete-object disjointness precondition. ``cppverify::aliases(p, q)`` opts a pair into
same-object aliasing; it does not establish arbitrary partial overlap or create
provenance.

A returned pointer must be dereferenceable: the implicit postcondition that
callers rely on rejects a one-past-the-end result. ``cppverify::valid`` of
``<cppverify.h>`` covers every pointee type; a user-declared spec named
``valid`` with a pointer and an integer parameter is still recognized as the
same marker.

Scalar lvalue references and automatic locals
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contracted executable free functions may accept ``T&`` and ``const T&`` when
``T`` is ``bool``, integral, or enum. VCR retains the binding as an immutable
address: reading loads the referent, assignment stores through that address,
and ``cppverify::old(ref)`` selects the entry heap. Every reference receives an implicit
non-null and live precondition, and an initialized referent unless the body
writes it before reading it (an out-parameter, below).

``cppverify::modifies(ref)`` is an open region rooted at the referent, like
``cppverify::modifies(*p)``. Default object-range disjointness and ``cppverify::aliases`` apply across
pointer and reference parameters. A call may bind a reference from another
supported reference, an ordinary scalar local, or a direct
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
promoted objects, and a local reference to a record may bind a promoted
record. Conditional bindings, temporaries, reference returns, general raw
address-taking/array decay (through such a reference too, and ``&x`` but as
a call argument), and rvalue references remain fail-closed. A promoted object
passed to a callee, by reference or ``&x``, keeps its lifetime: the callee
must keep no address of it, and every field must be initialized unless the
callee writes it before reading it. Addressable declarations inside loops and ``cppverify::old`` of local
objects/bindings are also rejected; outer automatic locals and loop-local aliases
are supported. Pointer leaves may retain abstract pointer values, but storing a
provenance-bearing local dynamic pointer fails closed until pointer provenance is
represented in a parallel heap.
A reference or pointer parameter whose storage the body writes before it
reads it, an out-parameter, may receive storage not yet initialized
(``int a; init(a);``), as C++ allows (:doc:`pointers`). The rule is
syntactic: a read at a computed index (``p[i]``), a copy of the pointer, and
a callee that may read the storage first or has no verified body make the
parameter an input, and a call that passes storage not yet initialized to
an input is ``Unresolved`` with reason ``construct.unsupported``, not a
failure. Callers read a returned pointer's storage as initialized, so a
function that returns a pointer to storage not yet initialized is
``Unresolved`` the same way. A local
reference may bind storage not yet initialized: a read through it checks that
the object is initialized, as C++ does. Reference reads participate in the existing argument-order safety
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
- two null pointers differ by 0; other operands have one origin: they came
  from one parameter's object or one global (stepped, copied, or chosen
  through branches and loops), or dynamic aliases carry one shared live
  lifetime identity;
- each position lies in its origin's object: a ``valid(p, n)`` extent admits
  element positions in ``[0, n]``, including the one-past endpoint; without an
  extent, direct abstract and represented scalar-dynamic pointers retain only
  complete-object positions ``0`` and ``1``;
- target-byte difference is divided by ``sizeof(T)`` and converted to target
  machine ``ptrdiff_t`` only after proving representability.

Differences between different parameters' objects (which may be one caller
array) are ``construct.unsupported``. Pointers loaded from memory, distinct
allocations, null/dangling operands, out-of-range positions, explicit
``cppverify::spec`` bodies, and lifted ``constexpr`` specs fail closed.
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
postconditions. A call changes only the cells of its footprints: exact cells
such as ``cppverify::modifies(p[i])`` and ``cppverify::modifies(p->field)``, ranges
``p[lo : n]``, and regions ``cppverify::modifies(*p)``, which are the argument's
``valid`` extent or one object. A pointer-taking callee without ``cppverify::modifies``
that may write memory forgets the whole value heap, as does a region
footprint under ``--no-check-ub``.

A call inside an expression runs where C++ evaluates it: a short-circuit
operand's or a ``?:`` branch's call only on its path, and a loop
condition's call at every test. Where C++ leaves the order of operands open
(the operands of most operators, a subscript's array and index, a call's
arguments, and, before C++17, an assignment's two sides), a call that may
write memory beside an operand that reads memory or makes a call is an
error, since the verifier checks one order. Calls returning records are
made as statements, whole initializers, assignments, or return values
only.

A callee ``valid(q, length)`` extent can be instantiated from an argument
only after proving that its elements lie in one of the caller's objects, such
as a nonnegative subrange of a ``valid(p, n)`` extent contained in
``[0, n]``; the argument may be a copy, a choice, a stepped pointer, or a
callee's result whose contract places it. Empty one-past slices, transitive read-only
forwarding, exact-cell and range writes, and region writes through a
sub-slice are supported; every cell outside the written slice keeps its
value.

Checked local dynamic identities can cross a narrow scalar call/return boundary
when the caller owns the identity. Body-derived fresh-owned returns additionally
transfer one initialized scalar allocation through acyclic in-translation-unit
factories; external contracts cannot claim this effect. Missing effect concepts
include general allocation/deallocation contracts, parameter ownership
transfer, escape sets, separate read footprints, non-integral or aggregate
global state, exceptional cleanup, lock state, and concurrency interference.

Contracts marked ``[[cppverify::trusted]]`` are assumed. CppVerify checks
callers against their preconditions but cannot prove an unavailable or
unverified implementation satisfies its postconditions or frame; every proof
that relies on one names it in ``[trusts=...]``.

Specifications, recursion, and induction
----------------------------------------

Recursive specs are termination-checked and fuel-controlled. Fuel exposes a
finite number of defining-equation steps and prevents uncontrolled SMT matching
loops.

Recursive ``cppverify::proof`` functions with ``cppverify::decreases`` already provide manual
well-founded induction: the recursive call is legal only at a smaller measure,
and its postcondition is the guarded induction hypothesis. Fuel and induction
have different jobs; increasing fuel is not a proof for all inputs.

Current proof-language limitations include:

- no first-class ``induction`` syntax generating explicit base/step obligations;
- no named rewrite sets (``cppverify::calc`` chains and ``cppverify::check ... by`` are
  supported);
- an unbounded quantifier's counterexample is checked when its body depends
  on the bound variables through linear arithmetic, comparisons, memory and
  collection reads, and nested quantifiers (Presburger arithmetic), when its
  body can hold at finitely many values once the specs applied to the
  variable are unfolded or approximated, or when a witness among the values
  tried decides it; otherwise it is ``counterexample.unchecked``. ``cppverify::choose`` is uninterpreted apart from its
  Hilbert axiom, and a counterexample whose choice the axiom cannot be
  decided at is ``counterexample.unchecked`` too;
- an inductive predicate unfolds at most four levels below each named
  application by itself (more with ``cppverify::reveal_with_fuel``); a claim that needs
  it false where its derivations go round a cycle needs a postcondition or
  an induction lemma, and a counterexample that needs it false where its
  derivations reach infinitely many arguments is
  ``counterexample.unchecked`` unless a proved postcondition excludes the
  argument;
- proofs may rest on each other only through a checked measure (a recursion
  cycle, a spec's induction hypothesis, or a cluster of specs and lemmas
  sharing ``cppverify::decreases`` clauses of one length); otherwise they are
  ``proof.cycle``;
- spec collections hold mathematical integers only (no nested collections or
  records);
- user-written loop invariants, with no candidate-invariant/Houdini pass;
- no automatic termination-measure or lemma discovery. Inductions over a goal
  are tried automatically (by the measure of a recursive spec it applies, with
  the hypothesis at the values that spec's recursion reaches, and strong
  induction on an integer variable), everything else fixed and the goal itself
  as hypothesis; a property whose step needs a stronger statement than the
  goal, such as one whose recursion changes an accumulator, needs an induction
  lemma (a recursive ``cppverify::proof`` function), as in Dafny, Lean, and Isabelle. The
  hypothesis over all smaller values is stated as one quantifier only for
  integer variables, since canonical quantifiers range over integers; over a
  sequence the hypothesis is given at the values its recursion reaches. The
  inductions for one claim share the time of two attempts (each a sixth of
  the query's timeout, ``--timeout`` or, over collections,
  ``--collection-timeout``; see :doc:`../book/part-ii/ch13-spec-and-proof-functions`),
  so an induction that needs longer is not found: raise ``--timeout`` or
  state the lemma;
- a counterexample whose spec values cannot be computed is confirmed only by
  a proof from facts that are proved: when none settles the claim, it stays
  ``spec.fuel``, with the proposed input in the message. The proof fixes the
  counterexample's integers, truth values, and pointers, not its memory or
  collections, so facts about those must come from the claim's preconditions
  or from lemmas. A lemma is used where its conclusion speaks of the same
  spec application as the claim; when that application does not determine
  the memory the lemma reads, the lemma is taken at the function's entry
  memory. cvc5 confirms fewer counterexamples than Z3, since it returns
  ``unknown`` on more queries over memory;
- bounded domains are settled by evaluating the definitions across them, which
  reaches about a thousand values at the default budget; larger ones need a
  lemma;
- a spec's termination cannot use the spec's own definition: a nested call
  such as ``f(f(n - 1))`` whose argument is smaller only because of what ``f``
  returns needs a ``cppverify::post`` on ``f`` stating it, which is proved with the
  termination by induction on the measure;
- a counterexample whose bounded quantifier ranges over millions of values is
  checked when the body depends on the bound variable only through loads and
  comparisons of polynomials (degree up to eight) in it, machine arithmetic
  included where it provably never wraps over the range; otherwise, as with
  division, wrapping arithmetic, or a spec applied to the bound variable, it
  may be reported as ``counterexample.unchecked`` instead of a failure;
- a heap-reading spec without a ``cppverify::reads`` clause is not framed: that its
  value is preserved across an unrelated write must be proved by induction
  over the spec, which the verifier tries automatically at a cost in solver
  time, while ``cppverify::reads(p, n)`` gives it directly. A ``cppverify::reads`` range
  is a pointer and an element count; ranges that depend on the heap, such as
  a linked list, are not supported. Under ``--no-check-ub`` a call with a
  region footprint and a loop without its own ``cppverify::modifies`` forget the
  whole heap, so no frame is carried across them;
- no aggregate-returning specs;
- mutual recursion only among functions of one kind (spec, proof, or
  executable) sharing a measure of one length.
- recursion through a function that allocates or frees storage is
  ``construct.unsupported``; recursion that stores through pointer or
  reference parameters, calls heap-modifying functions, or uses automatic
  objects is supported.

These are mainly automation and usability limits. They do not permit an
unproved recursive property to become ``Verified``.

C++ definedness coverage
------------------------

Always-on obligations currently cover signed arithmetic overflow, invalid
division/remainder, invalid shifts, conversions to an enumeration outside its
value range, non-null/live represented dereferences, supported local definite
initialization, and local scalar dynamic lifetime errors. Since a conversion
into an enumeration is checked, every executable or proof value of one,
parameters and reads from memory included, is assumed to lie in its range.

Memory checking (the default, off with ``--no-check-ub``) adds object
bounds: an access or pointer step stays in the ``valid(p, n)`` extent or the
single object a pointer addresses, across modular sub-slices and same-array
pointer positions. Contracts get both kinds of obligation, each clause where
it is evaluated (see :doc:`functions-loops`). Together they are not yet
comprehensive C++ undefined-behavior checking.

Missing general UB semantics include object provenance outside the represented
fragment, strict aliasing, arbitrary alignment, unsequenced side effects
(rejected where one may meet another write or read, not checked) and all
unspecified evaluation-order alternatives, object lifetime restart,
exception unwinding, floating-point environment, volatile/atomics, and data
races.

Solver and automation limitations
---------------------------------

The Z3 backend supports bit-vectors, mathematical integers, arrays,
quantifiers, models, timeouts, module-owned ordered-obligation fallback, and
full SMT dumps. Layer 3 now provides deterministic obligation IDs and raw
source encodings from the exact canonical module solved by the backend.
Hard quantified recursive/heap formulas can still leave decidable fragments and
return ``unknown``. The default ``--int-encoding=auto`` encodes a query that
needs the bits of a non-constant operand with bit-vectors, so bit-level code
combined with quantified 64-bit heap reasoning can remain slow under every
encoding.

Important missing optimizations and tactics are:

#. richer source-level obligation categories, VC slicing, and independent
   resource reports beyond the current IDs/raw source encodings;
#. a verifier-specific simplifier before SMT;
#. affected-function invalidation;
#. first-class induction syntax;
#. trigger inference reported to the user (manual ``cppverify::trigger`` marks and
   ``--profile-quantifiers`` exist);
#. candidate invariants with Houdini-style elimination;
#. solver-resource stability measurement across seeds;
#. broader portfolio model extraction and optional CHC/PDR invariant discovery.

Candidate invariants and assertion batching, like the parallel solving,
proof caching, and trigger control CppVerify already has, are
production-proven techniques in systems such as Boogie/Dafny, Verus, Why3, and
Frama-C. Fully automatic invariant/lemma
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
through an independent SMT-LIB2 emitter. cvc5 is optional and system-installed;
its models are checked against the definitions like Z3's and shown like Z3's,
in source names with the steps of the failing path. Strict portfolio mode requires matching decisive
results and preserves Z3's model only after both solvers produce checked
counterexamples. cvc5 may return ``unknown`` on quantified or heap-heavy
formulas that Z3 solves; strict mode then remains ``Unresolved``. Recursive
specs are weaker on cvc5: it computes closed applications and checks its
counterexamples against the definitions, but native recursive definitions and
bounded-domain coverage are Z3 only, so cvc5 settles fewer such queries. Use Z3
for recursive specs. cvc5 decides sets, multisets, and maps as arrays, as Z3
does, but settles fewer goals that need an infinite set or ghost collections
in loops. In a forced bit-vector encoding cvc5 does not
relate exact contract arithmetic to bit-vectors as well as Z3.
BMC-transformed archive replay still uses the Z3-backed BMC aggregator.

**Race** (``--backend=race``) runs Z3 and cvc5 at once on the same canonical
obligations. The first proof or certified counterexample stands and stops the
other solver; when neither settles a module alone, the obligations each one
proved are joined. Each solver's own boundaries above still apply.

**Lean** consumes the same typed canonical obligation as Z3. Standalone export
is an unchecked scratch-pad and reports ``Exported``. Project mode emits
faithful definitions for the current integer, bit-vector, pointer, total-heap,
quantifier, overflow, and finite spec-fuel theories, plus one source-attributed
goal per ordered obligation. Generated files are separated from preserved user
lemmas/proofs. The pinned admission-free kernel path reports ``Certified`` only
after every active proof checks and rejects user axiom/opaque shortcuts.
Memory checks are lowered on this path as well as on Z3/cvc5/portfolio/BMC.
Spec collections are Lean values of core types (a sequence a ``List Int``, a
set its membership test, a multiset its counts, a map the value at each key),
with a lemma for each operation; a goal over them that needs induction, as
over a recursive spec of a sequence, takes a proof by hand.
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

Portable obligation schema v2 (which also reads v1 records) bounds imported
integer sorts to 4096 bits and
uses explicit parser depth/node/collection budgets. Supporting wider backend
sorts requires a deliberate schema/capability revision, not unbounded resource
allocation from an archive.

Libraries and real programs
---------------------------

CppVerify does not yet ship comprehensive libc or C++ standard-library models:
of the standard library it knows ``std::min`` and ``std::max`` of two
integers (:doc:`functions-loops`), and any other of its functions is an
error naming it. Of the C library it knows ``abs`` and the memory functions
``memcpy``, ``memmove``, ``memset``, and ``memcmp`` over integers, through
trusted models in ``<cppverify.h>`` that every proof using one names
(:doc:`pointers`). A call of a function with a body and no contract runs
that body, inlined (:doc:`functions-loops`); a call of one without a body
fails closed; a contract is assumed only when it is marked
``[[cppverify::trusted]]``, or, in one run over
several files, once the verification of its definition in another of them
establishes it, and for files verified apart once
``cpp-verify --check-contracts`` finds it established
(:doc:`functions-loops`). Contracts are not saved in precompiled
headers: a function declared in a PCH has no contract for the verifier, so a
contracted function that calls it fails closed (``call to function without a
verification contract``).

Broader application verification needs:

- the memory functions over records and pointers, and the string functions
  (``strlen``, ``strcmp``);
- views of standard containers as the spec collections of ``<cppverify.h>``;
- ``std::array``, ``std::span``, smart pointers, optionals, and string views;
- vectors, strings, associative containers, iterators, invalidation, and
  allocator effects;
- contracts for searching, copying, permutation, partition, and sorting.

Models should expose abstract values (for example, a container ``view()``)
rather than force each user to verify library internals. Trusted models also
need executable conformance and false-model tests.

Diagnostics and developer tooling
---------------------------------

Diagnostics name each obligation they report by a stable source-anchored ID
and range, show counterexamples with source variable names and a trace of
branches, calls, loops, heap writes, and lifetimes, and are also emitted as
JSON Lines (``--diagnostics-format=json``), SARIF (``sarif``), and GitHub
annotations (``github``). ``--profile-quantifiers`` reports
quantifier instantiations, ``--solver-rlimit`` sets reproducible solver
budgets, and clangd, built with the tool, provides editor integration.
Production readiness still needs:

- SARIF output;
- affected-function verification;
- CI regression reports.

Assurance and testing gaps
--------------------------

Every current checkpoint uses positive programs, nearby false programs, and
layered lowering checks. Every night, 484 contracted functions over integers,
pointers, and records are also verified by each backend and run natively
under UBSan on enumerated or sampled inputs, and a verdict that execution
contradicts fails CI (:doc:`../book/part-ii/ch17-backends-modular-calls`).
Broader trust additionally requires:

- grammar-guided fuzzing of supported and neighboring unsupported C++;
- metamorphic and AST/VCR/SMT translation-validation tests;
- differential execution of classes, templates, and dynamic storage;
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

Add first-class induction syntax, candidate invariants, VC splitting and
slicing, stability gates, and further solvers. Automatic induction,
``cppverify::calc``, triggers and quantifier profiling, source-level
counterexamples, proof caching, parallel solving, and the Z3/cvc5 portfolio
and race already ship.

P4 — libraries and application ecosystem
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Add verified/conformance-tested standard-library models, mathematical views,
build-system integration, and stable multi-file incremental verification.
clangd support, JSON Lines and SARIF diagnostics already ship.

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
