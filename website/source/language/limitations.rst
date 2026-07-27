Supported C++ subset
====================

CppVerify targets a growing fragment of ISO C++. The verifier is strongest on integer programs,
control flow, and modular function contracts.

Highest-priority semantic boundaries
------------------------------------

The following are outside the verified subset, in priority order:

#. **Concrete object identity and lifetime.** Heap allocation with ``new`` /
   ``delete``, deallocation, dangling pointers, placement construction,
   use-after-lifetime, provenance, alignment, strict aliasing, and subobject
   lifetime changes are not modeled. ``valid(p, n)`` is an abstract caller
   promise, not evidence derived from an allocation.
#. **Addressable references and pointer-bearing aggregates.** References,
   pointers stored inside records, nested aggregates, unions, non-trivial
   constructors/destructors, inheritance, and virtual dispatch are rejected.
   Supported records are flat and trivial, with fields materialized
   independently.
#. **Quantified recursive automation.** Bounded quantifiers and finite recursive
   unfolding are sound, but recursive spec calls at symbolic quantified sites
   can exceed Z3's decidable fragments and report ``unknown``.
#. **The wider C++ language.** Class/function templates in verified code,
   exceptions, RTTI, lambdas, coroutines, concurrency, atomics, and multiple
   inheritance are not part of the current core.

Pointer and heap reasoning are available in the language surface (see :doc:`pointers` and
:doc:`../book/part-ii/ch14-pointers-frames-modifies`). Pointer arithmetic and array indexing
(``*(p + i)``, ``p[i]``) verify with disjointness, and quantified loop invariants over a buffer
range prove whole-array properties: single-buffer fills, ``strlen``-style search loops, and
two-buffer ``memcpy``-style copies (given an explicit non-overlap precondition) all verify
end-to-end. Addresses are modeled as mathematical integers, so range conditions are wrap-free;
disjointness facts should use **bounded** indices — an unbounded pure-disequality disjointness
(``i != k`` with no range) may report ``unknown``. Depth of automation continues to expand; see
the project :doc:`../book/part-ii/ch17-backends-modular-calls` and design notes in the repo
``docs/`` tree.

The heap uses flat mathematical **target-byte addresses**. Typed ``T*``
arithmetic scales every element step by Clang's target ``sizeof(T)``, while
record fields use Clang's byte layout offset. Scalar, byte-sized, and
flat-record strides are covered by false-proof regressions. There is not yet an
allocation/provenance object that relates arbitrary cross-object and subobject
operations, however. Pointer subtraction is therefore rejected, and code that
depends on pointer reinterpretation or arithmetic across distinct allocations
remains outside the verified subset.

Fail-closed behavior and solver incompleteness
----------------------------------------------

Unsupported AST, type, storage, or encoding cases are errors or ``unknown``;
they are never replaced with a proof-shaped default. ``unknown`` means the
backend could not establish the VC (commonly a quantified array formula or a
timeout), and CppVerify treats the function as **not verified**. A deliberately
invalid program may therefore be rejected with either a concrete
counterexample or conservative ``unknown``. Only ``Verified`` means Z3 proved
the generated obligation unsatisfiable.

At modular calls, ``modifies(*p)`` is a region footprint. Since the flat heap
cannot yet delimit that region with allocation identity, the caller
conservatively forgets the whole heap. Exact footprints such as
``modifies(p[i])`` and ``modifies(p->field)`` preserve all other addresses.
This may require stronger postconditions, but avoids unsound frame facts.

Undefined-behavior checking
---------------------------

Core expression definedness is always checked for executable/proof code:
signed overflow, zero divisors, the signed-minimum division case, invalid shift
counts/operands, and non-null abstract-valid dereferences. Definite
initialization is tracked for supported local scalars and flat-record fields.

``--check-ub`` additionally enables **array bounds** on the Z3 path. A buffer's
extent is declared with ``valid(p, n)`` in a precondition, and every ``p[i]`` /
``*(p+i)`` access rooted at that parameter must then be in ``[0, n)`` (see
:doc:`integers` and :doc:`../book/part-ii/ch18-undefined-behavior`). Reads from
uninitialized heap storage and use-after-lifetime are not checked because the
heap does not yet track allocation state. The layering plan is in
``docs/UB-CHECKING.md``.

The marker must be a positive top-level conjunction clause, its first argument
must be the bare complete-object pointer, and only one marker may describe a
given pointer. Unsupported shifted, conditional, disjunctive, or duplicate
markers are errors rather than silently strengthened assumptions.