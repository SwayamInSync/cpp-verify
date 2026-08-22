Pointers
========

- Heap modeled internally as a Z3 array from mathematical addresses to
  width-neutral integer cells
- ``modifies(*p, ...)`` — frame
- ``aliases(p, q)`` — allow aliasing
- Implicit object-range disjointness for distinct mutable pointer/reference
  parameters

Example:

.. code-block:: cpp

   void write(int *p, int v)
     pre(p != nullptr)
     modifies(*p)
     post(*p == v)
   {
     *p = v;
   }

Scalar lvalue references
------------------------

Contracted executable free functions support scalar ``T&`` and ``const T&``
parameters for boolean, integral, and enum referents:

.. code-block:: cpp

   void swap_values(int& left, int& right)
     modifies(left, right)
     post(left == old(right) && right == old(left))
   {
     int temporary = left;
     left = right;
     right = temporary;
   }

The VCR parameter is an immutable address. Reading ``left`` loads the heap,
assignment stores through the address, and ``old(left)`` reads the entry heap.
CppVerify adds a non-null, live, and initialized entry precondition for each
reference. Mutable pointer/reference parameter pairs are object-range disjoint
by default; ``aliases(left, right)`` permits same-object aliasing.

``modifies(left)`` is an open region rooted at the referent, like
``modifies(*p)``. An abstract parameter call may conservatively forget the
value heap. A provenance-backed automatic or dynamic scalar actual is framed as
one exact cell after the callee passes the structural non-escape scan.

A reference argument may also be an initialized ordinary scalar local:

.. code-block:: cpp

   void set_value(int& target, int value)
     modifies(target)
     post(target == value)
   {
     target = value;
   }

   void set_pointer(int* target, int value)
     pre(target != nullptr)
     modifies(*target)
     post(*target == value)
   {
     set_value(*target, value);
   }

   int set_local(int value)
     post(result == value)
   {
     int local = 0;
     int& alias = local;
     set_value(alias, value);
     return local;
   }

Only address-required scalar locals are spilled from scalar SSA. They use fresh
automatic lifetime identities, target size/alignment, byte ownership,
liveness, and initialization. Local bindings snapshot the address, may chain,
and cannot escape; their conservative function-wide modeled lifetime is
therefore unobservable.

Subscript/field/conditional bindings, temporaries, reference returns,
address-taking, rvalue references, and non-scalar referents fail closed.
Addressable declarations inside loops and ``old`` of an automatic local/local
binding are rejected, while an outer automatic local and a local reference
declared inside a loop are supported. Requiring initialized storage excludes
output-only references to an indeterminate object for now.
Heap-mutating executable recursion through a reference fails closed until
termination analysis models heap-state updates.

Buffers and array indexing
--------------------------

Pointer arithmetic and subscripting are supported: ``*(p + i)`` and ``p[i]``
(read and write) lower to indexed heap accesses. Addresses use target bytes, so
each ``T*`` step is scaled by Clang's target ``sizeof(T)``; field selection adds
the target record-layout byte offset. Distinct indices are therefore distinct
locations, so storing to ``p[k]`` leaves ``p[i]`` unchanged for ``i != k`` —
the verifier gets this from array theory:

.. code-block:: cpp

   void set(int* p, int i, int j, int v)
     pre(p != nullptr && i != j)
     pre(0 <= i && i < 1000 && 0 <= j && j < 1000)
     pre(p[j] == 5)
     modifies(*p)
     post(p[i] == v && p[j] == 5)        // p[j] is preserved
   { p[i] = v; }

.. note::

   The index bounds are load-bearing. Addresses are byte-scaled, so separating
   ``p[i]`` from ``p[j]`` means separating ``4*i`` from ``4*j``; deriving that
   from ``i != j`` alone requires range reasoning about the sign extension that
   bit-vector solvers do not do well, and the query returns ``unknown``. Bound
   the indices — as any real buffer contract does anyway — and the separation
   is immediate.

Within a verified function body, ``modifies(*p)`` authorizes the **whole
region** rooted at ``p`` — a write to any ``p[i]`` is covered. A write through
a *different* base pointer that is not in ``modifies`` is still rejected.

At a **modular call**, region and exact footprints deliberately differ:

- ``modifies(p[i])`` and ``modifies(p->field)`` identify one exact address, so
  all other heap cells are preserved.
- ``modifies(*p)`` has no finite end in the modular parameter-pointer model.
  Checked scalar dynamic-storage interfaces can carry caller-owned identity,
  but the region is still open-ended. A call with a region footprint therefore
  conservatively forgets the whole value heap and recovers only facts stated by
  the callee's postconditions.
- A pointer-taking callee with no explicit ``modifies`` is treated just as
  conservatively. This prevents a missing frame from becoming a false proof.
- Such an implicit effect cannot fit inside an explicit caller frame. An
  unframed caller may pass its own address parameters or checked caller-owned
  scalar allocations.

The whole-heap fallback can lose a true fact about an unrelated object, but it
cannot prove a false one. Inside the callee itself, ordinary non-aliasing and
store semantics remain precise, as the ``write_result`` example below shows.

To reason about a whole range, use a bounded quantifier in the loop invariant and
postcondition (the half-open bound ``[lo, hi)`` is the implicit trigger). A
fill/zero loop verifies end-to-end:

.. code-block:: cpp

   void zero(int* p, int n)
     pre(p != nullptr && n >= 0 && n <= 1000)
     modifies(*p)
     post(forall(i, 0, n, p[i] == 0))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, p[i] == 0))
       decreases(n - j)
     { p[j] = 0; j = j + 1; }
   }

Two-buffer copy loops (``memcpy``-style) also verify, given an explicit
**non-overlap** precondition that the source and destination ranges are disjoint
(``d + n <= s || s + n <= d``). Without it the copy is rejected — storing to the
destination could clobber a source cell still to be read, exactly the C
``memcpy`` vs ``memmove`` distinction:

.. code-block:: cpp

   void copy(int* d, int* s, int n)
     pre(d != nullptr && s != nullptr && n >= 0 && n <= 1000 &&
         (d + n <= s || s + n <= d))      // ranges disjoint
     modifies(*d)
     post(forall(i, 0, n, d[i] == s[i]))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, d[i] == s[i]))
       decreases(n - j)
     { d[j] = s[j]; j = j + 1; }
   }

Addresses are reasoned about as mathematical integers, so range conditions like
the non-overlap above are exact (no wraparound). Array indices used in
disjointness facts should be bounded (as in real buffer code); an *unbounded*
pure-disequality disjointness (``i != k`` with no range) may report ``unknown``
(see :doc:`limitations`).

Same-array pointer difference
-----------------------------

Pointer-pointer subtraction is supported in executable code when both
positions are proved to belong to one array object:

.. code-block:: cpp

   long distance(int *p, int n, int i, int j)
     pre(valid(p, n) && p != nullptr && n >= 0 &&
         0 <= i && i <= n && 0 <= j && j <= n)
     post(result == i - j)
   {
     return (p + i) - (p + j);
   }

The operands must have the same complete pointee type and be compositional
pointer-arithmetic positions rooted at one base. With ``--check-ub``, a
``valid(p, n)`` marker supplies the extent and each position must lie in the
closed interval ``[0, n]``; the inclusive endpoint is the legal one-past
position. CppVerify subtracts target-byte addresses, divides by ``sizeof(T)``,
proves that the mathematical element distance is representable by the target
``ptrdiff_t``, and only then materializes the machine result. Signed, unsigned,
and target-width indices follow their C++ machine representations.

Without a declared extent, a direct abstract parameter or represented scalar
dynamic allocation has only its complete-object positions ``0`` and ``1``.
Abstract array operands must use the same syntactic SSA base. Merely proving
``left == right`` or writing ``aliases(left, right)`` does not establish shared
C++ provenance. Local dynamic aliases may instead establish one origin through
their shared, nonzero lifetime identity.

Stored/indirect pointer positions whose root cannot be recovered, distinct
origins, null or dangling operands, out-of-range positions, unrepresentable
distances, pointer compound assignment, and pointer difference inside explicit
``spec`` or lifted ``constexpr`` functions fail closed.

Local scalar dynamic storage
----------------------------

Ordinary scalar ``new``/``delete`` is supported for a direct local pointer.
Allocation state is SSA-versioned: the verifier records the
owning byte range, liveness, target size/alignment, and initialization. It
therefore rejects use-after-delete, double-delete, overlap between simultaneous
allocations, and uninitialized reads:

.. code-block:: cpp

   int roundtrip(int value)
     post(result == value)
   {
     int *p = new int;
     *p = value;
     int observed = *p;
     delete p;
     return observed;
   }

Its identity propagates through matching-typed local copies, reassignment,
conditional selection, direct ``nullptr`` assignment, and branch merges.
Deleting through any alias invalidates all aliases of that lifetime.
Type-erasing/indirect copies, general arithmetic, and pointer reassignment or
allocation/free in a loop body remain unsupported. The same-object difference
fragment above is the only dynamic pointer arithmetic exception. A
restricted interface admits direct scalar access and acyclic direct-pointer
forwarding through matching parameters of verified, non-allocating executable
callees. A direct/conditional/null pointer result may retain caller-owned
provenance when its contract relates the result to those inputs.

A separate inferred factory effect admits the exact live initialized base of
one fresh scalar allocation (or null) from a body-present acyclic function.
Direct and local-alias forwarding compose, and the caller may mutate or delete
the result. Contracts still state null correlation and pointee values. No
contract or external declaration can claim freshness: uninitialized, freed,
arithmetic-derived, multiply allocated, secondarily escaped, recursive, and
type-erased results fail closed. See
:doc:`dynamic-storage` for the complete boundary.

Buffer bounds with ``valid``
----------------------------

``--check-ub`` recognizes ``valid(p, n)`` in a precondition as an extent marker:

.. code-block:: cpp

   spec bool valid(int* p, int n) { return true; }

   int get(int* p, int n, int i)
     pre(valid(p, n) && 0 <= i && i < n)
     post(result == p[i])
   { return p[i]; }

The marker means ``n >= 0``. A positive extent also means ``p`` is non-null and
abstractly valid; an extent of zero permits null. Every ``p[i]`` or ``*(p + i)``
access rooted at that parameter must then prove ``0 <= i < n``. The marker is
discovered before its intentionally trivial body is inlined. It must occur as a
positive top-level conjunction clause with a bare complete-object pointer, and
each pointer may have only one marker; ambiguous forms fail closed.

The same marker composes across modular calls. Passing ``p + offset`` to a
callee with ``valid(q, length)`` requires a same-root proof of
``0 <= offset``, ``0 <= length``, and ``offset + length <= n``. An empty slice
may start at ``p + n``. Read-only slice calls preserve the heap, including
acyclic chains of read-only callees; exact-cell effects such as
``modifies(q[0])`` are also supported. An unbounded region effect
``modifies(*q)`` through a proper sub-slice remains fail-closed because the
current frame IR cannot express a symbolic finite write range.

Without ``--check-ub``, dereferences must still be non-null and live, but the
verifier does not invent a buffer length. Parameter pointers use abstract
entry-state allocation and initialization assumptions. Concrete identity, liveness, alignment, and initialization are available only
for the bounded scalar allocation and inferred fresh-owned return subset. Its
provenance is first-class across supported local values and checked scalar
call/return interfaces, but abstract buffers and general pointer interfaces
remain unsupported.

Frames also preserve unrelated objects across a write:

.. code-block:: cpp

   void write_result(int *out, int *preserved, int value)
     pre(out != nullptr && preserved != nullptr)
     modifies(*out)
     post(*out == value)
     post(*preserved == old(*preserved))
   {
     *out = value;
   }

Distinct mutable pointer/reference parameters are non-aliasing by default. The
``modifies(*out)`` clause permits the store and frames ``*preserved`` at its
entry value.

See :doc:`../book/part-ii/ch14-pointers-frames-modifies`.