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
by default (over whole ``valid(p, n)`` extents);
``aliases(left, right)`` permits same-object aliasing.

``modifies(left)`` names the referent, a single scalar object, so a call
changes only that cell. A provenance-backed automatic or dynamic scalar actual
is framed as one exact cell after the callee passes the structural non-escape
scan.

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

   Addresses are byte-scaled, so separating ``p[i]`` from ``p[j]`` means
   separating ``4*i`` from ``4*j``. The default integer encoding derives that
   from ``i != j`` alone. With ``--int-encoding=bitvector`` it needs range
   reasoning about sign extension that bit-vector solvers do not do well, and
   the query returns ``unknown`` unless the indices are bounded, as the
   precondition above does.

Within a verified function body, ``modifies(*p)`` authorizes the **whole
region** rooted at ``p`` — a write to any ``p[i]`` is covered. A write through
a *different* base pointer that is not in ``modifies`` is still rejected.

A ``modifies`` footprint is one of:

- a **cell**: ``p[i]``, ``p->field``, or a reference, at its exact address;
- a **range** ``p[lo : n]``: the ``n`` elements from ``p[lo]``, half-open
  ``[lo, lo + n)`` (Clang's array-section syntax);
- a **region** ``*p``: the object ``p`` addresses, which is its
  ``valid(p, n)`` extent when it has one and otherwise one object.

At a **modular call** the caller's heap changes only inside the callee's
footprints, instantiated with the arguments; every other cell keeps its value.
A callee writing a range or a whole slice frames the rest of the buffer:

.. code-block:: cpp

   void zero_middle(int* p, int n, int lo, int len)
     pre(valid(p, n) && n >= 0 && n <= 1000 && 0 <= lo && 0 <= len &&
         lo + len <= n)
     modifies(p[lo : len])
     post(forall(i, lo, lo + len, p[i] == 0))
   {
     int j = lo;
     while (j < lo + len)
       invariant(lo <= j && j <= lo + len && forall(i, lo, j, p[i] == 0))
       modifies(p[lo : len])
       decreases(lo + len - j)
     { p[j] = 0; j = j + 1; }
   }

   void keeps_rest(int* p, int n)
     pre(valid(p, n) && n >= 4 && n <= 1000)
     modifies(*p)
     post(p[0] == old(p[0]) && p[3] == old(p[3]))
     post(p[1] == 0 && p[2] == 0)
   {
     zero_middle(p, n, 1, 2);
   }

Each callee footprint must lie within the caller's own frame. A pointer-taking
callee with no explicit ``modifies`` that may write memory is treated as
writing the whole heap, which cannot fit inside an explicit caller frame; an
unframed caller may still call it. Under ``--no-check-ub`` a region footprint
also forgets the whole heap. The whole-heap fallback can lose a true fact
about an unrelated object, but it cannot prove a false one.

To reason about a whole range, use a bounded quantifier in the loop invariant and
postcondition (the half-open bound ``[lo, hi)`` is the implicit trigger). A
fill/zero loop verifies end-to-end:

.. code-block:: cpp

   void zero(int* p, int n)
     pre(valid(p, n) && n >= 0 && n <= 1000)
     modifies(*p)
     post(forall(i, 0, n, p[i] == 0))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, p[i] == 0))
       decreases(n - j)
     { p[j] = 0; j = j + 1; }
   }

A loop writes only the objects its stores and calls reach, so every other
object keeps its value without an invariant saying so. A loop may also state
what it writes with ``modifies`` after its invariants (ACSL's ``loop
assigns``); the footprints are read in each iteration's state, so
``modifies(p[0 : j])`` describes the prefix written so far.

The objects a store reaches are found from where its pointer came from, not
its spelling: every pointer variable has origins, the objects it may address
(see *Pointer origins* below). A pointer that walks through a buffer still
writes only that buffer, and a pointer chosen among several parameters writes
one of their objects:

.. code-block:: cpp

   void fill_walk(int *a, int n, int *count)
     pre(valid(a, n) && n >= 0 && n <= 1000 && valid(count, 1))
     modifies(*a)
     post(forall(k, 0, n, a[k] == 7))
     post(*count == old(*count))
   {
     int *q = a;
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n && q == a + i)
       invariant(forall(k, 0, i, a[k] == 7))
       decreases(n - i)
     {
       *q = 7;
       q = q + 1;
     }
   }

   void clear_one(int *a, int *b, int *c, int n, bool first)
     pre(valid(a, n) && valid(b, n) && valid(c, 1) && n >= 1 && n <= 1000)
     modifies(*a, *b)
     post(*c == old(*c))
   {
     int *p = first ? a : b;
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n)
       decreases(n - i)
     {
       p[i] = 0;
     }
   }

Both verify without an invariant about ``*count`` or ``*c``.

Two-buffer copy loops (``memcpy``-style) need the source and destination
ranges to be disjoint; otherwise storing to the destination could clobber a
source cell still to be read, exactly the C ``memcpy`` vs ``memmove``
distinction. ``valid(d, n)`` and ``valid(s, n)`` extents provide this
automatically: the implicit non-aliasing default treats each declared extent
as the pointer's complete object, so the two extents are disjoint unless a
pointer is null or an extent is empty, and every caller must prove that. An
``aliases(d, s)`` pair keeps the single-object rule and may overlap.

.. code-block:: cpp

   void copy(int* d, const int* s, int n)
     pre(valid(d, n) && valid(s, n) && n >= 0 && n <= 1000)
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

The operands must have the same complete pointee type and one origin, and
each must lie in its origin's object: a ``valid(p, n)`` marker supplies the
extent and each position must lie in the closed interval ``[0, n]``; the
inclusive endpoint is the legal one-past position. CppVerify subtracts
target-byte addresses, divides by ``sizeof(T)``, proves that the mathematical
element distance is representable by the target ``ptrdiff_t``, and only then
materializes the machine result. Signed, unsigned, and target-width indices
follow their C++ machine representations. A position may be stepped or
copied any number of times, in a loop or not:

.. code-block:: cpp

   int length_of(const char *s, int n)
     pre(valid(s, n) && n >= 1 && n <= 1000)
     post(0 <= result && result < n)
   {
     const char *p = s;
     while (p < s + (n - 1) && *p != 0)
       invariant(s <= p && p <= s + (n - 1))
       decreases(s + (n - 1) - p)
     {
       p = p + 1;
     }
     return p - s;
   }

Without a declared extent, a direct abstract parameter or represented scalar
dynamic allocation has only its complete-object positions ``0`` and ``1``.
Local dynamic aliases establish one origin through their shared, nonzero
lifetime identity. Two different parameters may point into one caller array,
which the object model cannot express, so a difference between them (or
between pointers that may come from either) is ``construct.unsupported``:
neither proved nor reported as an error. Proving ``left == right`` does not
change that.

Pointers loaded from memory, null or dangling operands, out-of-range
positions, unrepresentable distances, pointer compound assignment, and
pointer difference inside explicit ``spec`` or lifted ``constexpr`` functions
fail closed.

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

Memory accesses are checked by default (``--no-check-ub`` turns it off).
``valid(p, n)`` in a precondition says that ``p`` points to ``n`` objects,
``p[0]`` to ``p[n - 1]``. ``<cppverify.h>`` provides it for every pointee
type:

.. code-block:: cpp

   #include <cppverify.h>
   using cppverify::valid;

   int get(const int* p, int n, int i)
     pre(valid(p, n) && 0 <= i && i < n)
     post(result == p[i])
   { return p[i]; }

   int past_end(const int* p, int n)
     pre(valid(p, n) && n >= 1)
   { return p[n]; }

.. code-block:: text

   Verified: get [backend=z3]
   error: verification failed: past_end [...::bounds@11:10]

The marker means ``n >= 0``. A positive extent also means ``p`` is non-null and
abstractly valid; an extent of zero permits null. Every ``p[i]`` or ``*(p + i)``
access rooted at that parameter must then prove ``0 <= i < n``, and pointer
arithmetic must stay in ``[0, n]``: ``p + n`` is the one-past position, which
may be formed and compared but not read. The marker must occur as a positive
top-level conjunction clause of a ``pre`` with a bare complete-object pointer,
and each pointer may have only one marker; ambiguous forms (under ``||``,
``!``, or a conditional, or a second marker for one pointer) fail closed.

``valid`` exists only for verification, like the spec collections of the same
header; Sema rejects it in executable code. Write ``cppverify::valid`` or add
``using cppverify::valid;``. Programs written before the header may declare
the marker themselves, and that form keeps working: a ``spec`` function named
``valid`` with a pointer and an integer parameter is the same marker.

.. code-block:: cpp

   spec bool valid(const long* p, int n) { return true; }

   long last(const long* a, int n)
     pre(valid(a, n) && n >= 1)
   { return a[n - 1]; }

A user declaration covers only its own pointer type, so one is needed per
pointee type; the header's template covers all of them.

A pointer without a marker addresses a single object, as Frama-C's ``\valid``
guards and Verus permissions require: ``p[1]`` through ``int *p`` fails, and
so does forming ``p + 10`` from ``valid(p, 2)``, since pointer arithmetic must
stay within the object's closed range ``[0, n]``. The object of a pointer is
the one its origin names, below; when its origin is unknown it is some
parameter's object, or the object at a base known to be valid such as a
callee's result.

Pointer origins
---------------

Every pointer variable has, at every point, its origins: the objects it may
address, as CompCert's memory blocks and Frama-C's base addresses. A pointer
parameter starts with the object it addresses on entry and a global's address
with the global. Pointer arithmetic keeps the origin, assignment copies it,
and branches and loops join the possibilities, so ``q = first ? a : b`` has
the origins ``a`` and ``b``. A pointer loaded from memory or returned by a
call has no known origin.

An access or a step must stay in its origin's object. A pointer that came
from ``a`` and moved one past its end is rejected there even when another
object happens to start at that address, as C++ requires. A pointer
difference needs one origin, and a loop writes only its stores' origins.

Inside a loop, the verifier proves two facts for you: a pointer the loop
moves stays a whole number of elements from its origin's start, and a pointer
that may have either of two origins keeps one of them. An invariant still
states addresses, and an address alone does not say where a pointer came
from. When a walker may be in either of two objects, tie it to the condition
that chose:

.. code-block:: cpp

   void clear_chosen(int *a, int *b, int n, bool s)
     pre(valid(a, n) && valid(b, n) && n >= 1 && n <= 1000)
     modifies(*a, *b)
   {
     int *q = s ? a : b;
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n && (s ? q == a + i : q == b + i))
       decreases(n - i)
     {
       *q = 0;
       q = q + 1;
     }
   }

With only ``q == a + i || q == b + i``, the invariant would allow ``q`` one
past the end of ``a`` at the start of ``b`` while it came from ``a``, and the
store there would be rejected.

The same marker composes across modular calls. Passing ``p + offset`` to a
callee with ``valid(q, length)`` requires a same-root proof of
``0 <= offset``, ``0 <= length``, and ``offset + length <= n``. An empty slice
may start at ``p + n``. Read-only slice calls preserve the heap, including
acyclic chains of read-only callees; exact-cell effects such as
``modifies(q[0])``, ranges, and a whole-slice ``modifies(*q)`` are also
supported, and frame every cell of ``p`` outside the slice.

With ``--no-check-ub``, dereferences must still be non-null and live, but
accesses are not checked against objects. Parameter pointers use abstract
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