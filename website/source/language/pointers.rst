Pointers
========

- Heap modeled internally as a Z3 array from mathematical addresses to
  width-neutral integer cells
- ``modifies(*p, ...)`` — frame
- ``aliases(p, q)`` — allow aliasing
- Implicit ``p != q`` for distinct mutable parameters

Example:

.. code-block:: cpp

   void write(int *p, int v)
     pre(p != nullptr)
     modifies(*p)
     post(*p == v)
   {
     *p = v;
   }

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
     pre(p != nullptr && i != j && p[j] == 5)
     modifies(*p)
     post(p[i] == v && p[j] == 5)        // p[j] is preserved
   { p[i] = v; }

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

Same-object pointer difference
------------------------------

A bounded form of pointer-pointer subtraction is supported in executable code:

.. code-block:: cpp

   long one_step(int *p)
     pre(p != nullptr)
     post(result == 1)
   {
     return (p + 1) - p;
   }

The operands must have the same complete pointee type and each must be a direct
pointer or an inline ``+0``/``+1`` position. CppVerify subtracts their
target-byte addresses, divides by ``sizeof(T)``, and converts the element count
to the target ``ptrdiff_t`` machine type. It separately proves that both bases
are non-null and live and that they have one object origin.

For abstract parameters, that origin currently means the same syntactic base:
``(p + 1) - p`` is accepted, while ``left - right`` remains rejected even under
``left == right`` or ``aliases(left, right)``. Numeric address equality is not
C++ provenance. Local dynamic aliases may instead establish the common origin
through their shared, nonzero lifetime identity.

Larger offsets, stored one-past values, general array distances, distinct
allocations, null or dangling operands, pointer compound assignment, and
pointer difference inside explicit ``spec`` or lifted ``constexpr`` functions
fail closed. The spec restriction avoids composing separately bounded offsets
through inlining until origin-and-position metadata is first-class.

Local scalar dynamic storage
----------------------------

Ordinary scalar ``new``/``delete`` is supported for a direct, non-escaping
local pointer. Allocation state is SSA-versioned: the verifier records the
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
Type-erasing/indirect copies, return, general call forwarding, general
arithmetic, and pointer reassignment or allocation/free in a loop body remain
unsupported. The same-object difference fragment above is the only dynamic
pointer arithmetic exception. A
restricted interface admits direct scalar access and acyclic direct-pointer
forwarding through matching parameters of verified, non-allocating executable
callees. A direct/conditional/null pointer result may retain caller-owned
provenance when its contract relates the result to those inputs. Returned local
copies, nested pointer-result calls, offsets, proof/external boundaries, and
type erasure still fail closed. See
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

Without ``--check-ub``, dereferences must still be non-null and live, but the
verifier does not invent a buffer length. Parameter pointers use abstract
entry-state allocation and initialization assumptions. Concrete identity, liveness, alignment, and initialization are available only
for the bounded local scalar allocation subset. Its provenance is first-class
across supported local values and checked scalar call/return interfaces, but
abstract buffers and general pointer interfaces remain unsupported.

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

Distinct mutable pointer parameters are non-aliasing by default. The
``modifies(*out)`` clause permits the store and frames ``*preserved`` at its
entry value.

See :doc:`../book/part-ii/ch14-pointers-frames-modifies`.