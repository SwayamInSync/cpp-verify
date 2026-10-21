Chapter 14 — Pointers, frames, and modifies
===========================================

Apply Part I’s frame and aliasing ideas in C++.

Swap with contract
------------------

.. code-block:: cpp

   void swap(int* a, int* b)
     cv::pre(a != nullptr && b != nullptr)
     cv::modifies(*a, *b)
     cv::post(*a == cv::old(*b) && *b == cv::old(*a))
   {
     int t = *a; *a = *b; *b = t;
   }

``cppverify::old(*b)`` is the value at ``b`` at function entry.

Aliasing
--------

- Distinct pointer/reference parameters are assumed **non-aliased** by
  default whenever at least one of the pair is mutable.
- Use ``cppverify::aliases(dst, src)`` when aliasing is allowed.

Scalar lvalue references
------------------------

Scalar ``T&`` and ``const T&`` parameters use the same addressable heap model.
The binding itself is immutable; a value use loads its referent and assignment
stores through the binding:

.. cppverify-example: label swap

.. code-block:: cpp

   void swap_values(int& left, int& right)
     cv::modifies(left, right)
     cv::post(left == cv::old(right) && right == cv::old(left))
   {
     int temporary = left;
     left = right;
     right = temporary;
   }

The verifier implicitly requires each reference to be non-null, live, and
initialized. ``cppverify::old(left)`` reads the entry heap, while the unwrapped ``left`` in
the postcondition reads the final heap. Two distinct references, at least one
of them mutable, are object-range disjoint unless ``cppverify::aliases(left, right)``
is present.

Reference formals can be forwarded from another reference, bound to a direct
dereference such as ``set_value(*p, value)``, bound to a field or element of a
local object or of a parameter's buffer (``set_value(pt.x, 7)``,
``set_value(a[1], 9)``), or passed an initialized ordinary scalar local. Local
references may bind those same forms and chain:

.. cppverify-example: with swap

.. code-block:: cpp

   bool swap_locals()
     cv::post(cv::result)
   {
     int left = 1;
     int right = 2;
     int& alias = left;
     swap_values(alias, right);
     return left == 2 && right == 1;
   }

CppVerify spills only the locals whose addresses are needed (scalars, fixed
arrays, and simple records) from scalar SSA. Each becomes a fresh automatic object with target size/alignment, byte ownership,
liveness, initialization, and a non-escaping lifetime identity. A local
binding snapshots its address, so changing a source pointer later does not
rebind the reference.

Conditional bindings, temporaries, reference returns, address-taking, rvalue
references, and non-scalar referents remain rejected.
Addressable declarations inside loops and ``cppverify::old`` of automatic locals or local
bindings are also fail-closed; outer automatic locals and loop-local reference
aliases are supported.

Buffers and arrays
------------------

Pointer arithmetic (``*(p + i)``) and subscripting (``p[i]``) read and write
indexed heap locations. The heap uses target-byte addresses: a ``T*`` element
step is multiplied by Clang's target ``sizeof(T)``, and a record field adds its
target-layout byte offset. Distinct indices are distinct cells, so a store to
``p[k]`` leaves ``p[i]`` alone whenever ``i != k``. Every access must stay in
its object: the ``valid(p, n)`` extent a precondition declares, or else the
single object ``p`` addresses (see :doc:`ch18-undefined-behavior`).

There are three frame granularities:

- a **cell**, ``cppverify::modifies(p[i])`` or ``cppverify::modifies(p->field)``, names one exact
  address;
- a **range**, ``cppverify::modifies(p[lo : n])``, names the ``n`` elements from
  ``p[lo]``, half-open ``[lo, lo + n)`` (Clang's array-section syntax);
- a **region**, ``cppverify::modifies(*p)``, names the object ``p`` addresses: its
  ``valid(p, n)`` extent, or one object.

Inside the function, every store must lie in a footprint read in the entry
state. At a modular call, the caller's heap changes only inside the callee's
footprints instantiated with the arguments, and every other cell keeps its
value. A callee footprint must lie within the caller's own frame, cell by
cell, however its pointer was computed: a callee that writes its one object
may receive a cell the caller may write, or a copy of a pointer into an
object the caller may write.

A pointer-taking callee with no explicit ``cppverify::modifies`` that may write memory is
treated as writing the whole heap: a caller may lose a true fact about an
unrelated object, but it cannot retain a frame fact that an unknown write
might invalidate. An explicit caller frame cannot contain that implicit
effect; an unframed caller may still make the call.

To state a property of a whole range, put a **bounded quantifier** in the loop
invariant and the postcondition, over the half-open range ``[lo, hi)``. A
buffer-zeroing loop proves its full postcondition this way:

.. cppverify-example: label zero

.. code-block:: cpp

   using cppverify::valid;

   void zero(int* p, int n)
     cv::pre(valid(p, n) && n >= 0 && n <= 1000)
     cv::modifies(*p)
     cv::post(cv::forall(i, 0, n, p[i] == 0))
   {
     int j = 0;
     while (j < n)
       cv::invariant(0 <= j && j <= n && cv::forall(i, 0, j, p[i] == 0))
       cv::decreases(n - j)
     { p[j] = 0; j = j + 1; }
   }

The invariant ``cppverify::forall(i, 0, j, p[i] == 0)`` says "everything written so far is
zero"; preservation across the store uses the disjointness of ``p[j]`` from each
earlier ``p[i]``, and at exit (``j == n``) it yields the postcondition.

The loop needs no invariant about memory it does not touch: a loop writes
only the objects its stores and calls reach, and every other object keeps its
value. A loop may also name what it writes with ``cppverify::modifies`` after its
invariants, ACSL's ``loop assigns``. The footprints are read in each
iteration's state, so ``cppverify::modifies(p[0 : j])`` says "only the prefix written so
far has changed":

.. code-block:: cpp

   void zero_prefix(int* p, int n)
     cv::pre(valid(p, n + 1) && n >= 1 && n <= 1000)
     cv::modifies(*p)
     cv::post(p[n] == cv::old(p[n]))
   {
     for (int j = 0; j < n; j = j + 1)
       cv::invariant(0 <= j && j <= n)
       cv::modifies(p[0 : n])
       cv::decreases(n - j)
     { p[j] = 0; }
   }

Without the loop's ``cppverify::modifies``, the whole object ``p`` addresses is written
as far as the verifier knows, and ``p[n] == cppverify::old(p[n])`` would need an
invariant.

The object a store writes is found from where its pointer came from (its
*origin*), not from how the pointer is spelled. A pointer that walks through
a buffer (``*q = 0; q = q + 1;``) still writes only that buffer, and a pointer
chosen at run time (``int *p = first ? a : b;``) writes one of ``a`` and
``b``. In both cases every other object keeps its value without an
invariant; :doc:`../../language/pointers` has the complete examples.

A subtle point shows up when a loop relates **two** buffers, as in a ``memcpy``:

.. code-block:: cpp

   void copy(int* d, int* s, int n)
     cv::pre(valid(d, n) && valid(s, n) && n >= 0 && n <= 1000 &&
         (d + n <= s || s + n <= d))             // explicit non-overlap
     cv::aliases(d, s)
     cv::modifies(*d)
     cv::post(cv::forall(i, 0, n, d[i] == s[i]))
   {
     int j = 0;
     while (j < n)
       cv::invariant(0 <= j && j <= n && cv::forall(i, 0, j, d[i] == s[i]))
       cv::decreases(n - j)
     { d[j] = s[j]; j = j + 1; }
   }

This verifies. Two declared extents are disjoint by default, as two
mutable pointer parameters are; ``cppverify::aliases(d, s)`` lifts that default here to
show what the default provides. The non-overlap precondition is then
essential: **without** it the verifier is right to reject the copy, because a store to ``d[j]`` could clobber
some ``s[i]`` still to be read — which is exactly why the C standard library has
both ``memcpy`` (requires non-overlap) and ``memmove`` (handles overlap). The
preservation step relies on the source and destination ranges being disjoint,
which the verifier derives from the non-overlap as plain integer arithmetic
(``d + j < d + n <= s <= s + i``), because addresses are modeled as mathematical
integers rather than wrapping machine words.

Records through pointers
------------------------

A record often holds its storage inline: a fixed-capacity stack keeps its
items in an array member next to its size. Through a pointer to such a
record, every field and every array element is a heap cell of its own, at
the address the record layout gives it. Code reads and writes it, contracts
and footprints name it, and the same frame reasoning as for a buffer applies:

.. cppverify-example: fails push_full

.. code-block:: cpp

   struct Stack {
     int items[16];
     int size;
   };

   void push(Stack *s, int v)
     cv::pre(s != nullptr && 0 <= s->size && s->size < 16)
     cv::modifies(s->items[s->size], s->size)
     cv::post(s->size == cv::old(s->size) + 1)
     cv::post(s->items[cv::old(s->size)] == v)
     cv::post(cv::forall(k, 0, cv::old(s->size), s->items[k] == cv::old(s->items[k])))
   {
     s->items[s->size] = v;
     s->size = s->size + 1;
   }

   void clear(Stack *s)
     cv::pre(s != nullptr)
     cv::modifies(s->items[0 : 16], s->size)
     cv::post(s->size == 0 && cv::forall(k, 0, 16, s->items[k] == 0))
   {
     for (int i = 0; i < 16; i = i + 1)
       cv::invariant(0 <= i && i <= 16 && cv::forall(k, 0, i, s->items[k] == 0))
       cv::modifies(s->items[0 : 16])
       cv::decreases(16 - i)
     {
       s->items[i] = 0;
     }
     s->size = 0;
   }

   void push_full(Stack *s, int v)
     cv::pre(s != nullptr && 0 <= s->size && s->size <= 16)
     cv::modifies(*s)
   {
     s->items[s->size] = v;
     s->size = s->size + 1;
   }

.. code-block:: text

   Verified: push [backend=z3]
   Verified: clear [backend=z3]
   stack.cpp:36:21: error: verification failed: push_full [...::bounds@36:21] (counterexample: s [ssa=s_0] [type=pointer] = 1; trace: heap-write.store@36:21 address=65 value=<unknown>) [backend=z3] [reason=counterexample]

``push`` writes exactly two cells, so its postcondition can promise that every
item below the old size is unchanged. ``clear`` writes a range of the member
array and the size; ``s->items[0 : 16]`` is a range footprint like
``p[0 : n]``.

``push_full`` admits a full stack. The store ``s->items[16]`` would land on
``s->size``, which is inside ``*s`` and inside the frame, so a check against
the object alone would accept it. Each index is checked against its own
array, as Frama-C's RTE guards are, and the counterexample is the full stack:
the store's address is 65, which is ``s + 16 * 4`` with ``s = 1``.

A pointer into the member array can also walk it. The pointer may address
only the array it comes from: ``s->items``, not the whole record, so a walk
that runs one element too far reads ``s->size`` and fails:

.. cppverify-example: fails count_past

.. code-block:: cpp

   struct Stack {
     int items[16];
     int size;
   };

   int count_zero(const Stack *s)
     cv::pre(s != nullptr && 0 <= s->size && s->size <= 16)
     cv::post(0 <= cv::result && cv::result <= s->size)
   {
     int n = 0;
     for (const int *q = s->items; q != s->items + s->size; q = q + 1)
       cv::invariant(s->items <= q && q <= s->items + s->size)
       cv::invariant(0 <= n && n <= q - s->items)
       cv::decreases(s->items + s->size - q)
     {
       if (*q == 0)
         n = n + 1;
     }
     return n;
   }

   int count_past(const Stack *s)
     cv::pre(s != nullptr && 0 <= s->size && s->size <= 16)
   {
     int n = 0;
     for (const int *q = s->items; q != s->items + s->size + 1; q = q + 1)
       cv::invariant(s->items <= q && q <= s->items + s->size + 1)
       cv::invariant(0 <= n && n <= q - s->items)
       cv::decreases(s->items + s->size + 1 - q)
     {
       if (*q == 0)
         n = n + 1;
     }
     return n;
   }

.. code-block:: text

   Verified: count_zero [backend=z3]
   stack.cpp:31:10: error: verification failed: count_past [...::bounds@31:10#2] (counterexample: n [ssa=n_1] [type=i32] = 0, n [ssa=n_2] [type=i32] = 0, q [ssa=q_1] [type=pointer] = 1, q [ssa=q_2] [type=pointer] = 65, s [ssa=s_0] [type=pointer] = 1; trace: loop.entry@26:3 -> loop.inductive iteration@26:3 condition=true) [backend=z3] [reason=counterexample]

In ``count_past`` the solver chooses a full stack, and ``q`` reaches 65, the
address of ``s->size`` with ``s`` at 1. The verifier itself states that a
pointer stepped through the array stays a whole number of elements from its
start, as a generated invariant it proves, so the walk never lands between
elements. :doc:`../../language/structs` lists the forms that are supported.

Declaring a checked extent
--------------------------

Memory checking is on by default (``--no-check-ub`` turns it off). The
``valid(p, n)`` marker of ``<cppverify.h>`` declares a buffer's extent (a
user-declared ``cppverify::spec bool valid(int* p, int n)`` is the same marker; see
:doc:`ch18-undefined-behavior`):

.. code-block:: cpp

   using cppverify::valid;

   int get(int* p, int n, int i)
     cv::pre(valid(p, n) && 0 <= i && i < n)
     cv::post(cv::result == p[i])
   { return p[i]; }

``valid(p, n)`` entails ``n >= 0``. If ``n > 0``, ``p`` must be non-null and
abstractly valid; ``n == 0`` permits null. Every access based on ``p`` must prove
that its index lies in ``[0, n)``. The marker must be a positive top-level
conjunction clause on the bare complete-object pointer, with at most one marker
per pointer. A pointer without a marker addresses one object. With
``--no-check-ub``, dereference definedness is still mandatory, but accesses
are not checked against objects.

This remains an abstract parameter-buffer promise; it is not inferred from a
caller's allocation. Direct local scalar ``new``/``delete`` has a separate
concrete liveness, initialization, size, alignment, and local
pointer-provenance model (see :doc:`../../language/dynamic-storage`).

Pointer difference supports general same-array positions under a declared
extent. For ``q - p``, both pointers must come from one object and lie in
``[0, n]`` of its ``valid(p, n)`` extent; the inclusive endpoint is the legal
one-past position. The pointers may have been stepped or copied, in loops
too: ``cppverify::decreases(end - q)`` for a walking ``q`` is a pointer difference. The
verifier subtracts target-byte addresses, divides by ``sizeof(T)``, proves
non-nullness, liveness, common origin, bounds, and ``ptrdiff_t``
representability, and then materializes the machine result. Without an
extent, abstract and scalar-dynamic pointers retain only base and one-past
complete-object positions. Pointers into two different parameters' objects
may be one caller array, which contracts cannot state, so their difference is
``construct.unsupported``. Pointers loaded from memory and subtraction in
explicit specs or lifted ``constexpr`` functions remain fail-closed.

Extents also compose at modular calls. If a callee requires
``valid(q, length)``, the caller must prove that the ``length`` elements from
its argument lie in one of its objects: for ``p + offset`` from
``valid(p, n)``, that ``0 <= offset``, ``0 <= length``, and
``offset + length <= n``. The argument may also be a local copy, a choice
between pointers, or a pointer stepped in a loop; its elements must then lie
in the objects it may address. Empty one-past slices are legal. Read-only slice
chains preserve the heap, while exact-cell effects such as
``cppverify::modifies(q[0])`` update only the corresponding caller cell, and a range or
a whole-slice ``cppverify::modifies(*q)`` updates only the slice:

.. cppverify-example: with zero

.. code-block:: cpp

   void zero_tail(int* p, int n, int lo)
     cv::pre(valid(p, n) && n >= 1 && n <= 1000 && 0 <= lo && lo <= n)
     cv::modifies(*p)
     cv::post(cv::forall(k, 0, lo, p[k] == cv::old(p[k])))
     cv::post(cv::forall(k, lo, n, p[k] == 0))
   {
     zero(p + lo, n - lo);
   }

Fresh-owned factory results
---------------------------

CppVerify can transfer one scalar allocation out of a narrowly structured
factory:

.. code-block:: cpp

   int *make(int value)
     cv::post(cv::result != nullptr)
     cv::post(*cv::result == value)
   {
     int *owner = new int(value);
     return owner;
   }

   int consume(int value)
     cv::post(cv::result == value)
   {
     int *p = make(value);
     int observed = *p;
     delete p;
     return observed;
   }

Freshness is inferred from the executable body, never trusted from contract
syntax. Every path must return null or the exact live, fully initialized base
of the function's sole scalar allocation, with no pointer parameters, extra
escape, arithmetic derivation, or recursive/external ownership source. Direct
and local-alias forwarding through already inferred acyclic factories is
supported.

The call creates a fresh lifetime identity and exact size, alignment, owner,
liveness, and initialization metadata while preserving all existing heap
cells. The ordinary postcondition describes the pointee value. The caller may
mutate or delete the result; all aliases become stale together after deletion.
Uninitialized, freed, multiply allocated, weakly specified, or cyclic factory
results fail closed.

Type invariants
---------------

A ``cppverify::type_invariant`` attaches a property to a struct that every function may assume of its
parameters — a frame condition on *values* rather than memory. Declare it after the fields it names:

.. code-block:: cpp

   struct Point {
     int x;
     int y;
     cv::type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
   };

   int sum(Point p)
     cv::post(cv::result >= 0 && cv::result <= 2000)
   { return p.x + p.y; }            // the invariant on x, y is assumed here

It is injected as a precondition at the first use of an invariant field for
supported by-value flat records, so callers must establish it. Record
references are not yet in the verified subset; current references have scalar
referents only, such as a field or an element reached through a pointer. See
:doc:`../../language/structs`.

See :doc:`../../language/limitations` for the supported pointer and heap feature set.
