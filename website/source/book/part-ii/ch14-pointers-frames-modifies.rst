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

- Distinct mutable pointer/reference address parameters are assumed
  **non-aliased** by default.
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
the postcondition reads the final heap. Distinct mutable references are
object-range disjoint unless ``cppverify::aliases(left, right)`` is present.

Reference formals can be forwarded from another reference, bound to a direct
dereference such as ``set_value(*p, value)``, or passed an initialized ordinary
scalar local. Local references may bind those same direct forms and chain:

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

CppVerify spills only address-required scalar locals from scalar SSA. Each
becomes a fresh automatic object with target size/alignment, byte ownership,
liveness, initialization, and a non-escaping lifetime identity. A local
binding snapshots its address, so changing a source pointer later does not
rebind the reference.

Subscript/field/conditional bindings, temporaries, reference returns,
address-taking, rvalue references, and non-scalar referents remain rejected.
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
value. A callee footprint must lie within the caller's own frame.

A pointer-taking callee with no explicit ``cppverify::modifies`` that may write memory is
treated as writing the whole heap: a caller may lose a true fact about an
unrelated object, but it cannot retain a frame fact that an unknown write
might invalidate. An explicit caller frame cannot contain that implicit
effect; an unframed caller may still make the call.

To state a property of a whole range, put a **bounded quantifier** in the loop
invariant and the postcondition — the half-open bound ``[lo, hi)`` is the trigger.
A buffer-zeroing loop proves its full postcondition this way:

.. cppverify-example: label zero

.. code-block:: cpp

   #include <cppverify.h>
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

Declaring a checked extent
--------------------------

Memory checking is on by default (``--no-check-ub`` turns it off). The
``valid(p, n)`` marker of ``<cppverify.h>`` declares a buffer's extent (a
user-declared ``cppverify::spec bool valid(int* p, int n)`` is the same marker; see
:doc:`ch18-undefined-behavior`):

.. code-block:: cpp

   #include <cppverify.h>
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
``valid(q, length)`` and receives ``p + offset``, the caller must prove one
origin and ``0 <= offset``, ``0 <= length``, and
``offset + length <= n``. Empty one-past slices are legal. Read-only slice
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
referents only. See :doc:`../../language/structs`.

See :doc:`../../language/limitations` for the supported pointer and heap feature set.
