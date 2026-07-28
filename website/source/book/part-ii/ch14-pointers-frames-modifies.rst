Chapter 14 — Pointers, frames, and modifies
===========================================

Apply Part I’s frame and aliasing ideas in C++.

Swap with contract
------------------

.. code-block:: cpp

   void swap(int* a, int* b)
     pre(a != nullptr && b != nullptr)
     modifies(*a, *b)
     post(*a == old(*b) && *b == old(*a))
   {
     int t = *a; *a = *b; *b = t;
   }

``old(*b)`` is the value at ``b`` at function entry.

Aliasing
--------

- Distinct mutable pointer/reference address parameters are assumed
  **non-aliased** by default.
- Use ``aliases(dst, src)`` when aliasing is allowed.

Scalar lvalue references
------------------------

Scalar ``T&`` and ``const T&`` parameters use the same addressable heap model.
The binding itself is immutable; a value use loads its referent and assignment
stores through the binding:

.. code-block:: cpp

   void swap_values(int& left, int& right)
     modifies(left, right)
     post(left == old(right) && right == old(left))
   {
     int temporary = left;
     left = right;
     right = temporary;
   }

The verifier implicitly requires each reference to be non-null, live, and
initialized. ``old(left)`` reads the entry heap, while the unwrapped ``left`` in
the postcondition reads the final heap. Distinct mutable references are
object-range disjoint unless ``aliases(left, right)`` is present.

Reference formals can be forwarded from another reference, bound to a direct
dereference such as ``set_value(*p, value)``, or passed an initialized ordinary
scalar local. Local references may bind those same direct forms and chain:

.. code-block:: cpp

   bool swap_locals()
     post(result)
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
Addressable declarations inside loops and ``old`` of automatic locals or local
bindings are also fail-closed; outer automatic locals and loop-local reference
aliases are supported.

Buffers and arrays
------------------

Pointer arithmetic (``*(p + i)``) and subscripting (``p[i]``) read and write
indexed heap locations. The heap uses target-byte addresses: a ``T*`` element
step is multiplied by Clang's target ``sizeof(T)``, and a record field adds its
target-layout byte offset. Distinct indices are distinct cells, so a store to
``p[k]`` leaves ``p[i]`` alone whenever ``i != k``. ``modifies(*p)`` frames the
whole region reachable through ``p``.

There are two frame granularities:

- ``modifies(p[i])`` or ``modifies(p->field)`` names one exact address. A
  modular caller preserves every other heap cell.
- ``modifies(*p)`` names an open-ended region rooted at ``p``. Inside the
  function it authorizes every ``p[i]`` store. Across a modular call, today's
  parameter-pointer model has no allocation identity or extent with which to
  delimit the region, so the verifier conservatively forgets the whole value
  heap and then assumes the callee's postconditions. Local scalar allocations
  can cross checked, non-allocating matching interfaces with their identity,
  but an open region still receives this whole-heap treatment.

The second rule is deliberately incomplete rather than unsound: a caller may
lose a true fact about an unrelated object, but it cannot retain a frame fact
that an unknown offset write might invalidate. A pointer-taking callee with no
explicit ``modifies`` receives the same whole-heap treatment. An explicit
caller frame cannot contain that implicit effect; an unframed caller may pass
its own address parameters or checked caller-owned scalar allocations.

To state a property of a whole range, put a **bounded quantifier** in the loop
invariant and the postcondition — the half-open bound ``[lo, hi)`` is the trigger.
A buffer-zeroing loop proves its full postcondition this way:

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

The invariant ``forall(i, 0, j, p[i] == 0)`` says "everything written so far is
zero"; preservation across the store uses the disjointness of ``p[j]`` from each
earlier ``p[i]``, and at exit (``j == n``) it yields the postcondition.

A subtle point shows up when a loop relates **two** buffers, as in a ``memcpy``:

.. code-block:: cpp

   void copy(int* d, int* s, int n)
     pre(d != nullptr && s != nullptr && n >= 0 && n <= 1000 &&
         (d + n <= s || s + n <= d))             // explicit non-overlap
     modifies(*d)
     post(forall(i, 0, n, d[i] == s[i]))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, d[i] == s[i]))
       decreases(n - j)
     { d[j] = s[j]; j = j + 1; }
   }

This verifies. The non-overlap precondition is essential: **without** it the
verifier is right to reject the copy, because a store to ``d[j]`` could clobber
some ``s[i]`` still to be read — which is exactly why the C standard library has
both ``memcpy`` (requires non-overlap) and ``memmove`` (handles overlap). The
preservation step relies on the source and destination ranges being disjoint,
which the verifier derives from the non-overlap as plain integer arithmetic
(``d + j < d + n <= s <= s + i``), because addresses are modeled as mathematical
integers rather than wrapping machine words.

Declaring a checked extent
--------------------------

On the Z3 and BMC paths, ``--check-ub`` gives a conventional ``valid`` spec
call special extent meaning:

.. code-block:: cpp

   spec bool valid(int* p, int n) { return true; }

   int get(int* p, int n, int i)
     pre(valid(p, n) && 0 <= i && i < n)
     post(result == p[i])
   { return p[i]; }

``valid(p, n)`` entails ``n >= 0``. If ``n > 0``, ``p`` must be non-null and
abstractly valid; ``n == 0`` permits null. Every access based on ``p`` must prove
that its index lies in ``[0, n)``. The marker must be a positive top-level
conjunction clause on the bare complete-object pointer, with at most one marker
per pointer. Without the option, dereference definedness is still mandatory,
but no length is inferred.

This remains an abstract parameter-buffer promise; it is not inferred from a
caller's allocation. Direct local scalar ``new``/``delete`` has a separate
concrete liveness, initialization, size, alignment, and local
pointer-provenance model (see :doc:`../../language/dynamic-storage`).

Pointer difference supports general same-array positions under a declared
extent. For ``(p + i) - (p + j)``, both indices must be proved in ``[0, n]``
for the same ``valid(p, n)`` origin; the inclusive endpoint is the legal
one-past position. The verifier subtracts target-byte addresses, divides by
``sizeof(T)``, proves non-nullness, liveness, common origin, bounds, and
``ptrdiff_t`` representability, and then materializes the machine result.
Without an extent, abstract and scalar-dynamic pointers retain only base and
one-past complete-object positions. Merely proving ``left == right`` does not
establish shared C++ provenance. Stored/indirect positions, distinct origins,
and subtraction in explicit specs or lifted ``constexpr`` functions remain
fail-closed.

Extents also compose at modular calls. If a callee requires
``valid(q, length)`` and receives ``p + offset``, the caller must prove one
origin and ``0 <= offset``, ``0 <= length``, and
``offset + length <= n``. Empty one-past slices are legal. Read-only slice
chains preserve the heap, while exact-cell effects such as
``modifies(q[0])`` update only the corresponding caller cell. Symbolic
writable ranges and unbounded ``modifies(*q)`` through a proper sub-slice still
fail closed.

Fresh-owned factory results
---------------------------

CppVerify can transfer one scalar allocation out of a narrowly structured
factory:

.. code-block:: cpp

   int *make(int value)
     post(*result == value)
   {
     return new int(value);
   }

   int consume(int value)
     post(result == value)
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

A ``type_invariant`` attaches a property to a struct that every function may assume of its
parameters — a frame condition on *values* rather than memory. Declare it after the fields it names:

.. code-block:: cpp

   struct Point {
     int x;
     int y;
     type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
   };

   int sum(Point p)
     post(result >= 0 && result <= 2000)
   { return p.x + p.y; }            // the invariant on x, y is assumed here

It is injected as a precondition at the first use of an invariant field for
supported by-value flat records, so callers must establish it. Record
references are not yet in the verified subset; current references have scalar
referents only. See :doc:`../../language/structs`.

See :doc:`../../language/limitations` for the supported pointer and heap feature set.
