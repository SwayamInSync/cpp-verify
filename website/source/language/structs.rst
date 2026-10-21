Structs and type invariants
===========================

Contracts may read fields of by-value flat struct/class parameters with ordinary
member syntax:

.. code-block:: cpp

   struct Rect { int w; int h; };

   int area(Rect r)
     cv::pre(r.w >= 0 && r.w <= 1000 && r.h >= 0 && r.h <= 1000)
     cv::post(cv::result >= 0)
   { return r.w * r.h; }

Records through pointers
------------------------

Through a pointer, every field and every element of a fixed array is
reachable, at any depth: ``p->f``, ``p->buf[i]``, ``p->inner.arr[j]``,
``p->grid[i][j]``, ``p->items[k].v``, ``(*p).buf[i]``, and ``p[k].buf[i]``
for an element of a ``valid(p, n)`` extent. Each one is a single heap cell.
Code can read and write it, name it in a contract or a ``cppverify::modifies``
footprint, bind a reference to it, and pass it to a reference parameter.

.. cppverify-example: fails slot

.. code-block:: cpp

   struct Ring {
     int buf[8];
     int head;
     int count;
   };

   int peek(const Ring *r)
     cv::pre(r != nullptr && 0 <= r->head && r->head < 8)
     cv::post(cv::result == r->buf[r->head])
   {
     return r->buf[r->head];
   }

   void put(Ring *r, int v)
     cv::pre(r != nullptr && 0 <= r->head && r->head < 8)
     cv::modifies(r->buf[r->head])
     cv::post(r->buf[r->head] == v && r->count == cv::old(r->count))
   {
     r->buf[r->head] = v;
   }

   int slot(const Ring *r, int i)
     cv::pre(r != nullptr && 0 <= i && i <= 8)
   {
     return r->buf[i];
   }

.. code-block:: text

   Verified: peek [backend=z3]
   Verified: put [backend=z3]
   ring.cpp:25:3: error: verification failed: slot [...::bounds@25:3] (counterexample: i [ssa=i_0] [type=i32] = 8, r [ssa=r_0] [type=pointer] = 1; ...) [backend=z3] [reason=counterexample]

Each index is checked against its own array, as Frama-C's RTE guards are,
and not only against the object. ``r->buf[8]`` has the address of
``r->head``, which lies inside ``*r``, and it is still an error. In
``p->grid[i][j]`` with ``int grid[3][4]``, both ``i < 3`` and ``j < 4`` must
hold, so ``grid[0][4]`` is rejected even though it has the address of
``grid[1][0]``. The check applies wherever an element is read or written: in
the body, and in postconditions and assertions, where a division by zero is
checked too.

Two forms are not supported yet. Reading a whole record or array through a
pointer (``Ring copy = *r;``) is an error; read its fields instead. Forming a
pointer to an array member, as passing ``r->buf`` to a buffer parameter does,
is also an error, because the pointer would have to carry the member's
bounds; index the member where it is used:

.. cppverify-example: rejects

.. code-block:: cpp

   struct Ring {
     int buf[8];
     int head;
     int count;
   };

   int first(const int *p, int n)
     cv::pre(cv::valid(p, n) && n >= 1)
     cv::post(cv::result == p[0])
   {
     return p[0];
   }

   int oldest(const Ring *r)
     cv::pre(r != nullptr)
   {
     return first(r->buf, 8);
   }

.. code-block:: text

   ring.cpp:17:16: error: oldest: a pointer to the array member 'buf' is unsupported; index the member where it is used, as in 'buf[i]'
      17 |   return first(r->buf, 8);
         |                ^~~~~~

``cppverify::type_invariant``
-----------------------------

A ``cppverify::type_invariant`` states a property every instance of a type maintains. Declare it **after** the
fields it names (it is parsed in place):

.. code-block:: cpp

   struct Point {
     int x;
     int y;
     cv::type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
   };

   int sum(Point p)
     cv::post(cv::result >= 0 && cv::result <= 2000)
   { return p.x + p.y; }            // x, y in [0, 1000] are assumed from the invariant

Semantics:

- The invariant is injected as a **precondition** at the first use of an
  invariant field for by-value parameters. Because it is a precondition,
  callers must establish it when they pass such a value.
- It is **not** injected for raw pointer-to-struct parameters (their fields are heap loads).
- **Returns are checked**: when a function returns a struct value of an invariant-bearing type,
  the verifier asserts the invariant holds for the returned value. Building and returning a struct
  whose fields violate the invariant is a verification error.

.. code-block:: cpp

   struct Box { int w; int h; cv::type_invariant(w >= 0 && h >= 0); };

   Box make(int a, int b)
     cv::pre(a >= 0 && a <= 50 && b >= 0 && b <= 50)   // drop b >= 0 and this fails
   { Box x; x.w = a; x.h = b; return x; }          // invariant asserted here

The invariant may be temporarily broken **inside** the function while you assign fields one at a
time — it is only required to hold at the return (the encapsulation boundary), not after each
individual field write.

View functions
--------------

Define ``cppverify::spec`` functions that expose a mathematical view of a struct, then write contracts against
the view rather than the layout:

.. code-block:: cpp

   struct Pair { int first; int second; };

   cv::spec int total(Pair p) { return p.first + p.second; }

The current aggregate model is intentionally narrow. A record passed or
returned by value must be trivial, standard-layout, and flat, with scalar
fields. A local object whose address is needed (it holds a fixed array, or a
reference binds to one of its members) is promoted to an automatic object and
may also have nested record, pointer, and fixed-array members. A record
reached through a pointer may have the same members, and its scalar fields and
elements are reached one at a time (see `Records through pointers`_). Reference
members, unions, bases, virtual dispatch, and non-trivial
construction/destruction are rejected rather than approximated.
