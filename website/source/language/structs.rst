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

Reading a whole record or array through a pointer (``Ring copy = *r;``) is
not supported yet; read its fields instead.

Pointers into a record
----------------------

A pointer can also point into the object a pointer addresses. A member array
decays to a pointer to its first element (``r->buf``), and ``&`` gives the
address of an element, a field, or a nested record (``&r->buf[2]``,
``&r->head``, ``&r->inner``). Such a pointer may address only that
subobject: the array it comes from, or else the field or record. Every access
and step through it must stay there, however the pointer is copied, chosen,
or stepped, and so must the elements of every argument formed from it.
``q[8]`` below has the address of ``r->head``, inside ``*r``, and is still out
of bounds:

.. cppverify-example: fails past

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
     cv::post(cv::result == r->buf[0])
   {
     return first(r->buf, 8);
   }

   int total(const Ring *r)
     cv::pre(r != nullptr)
     cv::pre(cv::forall(k, 0, 8, 0 <= r->buf[k] && r->buf[k] <= 100))
     cv::post(cv::result >= 0 && cv::result <= 800)
   {
     int s = 0;
     for (const int *q = r->buf; q != r->buf + 8; q = q + 1)
       cv::invariant(r->buf <= q && q <= r->buf + 8)
       cv::invariant(0 <= s && s <= 100 * (q - r->buf))
       cv::decreases(r->buf + 8 - q)
     {
       s = s + *q;
     }
     return s;
   }

   int past(const Ring *r)
     cv::pre(r != nullptr)
   {
     const int *q = r->buf;
     return q[8];
   }

.. code-block:: text

   Verified: first [backend=z3]
   Verified: oldest [backend=z3]
   Verified: total [backend=z3]
   ring.cpp:41:10: error: verification failed: past [...::bounds@41:10#2] (counterexample: q [ssa=q_1] [type=pointer] = 1, r [ssa=r_0] [type=pointer] = 1) [backend=z3] [reason=counterexample]

The rules follow C++:

- forming the pointer requires the object it points into: ``r`` non-null, and
  each index inside its array, so ``&r->buf[i]`` with ``i == 8`` is an error
  even though ``r->buf + 8`` is not;
- a step may reach one past the end of the array, and an access may not;
- a pointer difference such as ``q - r->buf`` requires both pointers in one
  array, so ``&r->head - r->buf`` is an error;
- as a bare value, in a condition or a contract (``q != r->buf + 8``), the
  pointer only compares.

Such a pointer cannot yet leave the function, because the bounds it carries
would be lost there: returning it, or storing it in memory, is an error.

.. cppverify-example: rejects

.. code-block:: cpp

   struct Ring {
     int buf[8];
     int head;
     int count;
   };

   const int *slot(const Ring *r, int i)
     cv::pre(r != nullptr && 0 <= i && i < 8)
   {
     return &r->buf[i];
   }

.. code-block:: text

   ring.cpp:10:3: error: slot: returning a pointer into a member array or field is unsupported
      10 |   return &r->buf[i];
         |   ^~~~~~

Records through references
--------------------------

A reference to a record (``Counter &``, ``const Counter &``) is a pointer to
it that is never null and never reseated, so everything above holds of it:
``c.n``, ``c.buf[i]``, and ``c.inner.x`` are cells of the object ``c`` names,
and ``&c.n`` and ``c.buf`` are pointers into it. The verifier requires the
object to be live and initialized at entry, as for a scalar reference, and
two references of which one is mutable name distinct objects unless
``cppverify::aliases`` allows them to name one. ``cppverify::modifies(c)`` is the
whole object, as ``cppverify::modifies(*p)`` is for a pointer, and a record
or array member named whole, ``cppverify::modifies(p.left)`` or
``cppverify::modifies(r.buf)``, is the bytes of that member. A reference
parameter may be bound to a reference, to ``*p``, to a field such as
``p->left``, or to an element ``a[i]``, and so may a local reference:

.. cppverify-example: fails reset_count

.. code-block:: cpp

   struct Counter {
     int n;
     int limit;
   };

   struct Pair {
     Counter left;
     Counter right;
   };

   void bump(Counter &c)
     cv::pre(c.n < c.limit)
     cv::modifies(c.n)
     cv::post(c.n == cv::old(c.n) + 1)
   {
     c.n = c.n + 1;
   }

   void reset(Counter &c)
     cv::modifies(c)
     cv::post(c.n == 0 && c.limit == 10)
   {
     c.n = 0;
     c.limit = 10;
   }

   void reset_left(Pair &p)
     cv::modifies(p.left)
     cv::post(p.left.n == 0 && p.right.n == cv::old(p.right.n))
   {
     reset(p.left);
   }

   void bump_left(Pair *p)
     cv::pre(p != nullptr && p->left.n < p->left.limit)
     cv::modifies(p->left.n)
     cv::post(p->left.n == cv::old(p->left.n) + 1)
   {
     Counter &c = p->left;
     bump(c);
   }

   void reset_count(Pair &p)
     cv::modifies(p.left.n)
   {
     reset(p.left);
   }

.. code-block:: text

   Verified: bump [backend=z3]
   Verified: reset [backend=z3]
   Verified: reset_left [backend=z3]
   Verified: bump_left [backend=z3]
   pair.cpp:46:3: error: verification failed: reset_count [...::frame@46:3] (counterexample: p [ssa=p_0] [type=pointer] = 1; trace: call.reset@46:3 arg0=1) [backend=z3] [reason=counterexample]

``reset_left`` may write ``p.left``, which holds the whole object ``reset``
may write, so ``p.right`` keeps its value. ``reset_count`` may write only
``p.left.n``, and ``reset`` writes ``p.left.limit`` too: the call fails its
``frame`` check. A caller that may write both fields one by one,
``cppverify::modifies(p.left.n, p.left.limit)``, still fails it: the callee's
footprint is every byte of the record, which only a footprint naming the
record, or an object around it, contains.

Local records passed to callees
-------------------------------

A local record may be passed to a reference parameter (``bump(c)``), and
the address of a local, of one of its fields, or of an element of a local
array (``&c``, ``&c.n``, ``&a[1]``) to a pointer parameter. The callee is
verified for an object it does not own, so every access it makes through
the parameter, at whatever field or element, is proved to lie in that
object. The call checks the rest:

- the callee keeps no address of the local: it stores none in memory,
  returns none, frees none, and passes one only to callees that keep none
  themselves (recursion included). A callee without a verified body, or one
  that may keep the address, makes the call ``Unresolved`` with reason
  ``construct.unsupported`` (``the address of local or dynamic storage is
  passed to f, which may keep or free it, or has no verified body``);
- the whole record lies in the live local;
- every field is initialized, since the callee reads its parameter's object
  as initialized storage. C++ allows an out-parameter that is only written,
  but the verifier does not model one yet: the call is ``Unresolved`` with
  reason ``construct.unsupported``.

The callee then writes only its footprints inside the local, by their bytes,
and every other local keeps its value. The caller's own
``cppverify::modifies`` need not name its locals.

.. cppverify-example: unresolved half_initialized

.. code-block:: cpp

   struct Counter {
     int n;
     int limit;
   };

   void bump(Counter &c)
     cv::pre(c.n < c.limit)
     cv::modifies(c.n)
     cv::post(c.n == cv::old(c.n) + 1)
     cv::post(c.limit == cv::old(c.limit))
   {
     c.n = c.n + 1;
   }

   void reset(Counter *c)
     cv::pre(c != nullptr)
     cv::modifies(*c)
     cv::post(c->n == 0 && c->limit == 10)
   {
     c->n = 0;
     c->limit = 10;
   }

   void set_n(Counter &c)
     cv::modifies(c.n)
     cv::post(c.n == 1)
   {
     c.n = 1;
   }

   int counted()
     cv::post(cv::result == 11)
   {
     Counter c;
     c.n = 0;
     c.limit = 5;
     bump(c);
     int k = c.n;
     reset(&c);
     return k + c.limit;
   }

   int half_initialized()
     cv::post(cv::result == 1)
   {
     Counter c;
     c.n = 0;
     set_n(c);
     return c.n;
   }

.. code-block:: text

   Verified: bump [backend=z3]
   Verified: reset [backend=z3]
   Verified: set_n [backend=z3]
   Verified: counted [backend=z3]
   counter.cpp:48:3: Unresolved: half_initialized [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: binding a reference or pointer parameter to storage that is not initialized, since the callee is verified as reading initialized storage)

``half_initialized`` leaves ``c.limit`` uninitialized, and ``set_n`` would
read it as initialized.

The address of a local is supported as a call argument only. Stored in a
pointer variable (``Counter *q = &c;``), or formed through a local reference
to a local (``&r.n``, ``r.buf``), it is still an error. Under
``--no-check-ub`` the callee's accesses are not proved to lie in its object,
so a call that passes a local record is ``construct.unsupported``.

Not yet supported:

- reading a whole record through a reference, as through a pointer;
- reference returns, rvalue and ``volatile`` references, and references in
  spec and proof functions.

Extents of pointer fields
-------------------------

A record often describes a buffer it does not hold: a pointer and a length.
A precondition states its extent as for a pointer parameter,
``cppverify::valid(b.data, b.len)``, for a pointer field of the object a
pointer or reference parameter addresses (``s->data``, ``s.data``,
``(*s).data``, ``s->inner.data``). The extent describes the buffer the field
addresses when the function is entered. That value is an input of the
function as a parameter's value is, and the verifier treats it so: an
access through ``b.data`` must lie in the extent while the field still
holds it, and at a call the field's value at the arguments must have the
extent in the caller's objects, as a pointer argument must. A buffer through
a pointer to non-const is disjoint from the other address parameters'
objects by default, its own record's included, so writing ``b.data[i]``
leaves ``b.len`` alone; two buffers through pointers to const may be one.

.. cppverify-example: fails zero_more

.. code-block:: cpp

   struct Buf {
     int *data;
     int len;
   };

   void zero(Buf &b)
     cv::pre(cv::valid(b.data, b.len) && 0 <= b.len)
     cv::modifies(b.data[0 : b.len])
     cv::post(cv::forall(k, 0, b.len, b.data[k] == 0))
   {
     for (int i = 0; i < b.len; i = i + 1)
       cv::invariant(0 <= i && i <= b.len)
       cv::invariant(cv::forall(k, 0, i, b.data[k] == 0))
       cv::modifies(b.data[0 : b.len])
       cv::decreases(b.len - i)
     {
       b.data[i] = 0;
     }
   }

   void zero_prefix(int *p, int n, int k)
     cv::pre(cv::valid(p, n) && 0 <= k && k <= n)
     cv::modifies(p[0 : n])
     cv::post(cv::forall(j, 0, k, p[j] == 0))
   {
     Buf b;
     b.data = p;
     b.len = k;
     zero(b);
   }

   void zero_more(int *p, int n)
     cv::pre(cv::valid(p, n) && 0 <= n && n < 100)
     cv::modifies(p[0 : n])
   {
     Buf b;
     b.data = p;
     b.len = n + 1;
     zero(b);
   }

.. code-block:: text

   Verified: zero [backend=z3]
   Verified: zero_prefix [backend=z3]
   buf.cpp:39:3: error: verification failed: zero_more [...::bounds@39:3] (counterexample: n [ssa=n_0] [type=i32] = 0, p [ssa=p_0] [type=pointer] = 1; trace: allocation.automatic allocation@36:3 address=231056 provenance=18 -> heap-write.store@37:10 address=231056 value=1 -> heap-write.store@38:9 address=231064 value=1 -> call.zero@39:3 arg0=231056) [backend=z3] [reason=counterexample]

``zero_more`` passes a buffer one element longer than the extent of ``p``.
A field given another pointer in the body (``b.data = q;``) addresses that
pointer's object from then on, not the extent. A field of an array element
(``s->items[k].data``) cannot take an extent yet.

Member functions
----------------

A member function of a class without bases or virtual functions is verified
as a function of ``this``, a pointer to its object that is never null, as a
reference is: a field, written ``n`` or ``this->n``, is a cell of the object,
``cppverify::modifies(n)`` names it and ``cppverify::modifies(*this)`` the
object, and a call passes the object's address (``c.bump()`` passes ``&c``,
``p->bump()`` passes ``p``, and ``bump()`` in a member function passes
``this``). Its clauses are parsed once the class is complete, so they may
name members declared after them, as in C++26 contracts. ``this`` and the
other address parameters name distinct objects by default;
``cppverify::aliases(this, o)`` allows them to name one.

A non-const member function without ``cppverify::modifies`` may write its
object, which is the C++ reading of a method that changes ``*this``; a
``const`` one writes only its own storage, its ``mutable`` fields included
unless its ``cppverify::modifies`` lists them. An explicit
``cppverify::modifies`` replaces the default. A static member function is a
free function.

.. cppverify-example: fails reset_count self_copy

.. code-block:: cpp

   struct Counter {
     void bump()
       cv::pre(n < limit)
       cv::modifies(n)
       cv::post(n == cv::old(n) + 1 && limit == cv::old(limit))
     {
       n = n + 1;
     }

     int get() const
       cv::post(cv::result == n)
     {
       return n;
     }

     void reset()
       cv::post(n == 0 && limit == 10)
     {
       n = 0;
       limit = 10;
     }

     void copy_from(const Counter &o)
       cv::modifies(n)
       cv::post(n == o.n)
     {
       n = o.n;
     }

     int n;
     int limit;
   };

   int counted()
     cv::post(cv::result == 11)
   {
     Counter c;
     c.n = 0;
     c.limit = 5;
     c.bump();
     int k = c.get();
     c.reset();
     return k + c.limit;
   }

   void reset_count(Counter &c)
     cv::modifies(c.n)
   {
     c.reset();
   }

   void self_copy(Counter &c)
     cv::modifies(c.n)
   {
     c.copy_from(c);
   }

.. code-block:: text

   Verified: Counter::bump [backend=z3]
   Verified: Counter::get [backend=z3]
   Verified: Counter::reset [backend=z3]
   Verified: Counter::copy_from [backend=z3]
   Verified: counted [backend=z3]
   counter.cpp:49:5: error: verification failed: reset_count [...::frame@49:5] (counterexample: c [ssa=c_0] [type=pointer] = 1; trace: call.reset@49:5 arg0=1) [backend=z3] [reason=counterexample]
   counter.cpp:55:5: error: verification failed: self_copy [...::aliasing@55:5] (counterexample: c [ssa=c_0] [type=pointer] = 1; trace: call.copy_from@55:5 arg0=1 arg1=1) [backend=z3] [reason=counterexample]

``reset`` states no ``cppverify::modifies``, so it may write all of ``c``,
which ``reset_count`` may not. ``copy_from`` writes ``this->n`` and reads
``o``, which by default are distinct objects; ``c.copy_from(c)`` is the same
object twice.

Not yet supported, each an error naming the function: virtual functions,
member functions of a class with bases, destructors, conversion functions,
and member functions of a class template (whose contracts are ignored with a
warning). A member call inside an expression (``return n + get();``) is
unsupported as a free function's is; assign its result first.

Constructors
------------

A constructor runs on storage its caller allocated. When it is entered,
every member of its object is uninitialized; its member initializers run
first, in declaration order whatever order they are written in, a member it
does not name taking its in-class initializer; and by its end it must have
initialized every member. Its postcondition describes the new object. A
caller passes the object's address as ``this`` and holds an initialized
object after the call:

.. cppverify-example: fails Ring::Ring

.. code-block:: cpp

   struct Ring {
     Ring()
       cv::post(head == 0 && count == 0)
       cv::post(cv::forall(k, 0, 8, buf[k] == 0))
       : head(0), count(0)
     {
       for (int i = 0; i < 8; i = i + 1)
         cv::invariant(0 <= i && i <= 8)
         cv::invariant(head == 0 && count == 0)
         cv::invariant(cv::forall(k, 0, i, buf[k] == 0))
         cv::decreases(8 - i)
       {
         buf[i] = 0;
       }
     }

     Ring(int first)
       cv::post(head == 0 && count == 1 && buf[0] == first)
       : head(0), count(1)
     {
       buf[0] = first;
     }

     int buf[8];
     int head;
     int count;
   };

   int fresh()
     cv::post(cv::result == 0)
   {
     Ring r;
     return r.count + r.buf[7];
   }

.. code-block:: text

   Verified: Ring::Ring [backend=z3]
   ring.cpp:24:7: error: verification failed: Ring::Ring [...::initialization@24:7#2] (counterexample: ...) [backend=z3] [reason=counterexample]
   Verified: fresh [backend=z3]

The second constructor initializes ``buf[0]`` alone, and the failure is
located at the member it leaves uninitialized, at its second element. The
loop of the first states what it has written, which is also what shows the
array initialized (:doc:`functions-loops`).

- An implicit or defaulted default constructor is its members'
  initializers, run where the object is defined: ``struct Point { int x = 3;
  int y = 4; };`` then ``Point p;`` gives ``p.x == 3``. A constructor the
  class provides needs a contract, as any function a verified one calls.
- A constructor's precondition cannot read its object, whose lifetime has
  not begun, and ``cppverify::aliases`` cannot name ``this``: the object is
  new. Its frame is its object and the footprints it lists.
- A member function called on the object before every member is
  initialized reads them as initialized, which C++ does not require, so the
  call is ``construct.unsupported``, as an out-parameter's is.
- Copies of such an object are its members' copies: its class must be
  trivially copyable.
- Not yet, each an error naming the function: delegating constructors,
  constructors of a class that is not trivially copyable (a destructor or a
  copy operation of its own), of a class with members whose class provides a
  constructor, with reference or bit-field members, or larger than 256
  bytes; arrays of objects with constructors; ``new`` of a record. A
  constructed object is kept in memory, and passing or returning it by value
  is not supported yet.

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
- It is **not** injected for pointer-to-struct or reference-to-struct
  parameters: their fields are heap loads of an object in memory.
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
reached through a pointer or a reference may have the same members, and its
scalar fields and elements are reached one at a time (see `Records through
pointers`_ and `Records through references`_), or through a pointer into it
(see `Pointers into a record`_). Reference
members, unions, bases, virtual dispatch, and non-trivial
construction/destruction are rejected rather than approximated.
