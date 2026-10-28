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

A record may be returned from an initializer list, ``return Pt{a, b};`` or
``return {a, b};``, whose fields are given in order and the rest zero, and a
structured binding copies a record and names its fields:

.. code-block:: cpp

   struct Pt { int x; int y; };

   Pt make(int a, int b)
     cv::post(cv::result.x == a && cv::result.y == b)
   {
     return Pt{a, b};
   }

   int sum(Pt p)
     cv::pre(-1000 <= p.x && p.x <= 1000 && -1000 <= p.y && p.y <= 1000)
     cv::post(cv::result == p.x + p.y)
   {
     auto [a, b] = p;
     return a + b;
   }

A counterexample shows a binding by its name. Structured bindings of an
array, of a tuple-like type, or by reference (``auto &[a, b] = p;``) are not
supported yet.

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
   ring.cpp:25:3: error: verification failed: slot [bounds] [backend=z3] [reason=counterexample]
      25 |   return r->buf[i];
         |   ^
   ring.cpp:25:3: note: counterexample: r = 1, i = 8

Each index is checked against its own array, as Frama-C's RTE guards are,
and not only against the object. ``r->buf[8]`` has the address of
``r->head``, which lies inside ``*r``, and it is still an error. In
``p->grid[i][j]`` with ``int grid[3][4]``, both ``i < 3`` and ``j < 4`` must
hold, so ``grid[0][4]`` is rejected even though it has the address of
``grid[1][0]``. The check applies wherever an element is read or written: in
the body, and in postconditions and assertions, where a division by zero is
checked too.

A record with scalar fields is read as a whole through a pointer or a
reference field by field, each read checked where it is: ``Pair copy = *p;``,
``sum(*p)``, and ``return *p;`` read ``p->first`` and ``p->second``.

.. code-block:: cpp

   struct Pair {
     int first;
     int second;
   };

   int sum(Pair p)
     cv::pre(-1000 < p.first && p.first < 1000)
     cv::pre(-1000 < p.second && p.second < 1000)
     cv::post(cv::result == p.first + p.second)
   {
     return p.first + p.second;
   }

   int sum_at(const Pair *p)
     cv::pre(p != nullptr)
     cv::pre(-1000 < p->first && p->first < 1000)
     cv::pre(-1000 < p->second && p->second < 1000)
     cv::post(cv::result == p->first + p->second)
   {
     return sum(*p);
   }

.. code-block:: text

   Verified: sum [backend=z3]
   Verified: sum_at [backend=z3]

A record holding an array or another record (``Ring copy = *r;``) is not
read as a whole yet; read its fields instead.

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
   ring.cpp:41:10: error: verification failed: past [bounds] [backend=z3] [reason=counterexample]
      41 |   return q[8];
         |          ^
   ring.cpp:41:10: note: counterexample: r = 1, q = 1

The rules follow C++:

- forming the pointer requires the object it points into: ``r`` non-null, and
  each index inside its array, so ``&r->buf[i]`` with ``i == 8`` is an error
  even though ``r->buf + 8`` is not. A pointer formed in an operand that
  ``&&``, ``||``, or ``?:`` evaluates only on its own path is formed, and
  checked, only there: ``i < 8 && &r->buf[i] == q`` and ``i < 8 ? &r->buf[i]
  : nullptr`` need nothing of ``i`` when ``i >= 8``;
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
   pair.cpp:46:3: error: verification failed: reset_count [frame] [backend=z3] [reason=counterexample]
      46 |   reset(p.left);
         |   ^
   pair.cpp:46:3: note: counterexample: &p = 1
   pair.cpp:46:3: note: calls reset(1)

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
- every field is initialized when the callee may read its parameter's
  object before writing it, else the call is ``Unresolved`` with reason
  ``construct.unsupported``. A callee that writes each field it reads first
  (an out-parameter, :doc:`pointers`) needs none of them initialized, and
  the fields it writes on every path are initialized after the call.

The callee then writes only its footprints inside the local, by their bytes,
and every other local keeps its value. The caller's own
``cppverify::modifies`` need not name its locals.

.. cppverify-example: unresolved no_limit

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
     set_n(c);
     return c.n;
   }

   int limit_of(const Counter &c)
     cv::post(cv::result == c.limit)
   {
     return c.limit;
   }

   int no_limit()
     cv::post(cv::result == 0)
   {
     Counter c;
     c.n = 0;
     int l = limit_of(c);
     return 0;
   }

.. code-block:: text

   Verified: bump [backend=z3]
   Verified: reset [backend=z3]
   Verified: set_n [backend=z3]
   Verified: counted [backend=z3]
   Verified: half_initialized [backend=z3]
   Verified: limit_of [backend=z3]
   counter.cpp:62:3: Unresolved: no_limit [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: binding a reference or pointer parameter to storage that is not initialized, which the callee may read before writing it)

``set_n`` writes ``c.n`` before reading it, so ``half_initialized`` may
leave ``c.limit`` uninitialized; ``limit_of`` reads ``c.limit``, which
``no_limit`` never initializes.

The address of a local is supported as a call argument, and in a contract,
where a spec it is passed to cannot keep it: ``size(&r)`` in a loop
invariant or a ``cv::check`` of a local object ``r`` (the case study
:doc:`../case-studies/ring-buffer` reads its ring through such views). Stored
in a pointer variable (``Counter *q = &c;``), or formed through a local
reference to a local (``&r.n``, ``r.buf``), it is still an error, and so is
an address taken in ghost code, which could keep it. Under
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
   buf.cpp:39:3: error: verification failed: zero_more [bounds] [backend=z3] [reason=counterexample]
      39 |   zero(b);
         |   ^
   buf.cpp:39:3: note: counterexample: p = 1, n = 0
   buf.cpp:36:3: note: creates a local object at address 231056
      36 |   Buf b;
         |   ^
   buf.cpp:37:10: note: stores 1 at address 231056
      37 |   b.data = p;
         |          ^
   buf.cpp:38:9: note: stores 1 at address 231064
      38 |   b.len = n + 1;
         |         ^
   buf.cpp:39:3: note: calls zero(231056)
      39 |   zero(b);
         |   ^

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
   counter.cpp:49:5: error: verification failed: reset_count [frame] [backend=z3] [reason=counterexample]
      49 |   c.reset();
         |     ^
   counter.cpp:49:5: note: counterexample: &c = 1
   counter.cpp:49:5: note: calls reset(1)
   counter.cpp:55:5: error: verification failed: self_copy [aliasing] [backend=z3] [reason=counterexample]
      55 |   c.copy_from(c);
         |     ^
   counter.cpp:55:5: note: counterexample: &c = 1
   counter.cpp:55:5: note: calls copy_from(1, 1)

``reset`` states no ``cppverify::modifies``, so it may write all of ``c``,
which ``reset_count`` may not. ``copy_from`` writes ``this->n`` and reads
``o``, which by default are distinct objects; ``c.copy_from(c)`` is the same
object twice.

Not yet supported, each an error naming the function: virtual functions,
member functions of a class with bases, destructors, and conversion
functions. A member call may stand inside an expression (``return n +
get();``), as any call may (:doc:`functions-loops`, "Calls in expressions");
one that is not ``const`` may write its object, so it cannot share an
expression with a read of that object, whose order C++ leaves open. A class
template's member functions are verified in each specialization (`Class
templates`_).

Member operators
~~~~~~~~~~~~~~~~

A member operator is a member function whose object is its first operand:
``a == b`` is ``a.operator==(b)`` and ``a |= b`` is ``a.operator|=(b)``. One
that returns a reference to its own object (every return being ``return
*this;``, as an assignment operator's is) returns nothing the caller does not
already hold, so it is verified as returning nothing, and is called as a
statement of its own:

.. code-block:: cpp

   class Bits {
   public:
     Bits()
       cv::post(word == 0)
       : word(0) {}

     void set(int i)
       cv::pre(0 <= i && i < 16)
       cv::modifies(word)
       cv::post(word == (cv::old(word) | (1u << i)))
     {
       word = word | (1u << i);
     }

     bool operator==(const Bits &o) const
       cv::post(cv::result == (word == o.word))
     {
       return word == o.word;
     }

     Bits &operator|=(const Bits &o)
       cv::modifies(word)
       cv::post(word == (cv::old(word) | o.word))
     {
       word = word | o.word;
       return *this;
     }

     unsigned word;

     cv::type_invariant(word < 65536);
   };

   bool merged()
     cv::post(cv::result)
   {
     Bits a;
     Bits b;
     a.set(3);
     b.set(5);
     a |= b;
     b |= a;
     bool same = a == b;
     return same;
   }

.. code-block:: text

   Verified: Bits::Bits [backend=z3]
   Verified: Bits::set [backend=z3]
   Verified: Bits::operator== [backend=z3]
   Verified: Bits::operator|= [backend=z3]
   Verified: merged [backend=z3]

``operator|=`` keeps the invariant because its operand ``o`` satisfies it
too: an object passed by reference does (`Class invariants`_). ``a |= a``
passes one object as both ``this`` and ``o``, which are distinct by default,
and fails ``aliasing``. Using the reference such an operator returns, as in
``(a |= b) |= b``, ``Bits c = (a |= b);``, or ``c = (a |= b);``, is an error;
a free operator is a free function and returns its value as one does.

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
   ring.cpp:24:7: error: verification failed: Ring::Ring [initialization] [backend=z3] [reason=counterexample]
      24 |   int buf[8];
         |       ^
   ring.cpp:24:7: note: counterexample: this = 11798, first = 0
   ring.cpp:19:7: note: stores 0 at address 11830
      19 |     : head(0), count(1)
         |       ^
   ring.cpp:19:16: note: stores 1 at address 11834
      19 |     : head(0), count(1)
         |                ^
   ring.cpp:21:12: note: stores 0 at address 11798
      21 |     buf[0] = first;
         |            ^
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
  initialized needs initialized members only if it may read them before
  writing them: one that writes them first (its object is an out-parameter,
  :doc:`pointers`) may be called there, and the members it writes on every
  path are initialized after the call. Calling one that may read them first
  is ``construct.unsupported``.
- Copies of such an object are its members' copies: its class must be
  trivially copyable.
- Not yet, each an error naming the function: delegating constructors,
  constructors of a class that is not trivially copyable (a destructor or a
  copy operation of its own), of a class with members whose class provides a
  constructor, with reference or bit-field members, or larger than 256
  bytes; arrays of objects with constructors; ``new`` of a record.
- A constructed object is kept in memory, and is passed, returned, and
  copied by value as its fields, each read where it is (see `Records
  through pointers`_).

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

Class invariants
~~~~~~~~~~~~~~~~

On a class with member functions, the invariant holds at the boundary of
every public member function, which assumes it on entry and must restore it,
and every constructor must establish it. It is checked at every call,
internal calls included, so no call observes the object while it is broken:

.. cppverify-example: fails Meter::overflow

.. code-block:: cpp

   class Meter {
   public:
     Meter()
       cv::post(level == 0)
       : level(0) {}

     void add(int d)
       cv::pre(0 <= d && level + d <= 100)
       cv::post(level == cv::old(level) + d)
     {
       level = level + d;
     }

     void overflow()
       cv::post(true)
     {
       level = 101;
     }

     int get() const
       cv::post(cv::result == level)
     {
       return level;
     }

     int level;

     cv::type_invariant(0 <= level && level <= 100);
   };

   int filled()
     cv::post(0 <= cv::result && cv::result <= 100)
   {
     Meter m;
     m.add(30);
     int v = m.get();
     return v;
   }

.. code-block:: text

   Verified: Meter::Meter [backend=z3]
   Verified: Meter::add [backend=z3]
   meter.cpp:28:33: error: verification failed: Meter::overflow [type-invariant] [backend=z3] [reason=counterexample]
      28 |   cv::type_invariant(0 <= level && level <= 100);
         |                      ~~~~~~~~~~~^~~~~~~~~~~~~~~
   meter.cpp:28:33: note: counterexample: this = 1
   meter.cpp:17:11: note: stores 101 at address 1
      17 |     level = 101;
         |           ^
   Verified: Meter::get [backend=z3]
   Verified: filled [backend=z3]

``filled`` knows ``0 <= v <= 100`` from the invariant ``get`` returns with.

- A private or protected member function neither assumes nor restores it,
  so it may work on the object while the invariant is broken; a public one
  it calls then fails, at that call.
- A caller that writes a public field holds the invariant only if it keeps
  it: the next public call checks it there.
- An object a parameter refers to or points to satisfies its invariant on
  entry, as the caller shows at the call, and through a mutable reference or
  pointer it must at exit: every function boundary is one where it holds. A
  null pointer needs none, and a pointer with an extent is not covered yet.
  An extent in the invariant is ``this``'s, so an object passed by reference
  does not carry it yet.
- An extent of a pointer field, ``cv::valid(data, len)``, is assumed on
  entry as in a precondition (`Extents of pointer fields`_). At exit it
  states nothing; the next call checks it from what its caller knows, so a
  member function that changes ``len`` states how.
- A loop outside the class keeps the invariant of every object it reaches:
  the local objects alive at the loop and those its function's reference
  and pointer parameters address. Only the class's members, and code that
  writes a public field, change what the invariant states, and a public
  member keeps it, so the verifier adds it to the loop's invariants, where
  it is checked at entry and kept by every iteration like the user's own.
  A loop in a member function of the class gets none of its class's, since
  the member may break it between calls.

.. code-block:: cpp

   class Tally {
   public:
     Tally() cv::post(count_of(this) == 0) : count(0), last(0) {}

     void add(int d)
       cv::pre(0 <= d && d <= 10 && count_of(this) <= 1000)
       cv::post(count_of(this) == cv::old(count_of(this)) + d)
     {
       last = d;
       count = count + d;
     }

     friend cv::spec int count_of(const Tally *t);

   private:
     int count;
     int last;

   public:
     cv::type_invariant(0 <= last && last <= count);
   };

   cv::spec int count_of(const Tally *t) { return t->count; }

   int count_to(int n)
     cv::pre(0 <= n && n <= 100)
     cv::post(cv::result == n)
   {
     Tally t;
     int i = 0;
     while (i < n)
       cv::invariant(0 <= i && i <= n && count_of(&t) == i)
       cv::decreases(n - i)
     {
       t.add(1);
       i = i + 1;
     }
     return i;
   }

.. code-block:: text

   Verified: Tally::Tally [backend=z3]
   Verified: Tally::add [backend=z3]
   Verified: count_to [backend=z3]

Before 0.2, ``count_to`` was rejected: ``&t`` could not appear in a contract
(``raw address-of is unsupported until lexical lifetime and escape effects
are modeled``). A loop that called ``add`` on an object a reference
parameter names failed at that call (``[type-invariant]``): at the loop the
verifier knew of the object only what the loop's invariants said, and an
invariant over private fields could not be stated there.

Class templates
---------------

A class template is verified in each specialization the translation unit
instantiates, as a function template is (:doc:`functions-loops`): a member's
contract is instantiated with the member, in each specialization that uses
it, and the class's type invariants with the class.

.. cppverify-example: fails Box<short>::twice

.. code-block:: cpp

   template <typename T>
   class Box {
   public:
     Box(T v)
       cv::pre(0 <= v && v <= 20000)
       cv::post(value == v)
       : value(v) {}

     T twice() const
       cv::post(cv::result == 2 * value)
     {
       return value + value;
     }

     T value;

     cv::type_invariant(0 <= value && value <= 20000);
   };

   int doubled(int v)
     cv::pre(0 <= v && v <= 20000)
     cv::post(cv::result == 2 * v)
   {
     Box<int> b(v);
     int d = b.twice();
     return d;
   }

   short doubled_short(short v)
     cv::pre(0 <= v && v <= 20000)
   {
     Box<short> b(v);
     short d = b.twice();
     return d;
   }

.. code-block:: text

   Verified: Box<int>::Box [backend=z3]
   Verified: Box<int>::twice [backend=z3]
   Verified: Box<short>::Box [backend=z3]
   box.cpp:10:25: error: verification failed: Box<short>::twice [postcondition] [backend=z3] [reason=counterexample]
      10 |     cv::post(cv::result == 2 * value)
         |              ~~~~~~~~~~~^~~~~~~~~~~~
   box.cpp:10:25: note: counterexample: this = 1, result = -32768
   box.cpp:12:5: note: returns -32768
      12 |     return value + value;
         |     ^
   box.cpp:33:15: note: in instantiation of member function 'Box<short>::twice' requested here
      33 |   short d = b.twice();
         |               ^
   Verified: doubled [backend=z3]
   Unresolved: doubled_short [backend=z3] [reason=callee.contract] (relies on the contract of Box<short>::twice, which is not established)

``value + value`` is an ``int``, which a ``short`` holds only up to 32767.

- A member is verified in the specializations that use it, or that an
  explicit instantiation (``template class Box<long>;``) defines whole. One
  that no specialization uses is reported, not verified: ``warning:
  Box<T>::reset: member of a class template is not verified: this
  translation unit instantiates it in none of the class's specializations``.
- A clause that does not fit the arguments is a compiler error with Clang's
  instantiation note: an invariant where the class is instantiated, a
  member's contract where the member is used.
- Member function templates of a class template, member definitions outside
  the class, and specs that the invariant applies are instantiated as the
  rest is.

View functions
--------------

Define ``cppverify::spec`` functions that expose a mathematical view of a struct, then write contracts against
the view rather than the layout:

.. code-block:: cpp

   struct Pair { int first; int second; };

   cv::spec int total(Pair p) { return p.first + p.second; }

The current aggregate model is intentionally narrow. A record passed or
returned by value must be trivially copyable, standard-layout, and flat, with
scalar fields; when the value is kept in memory (a local object, or a record
a pointer or reference addresses), each field is read where it is, with the
checks of that read, so a copy of a record with a field never written fails
its ``initialization`` check. A local object whose address is needed (it holds a fixed array, or a
reference binds to one of its members) is promoted to an automatic object and
may also have nested record, pointer, and fixed-array members. A record
reached through a pointer or a reference may have the same members, and its
scalar fields and elements are reached one at a time (see `Records through
pointers`_ and `Records through references`_), or through a pointer into it
(see `Pointers into a record`_). Reference
members, unions, bases, virtual dispatch, and non-trivial
construction/destruction are rejected rather than approximated.
