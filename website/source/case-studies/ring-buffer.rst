Ring buffer
===========

A queue in a fixed array, specified as a queue.

Embedded code keeps its queues in fixed arrays: a UART's received bytes, the
samples of a sensor, the commands of a control loop. The array never moves,
two counters say where the queue starts and how long it is, and the indices
wrap around at the end. This case study is such a ring as a C++ class
template, ``Ring<N>``, with its fields private and an invariant over them,
and a contract that says what the class means rather than how it stores it:
it is a FIFO queue of at most ``N`` integers.

It exercises the class and template support of 0.2: a class template with a
non-type parameter, a constructor whose loop initializes an array member, a
class invariant, contracts written through spec functions that read the
private fields (*views*), ``assert`` inside a member function, and clients
that use a range-based ``for``, a ``switch`` over a scoped enumeration, and
an object passed by reference.

The code
--------

.. code-block:: cpp

   #include <cassert>

   namespace cv = cppverify;

   template <int N> class Ring;
   template <int N> cv::spec int size(const Ring<N> *r);
   template <int N> cv::spec int at(const Ring<N> *r, int i);

   // A queue of at most N ints in a fixed array, as embedded code keeps one:
   // its elements, oldest first, are buf[head], buf[head + 1], ..., wrapping
   // around at N.
   template <int N>
   class Ring {
   public:
     Ring()
       cv::post(size(this) == 0)
       : head(0), count(0)
     {
       for (int i = 0; i < N; i = i + 1)
         cv::invariant(0 <= i && i <= N && head == 0 && count == 0)
         cv::invariant(cv::forall(k, 0, i, buf[k] == 0))
         cv::decreases(N - i)
       {
         buf[i] = 0;
       }
     }

     bool full() const
       cv::post(cv::result == (size(this) == N))
     {
       return count == N;
     }

     // Appends v after the newest element.
     void push(int v)
       cv::pre(size(this) < N)
       cv::post(size(this) == cv::old(size(this)) + 1)
       cv::post(at(this, size(this) - 1) == v)
       cv::post(cv::forall(k, 0, cv::old(size(this)),
                           at(this, k) == cv::old(at(this, k))))
     {
       assert(count < N);
       buf[(head + count) % N] = v;
       count = count + 1;
     }

     // Removes the oldest element and returns it.
     int pop()
       cv::pre(size(this) > 0)
       cv::post(size(this) == cv::old(size(this)) - 1)
       cv::post(cv::result == cv::old(at(this, 0)))
       cv::post(cv::forall(k, 0, size(this),
                           at(this, k) == cv::old(at(this, k + 1))))
     {
       int v = buf[head];
   #ifdef FORGET_WRAP
       head = head + 1;
   #else
       head = (head + 1) % N;
   #endif
       count = count - 1;
       return v;
     }

   private:
     int buf[N];
     int head;
     int count;

     template <int M> friend cv::spec int size(const Ring<M> *r);
     template <int M> friend cv::spec int at(const Ring<M> *r, int i);

   public:
     cv::type_invariant(0 <= head && head < N && 0 <= count && count <= N);
   };

   // How many elements r holds.
   template <int N> cv::spec int size(const Ring<N> *r) { return r->count; }

   // The element i places after the oldest.
   template <int N> cv::spec int at(const Ring<N> *r, int i)
   {
     return r->buf[(r->head + i) % N];
   }

   // The samples come out in the order they went in.
   int first_two()
     cv::post(cv::result == 12)
   {
     cv::hide(at<4>);
     Ring<4> r;
     int samples[3] = {1, 2, 3};
     for (int s : samples)
       cv::invariant(size(&r) == cv::index)
       cv::invariant(cv::forall(k, 0, cv::index, at(&r, k) == samples[k]))
       r.push(s);
     if (!r.full())
       r.push(4);
     int a = r.pop();
     int b = r.pop();
     return 10 * a + b;
   }

   enum class Command { Push, Pop, Skip };

   // Applies one command to r: a push of v, a pop, which returns the oldest
   // element, or nothing.
   int apply(Ring<4> &r, Command c, int v)
     cv::pre(c != Command::Push || size(&r) < 4)
     cv::pre(c != Command::Pop || size(&r) > 0)
     cv::post(c != Command::Pop || cv::result == cv::old(at(&r, 0)))
     cv::post(c != Command::Skip || size(&r) == cv::old(size(&r)))
     cv::modifies(r)
   {
     switch (c) {
     case Command::Push:
       r.push(v);
       return 0;
     case Command::Pop:
       return r.pop();
     case Command::Skip:
       break;
     }
     return 0;
   }

``at(r, i)`` is the element ``i`` places after the oldest, and ``size(r)``
the number of elements: together they are the queue the ring stands for.
They are spec functions, which exist only for verification, and friends of
the class, so that they may read its private fields while no executable
code outside the class can.

What is proved
--------------

.. code-block:: text

   $ cpp-verify ring_buffer.cpp
   Verified: Ring<4>::Ring [backend=z3]
   Verified: Ring<4>::full [backend=z3]
   Verified: Ring<4>::push [backend=z3]
   Verified: Ring<4>::pop [backend=z3]
   Verified: first_two [backend=z3]
   Verified: apply [backend=z3]
   Summary: 6 verified in 1.9 s

A template is verified in each specialization a translation unit uses, here
``Ring<4>``. For it:

- every access to ``buf`` lies in the array, and no arithmetic overflows;
- the class invariant holds at the boundary of every public member function:
  the constructor establishes it, and ``push`` and ``pop`` keep it;
- ``push`` appends: the queue grows by one, its newest element is ``v``,
  and every older one keeps its place;
- ``pop`` removes the oldest element and returns it, and every other one
  moves one place forward;
- the constructor's loop initializes every element of ``buf``, so no read of
  the array is of an uninitialized value;
- ``assert(count < N)`` in ``push`` holds, from the precondition.

The clients use only these contracts. ``first_two`` loads three samples in
a range-based ``for`` whose invariants say where each one is in the queue,
adds a fourth if the ring is not full, and takes the two oldest out: the
contract alone shows that they are 1 and 2, so the function returns 12.
``apply`` runs one command on a ring a reference names; its contract states
what each command does, and ``cv::modifies(r)`` that it changes the ring.

A bug
-----

The classic one is to forget the wraparound when the oldest element leaves:

.. code-block:: cpp

   head = head + 1;

instead of ``(head + 1) % N``. Compiled with ``-DFORGET_WRAP``:

.. code-block:: text

   $ cpp-verify ring_buffer.cpp -- -DFORGET_WRAP
   Verified: Ring<4>::Ring [backend=z3]
   Verified: Ring<4>::full [backend=z3]
   Verified: Ring<4>::push [backend=z3]
   ring_buffer.cpp:74:58: error: verification failed: Ring<4>::pop [type-invariant] [backend=z3] [reason=counterexample]
      74 |   cv::type_invariant(0 <= head && head < N && 0 <= count && count <= N);
         |                      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~
   ring_buffer.cpp:74:58: note: counterexample: this = 1, v = -2147483648, result = -2147483648
   ring_buffer.cpp:57:10: note: stores 4 at address 17
      57 |     head = head + 1;
         |          ^
   ring_buffer.cpp:61:11: note: stores 1 at address 21
      61 |     count = count - 1;
         |           ^
   ring_buffer.cpp:62:5: note: returns -2147483648
      62 |     return v;
         |     ^
   ring_buffer.cpp:99:13: note: in instantiation of member function 'Ring<4>::pop' requested here
      99 |   int a = r.pop();
         |             ^
   Unresolved: first_two [backend=z3] [reason=callee.contract] (relies on the contract of Ring<4>::pop, which is not established)
   Unresolved: apply [backend=z3] [reason=callee.contract] (relies on the contract of Ring<4>::pop, which is not established)
   Summary: 3 verified, 1 failed, 2 unresolved (callee.contract 2) in 1.9 s

The class invariant fails when ``pop`` returns, at ``head < N``. The ring
is at address 1: ``buf`` takes its first 16 bytes, so ``head`` is at
address 17 and ``count`` at 21, and the path stores 4 into ``head``, one
past the last index of a ring of 4, and 1 into ``count``. The clients are
not verified while ``pop``'s contract is not.

What it took
------------

Writing the case study found four things the verifier did not support, and
0.2 does:

- a contract may take the address of a local object, ``size(&r)``, since a
  spec it is passed to cannot keep it (:doc:`../language/structs`);
- a loop keeps the class invariants of the objects it reaches, here
  ``r``'s, without restating them, which with private fields it could not
  (:doc:`../language/structs`);
- ``cv::hide`` and ``cv::reveal_with_fuel`` name a specialization of a spec
  template, ``at<4>`` (:doc:`../language/ghost-proofs`);
- ``first_two`` hides ``at``: its proof needs only the contracts of ``push``
  and ``pop``, which speak of ``at``, and the definition, with its ``%``
  inside every quantifier, kept the solver from finishing within the time
  limit.

Limits
------

- A view must be a free function that takes a pointer. A spec member
  function (``cv::spec int at(int i) const``) and a spec parameter of class
  reference type (``const Ring<N> &``) are not supported yet.
- The counterexample names the object, ``this = 1``, and the path shows the
  stores into it; the values of ``head`` and ``count`` are not listed by
  name yet.
