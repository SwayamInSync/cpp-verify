Chapter 19 — Dynamic storage and lifetime
=========================================

The first rule for verifying dynamic memory is that allocation is **state**.
If validity were a timeless predicate, assuming both ``valid(p)`` before
``delete`` and ``!valid(p)`` afterwards would make the logic inconsistent.
From a contradiction, any postcondition could be "proved."

CppVerify instead versions allocation metadata just like it versions the value
heap. Each ``new`` and ``delete`` produces a new logical state.

A complete scalar lifetime
--------------------------

.. code-block:: cpp

   int compute(int input)
     post(result == input + 1)
   {
     int *p = new int(input);
     *p = *p + 1;
     int answer = *p;
     delete p;
     return answer;
   }

The proof follows the actual lifetime:

#. ``new int(input)`` chooses a non-null, correctly aligned, non-overlapping
   scalar object and starts its lifetime.
#. The initializer stores ``input`` and marks the cell initialized.
#. The assignment requires a live initialized read, then writes ``input + 1``.
#. ``delete p`` requires that ``p`` still denotes the live allocation base and
   ends that lifetime.
#. The returned local ``answer`` no longer depends on accessing the freed
   storage.

Default initialization matters
------------------------------

``new int`` starts an ``int`` lifetime but leaves its value indeterminate.
``new int()`` value-initializes it to zero. CppVerify keeps the distinction:

.. code-block:: cpp

   int good(int value) post(result == value) {
     int *p = new int;
     *p = value;
     int result_value = *p;
     delete p;
     return result_value;
   }

   int bad() post(true) {
     int *p = new int;
     return *p;              // rejected: uninitialized heap read
   }

This check is separate from liveness. A cell may be live but uninitialized, or
initialized in an old lifetime but dead now. A new allocation resets the
initialization state before applying its initializer.

Identity, disjointness, and reuse
---------------------------------

For each allocation event, the verifier issues a fresh lifetime identity that
can never be reused. It records which identity owns each target byte, the
identity's numeric base, and whether that identity is live. A second allocation
must choose a byte range whose previous owners are all dead. This proves that
simultaneous scalar allocations are distinct:

.. code-block:: cpp

   bool two_objects() post(result) {
     int *left = new int(1);
     int *right = new int(2);
     bool distinct = left != right;
     delete right;
     delete left;
     return distinct;
   }

Ending a lifetime changes the liveness heap rather than asserting the negation
of an old timeless fact. The allocator can therefore reuse a dead range later
without contradiction. Reuse does not revive the old pointer: even if its
numeric address equals the replacement pointer, its retained lifetime identity
no longer matches the byte owner's new identity.

Local pointer values retain provenance
--------------------------------------

The pointer address and its lifetime identity travel as a pair. Matching-type
local copies, reassignment, conditional selection, and direct ``nullptr``
assignment update both through ordinary SSA and branch merges:

.. code-block:: cpp

   int reassigned_alias(int value) post(result == value) {
     int *first = new int(0);
     int *owner = new int;
     int *alias = first;
     alias = owner;
     *alias = value;
     int answer = *owner;
     delete alias;
     delete first;
     return answer;
   }

The assignment changes ``alias`` to the identity of ``owner`` without changing
``first``. The store initializes the shared object, and deletion through
``alias`` ends the lifetime observed through ``owner`` too. A second deletion
or later dereference through either alias is rejected.

Calling a scalar helper
-----------------------

Lifetime identity can be substituted into a verified modular callee when its
matching pointer parameter is used only for direct scalar access:

.. code-block:: cpp

   void set_value(int *target, int value)
     pre(target != nullptr)
     modifies(*target)
     post(*target == value)
   {
     *target = value;
   }

   int through_helper(int value) post(result == value) {
     int *p = new int(0);
     set_value(p, value);
     int answer = *p;
     delete p;
     return answer;
   }

The call asserts the callee preconditions against the current allocation and
uses the usual ``modifies``/postcondition abstraction for the value heap.
Metadata ownership and liveness stay with the caller. This catches passing an
uninitialized object to a reader, passing a dangling pointer, and violating a
callee's implicit non-aliasing precondition.

The callee must have a verified body and a non-pointer return, and cannot
offset, subscript, copy, forward, return, or delete the dynamic pointer.
Nested executable/spec calls, ghost access, proof functions, and external
contract interfaces are excluded from this boundary.
Without these restrictions, a scalar allocation could be treated as a buffer
or its identity could be lost at the modular boundary.

Failures are path-sensitive
---------------------------

Liveness heaps merge across ``if`` statements in the same way as ordinary SSA
variables. A second ``delete`` is rejected only on paths where the first one
executed, and a dereference must be live and initialized on every path that can
reach it.

.. code-block:: cpp

   int maybe_bad(bool release) post(true) {
     int *p = new int(1);
     if (release)
       delete p;
     return *p;              // rejected on release == true
   }

Why the surface is intentionally narrow
---------------------------------------

The current checkpoint permits a direct local allocation pointer and
matching-typed local pointer values to be copied, reassigned, conditionally
selected, set to ``nullptr``, loaded, stored through, compared for equality,
converted to ``bool``, and deleted. Type-erasing or indirect copies, return,
general/spec/external calls, forwarding through nested calls, pointer
arithmetic, arrays, placement/nothrow allocation, records, and pointer
reassignment or allocation in a loop body are rejected. The restricted
verified scalar callee above is the only current call boundary.

Those restrictions are not parser shortcuts. General interfaces must transport
provenance and lifetime effects in contracts; arrays require element/subobject
lifetime and extent rules; non-trivial objects require constructor, destructor,
and exceptional-cleanup semantics. CppVerify fails closed until each layer can
preserve those facts.

The normal compilation path is unchanged: ``new`` and ``delete`` remain real
C++ operations. The logical metadata exists only in verification and adds no
runtime instrumentation.

See :doc:`../../language/dynamic-storage` for the exact reference and
:doc:`../../language/limitations` for the remaining priority order.
