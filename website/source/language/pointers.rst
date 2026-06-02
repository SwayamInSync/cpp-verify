Pointers
========

- Heap modeled internally (Z3 arrays)
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

See :doc:`../book/part-ii/ch14-pointers-frames-modifies`.