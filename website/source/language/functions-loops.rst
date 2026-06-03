Functions and loops
===================

Functions
---------

.. code-block:: cpp

   int f(int x)
     pre(x > 0 && x < 1000)
     post(result > x)
   { return x + 1; }

Loops
-----

.. code-block:: cpp

   while (c)
     invariant(I)
     decreases(D)
   { ... }