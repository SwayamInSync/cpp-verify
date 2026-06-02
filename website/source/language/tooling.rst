Commands and flags
==================

.. code-block:: bash

   cpp-verify file.cpp
   cpp-verify --dump-ir=1,2 file.cpp
   clang++ -std=c++17 -fverify-contracts -c file.cpp -o file.o
   clang++ -std=c++17 -fverify-contracts -fno-verify -c file.cpp -o file.o

``--dump-ir`` layers: ``1`` VCR, ``2`` passive, ``3`` verification condition, ``4`` solver input.