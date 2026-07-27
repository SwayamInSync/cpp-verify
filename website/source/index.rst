CppVerify
=========

**CppVerify** is a verifier for C++ that checks your code against the properties you write in the
program itself — and reports whether those properties always hold, or shows you when they can fail.

Formal verification lets you treat correctness as an engineering artifact: you state what should
be true, and the tool either proves it or gives you a precise reason it does not. CppVerify
brings that discipline to everyday C++ without a separate language or annotation dialect.

.. figure:: /_static/diagrams/cppverify-workflow.svg
   :align: center
   :figclass: book-figure
   :alt: Contracts in source go through Clang verify and compile paths

|

Install
-------

.. tabs::

   .. tab:: macOS

      .. code-block:: bash

         brew install cmake ninja git
         git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
         cd cpp-verify
         ./setup.sh

      → ``build/bin/cpp-verify``, ``build/bin/clang++``

   .. tab:: Linux

      .. code-block:: bash

         sudo apt install cmake ninja-build build-essential git
         git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
         cd cpp-verify
         ./setup.sh

      → ``build/bin/cpp-verify``, ``build/bin/clang++``

   .. tab:: Windows

      Install `CMake <https://cmake.org/download/>`_, `Ninja <https://github.com/ninja-build/ninja/releases>`_,
      and `Git <https://git-scm.com/download/win>`_, plus **Visual Studio Build Tools** (C++ workload).

      .. code-block:: powershell

         git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
         cd cpp-verify
         .\setup.ps1

      → ``build\bin\cpp-verify.exe``, ``build\bin\clang++.exe``

Manual build (from repository root; same flags as ``setup.sh``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tabs::

   .. tab:: macOS / Linux

      .. code-block:: bash

         cmake -S llvm -B build -G Ninja \
           -DCMAKE_BUILD_TYPE=Release \
           -DLLVM_ENABLE_PROJECTS=clang \
           -DLLVM_TARGETS_TO_BUILD=Native \
           -DCPPVERIFY_VENDOR_Z3=ON \
           -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
         ninja -C build clang cpp-verify

   .. tab:: Windows (Ninja)

      .. code-block:: powershell

         cmake -S llvm -B build -G Ninja `
           -DCMAKE_BUILD_TYPE=Release `
           -DLLVM_ENABLE_PROJECTS=clang `
           -DLLVM_TARGETS_TO_BUILD=Native `
           -DCPPVERIFY_VENDOR_Z3=ON `
           -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
         cmake --build build --target clang cpp-verify -m

   .. tab:: Windows (Visual Studio)

      .. code-block:: powershell

         cmake -S llvm -B build `
           -G "Visual Studio 17 2022" -A x64 `
           -DLLVM_ENABLE_PROJECTS=clang `
           -DLLVM_TARGETS_TO_BUILD=Native `
           -DCPPVERIFY_VENDOR_Z3=ON `
           -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
         cmake --build build --config Release --target clang cpp-verify -m

Quick start
-----------

.. code-block:: cpp

   int abs(int x)
     pre(x >= -2147483647)   // every int except INT_MIN, whose negation overflows
     post(result >= 0)
   {
     return x < 0 ? -x : x;
   }

.. tabs::

   .. tab:: Verify

      .. code-block:: bash

         ./build/bin/cpp-verify abs.cpp

   .. tab:: Compile + verify

      .. code-block:: bash

         ./build/bin/clang++ -std=c++17 -fverify-contracts -c abs.cpp -o abs.o

Use ``-fverify-contracts`` on ``clang++`` so ``pre`` / ``post`` are keywords.
``cpp-verify`` adds that flag automatically.

Verified scalar lifetimes
~~~~~~~~~~~~~~~~~~~~~~~~~

CppVerify also tracks initialized local scalar ``new``/``delete`` lifetimes:

.. code-block:: cpp

   int roundtrip(int value) post(result == value) {
     int *p = new int;
     *p = value;
     int observed = *p;
     delete p;
     return observed;
   }

Use-after-delete, double-delete, overlapping live allocations, and reads before
initialization are proof failures. See :doc:`language/dynamic-storage` for the
current non-escaping subset.

Address-preserving scalar references
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contracted executable free functions may use scalar ``T&`` and ``const T&``
parameters:

.. code-block:: cpp

   void increment(int& value)
     pre(value < 2147483647)
     modifies(value)
     post(value == old(value) + 1)
   {
     ++value;
   }

Reference values lower to heap loads, writes lower to stores, and ``old`` reads
the entry heap. The bounded scalar slice supports direct forwarding, direct
``*p`` bindings, ordinary initialized scalar local actuals, and chained local
reference aliases. Subobjects, temporaries, reference returns, and non-scalar
referents remain fail-closed. See
:doc:`language/pointers`.

Backends and modular calls
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: bash

   cpp-verify --backend=bmc --unroll=3 loops.cpp
   cpp-verify --dump-ir=3,4 debug.cpp

See :doc:`book/part-ii/ch17-backends-modular-calls` for Z3 vs BMC vs Lean export and chained calls like ``f(g(x))``.

Learn more
----------

.. grid:: 1 2 2 3
   :gutter: 3

   .. grid-item-card:: 📘 The Book
      :link: book/index
      :link-type: doc

      Foundations (Part I) and using CppVerify on C++ (Part II).

   .. grid-item-card:: 📋 Language reference
      :link: language/index
      :link-type: doc

      Contract syntax and flags.

   .. grid-item-card:: 🔧 Verifier API
      :link: api/index
      :link-type: doc

      C++ headers in ``clang/lib/Verify`` (Doxygen).

`Source on GitHub <https://github.com/SwayamInSync/cpp-verify>`_

.. toctree::
   :hidden:
   :caption: Book
   :maxdepth: 2

   book/index

.. toctree::
   :hidden:
   :caption: Reference
   :maxdepth: 2

   language/index
   api/index