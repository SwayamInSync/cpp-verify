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

Manual build (same CMake flags)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
     pre(true)
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