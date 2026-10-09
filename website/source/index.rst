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

Each `release <https://github.com/SwayamInSync/cpp-verify/releases>`_ has
archives for Linux x86_64 and macOS arm64: unpack one and run
``bin/cpp-verify --version``. The macOS binaries are not notarized; if macOS
refuses to open one downloaded with a browser, remove the quarantine mark with
``xattr -dr com.apple.quarantine`` on the unpacked directory. To build from
source:

.. tabs::

   .. tab:: macOS

      .. code-block:: bash

         brew install cmake ninja git
         git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
         cd cpp-verify
         ./setup.sh

      → ``build/bin/cpp-verify``, ``build/bin/clang++``, ``build/bin/clangd``, ``build/bin/clang-format``

   .. tab:: Linux

      .. code-block:: bash

         sudo apt install cmake ninja-build build-essential git
         git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
         cd cpp-verify
         ./setup.sh

      → ``build/bin/cpp-verify``, ``build/bin/clang++``, ``build/bin/clangd``, ``build/bin/clang-format``

   .. tab:: Windows

      Install `CMake <https://cmake.org/download/>`_, `Ninja <https://github.com/ninja-build/ninja/releases>`_,
      `Git <https://git-scm.com/download/win>`_, and `Python 3 <https://www.python.org/downloads/windows/>`_,
      plus **Visual Studio Build Tools** (C++ workload). Run the commands from an x64 Developer
      PowerShell for VS 2022 (or an x64 Native Tools prompt) so that CMake finds the compiler, or
      pass ``-Generator "Visual Studio 17 2022"`` to ``setup.ps1``.

      .. code-block:: powershell

         git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
         cd cpp-verify
         .\setup.ps1

      → ``build\bin\cpp-verify.exe``, ``build\bin\clang++.exe``, ``build\bin\clangd.exe``, ``build\bin\clang-format.exe``

Manual build (from repository root; same flags as ``setup.sh``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

On macOS, also pass ``-DCLANG_USE_XCSELECT=ON``, as ``setup.sh`` does, so that the
built ``clang++`` finds the SDK without ``SDKROOT``.

.. tabs::

   .. tab:: macOS / Linux

      .. code-block:: bash

         cmake -S llvm -B build -G Ninja \
           -DCMAKE_BUILD_TYPE=Release \
           -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra" \
           -DLLVM_TARGETS_TO_BUILD=Native \
           -DCPPVERIFY_VENDOR_Z3=ON \
           -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
         ninja -C build clang cpp-verify clangd clang-format

   .. tab:: Windows (Ninja)

      .. code-block:: powershell

         cmake -S llvm -B build -G Ninja `
           -DCMAKE_BUILD_TYPE=Release `
           -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra" `
           -DLLVM_TARGETS_TO_BUILD=Native `
           -DCPPVERIFY_VENDOR_Z3=ON `
           -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
         cmake --build build --target clang cpp-verify clangd clang-format --parallel

   .. tab:: Windows (Visual Studio)

      .. code-block:: powershell

         cmake -S llvm -B build `
           -G "Visual Studio 17 2022" -A x64 `
           -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra" `
           -DLLVM_TARGETS_TO_BUILD=Native `
           -DCPPVERIFY_VENDOR_Z3=ON `
           -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
         cmake --build build --config Release --target clang cpp-verify clangd clang-format --parallel

Quick start
-----------

.. code-block:: cpp

   int abs(int x)
     cppverify::pre(x >= -2147483647)   // every int except INT_MIN, whose negation overflows
     cppverify::post(cppverify::result >= 0)
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

Use ``-fverify-contracts`` on ``clang++`` so the constructs (``cppverify::pre``,
``cppverify::post``, ...) are recognized. ``cpp-verify`` adds that flag automatically.
Every construct is written qualified; the examples below use the alias that a
file declares with ``namespace cv = cppverify;``.

Verified scalar lifetimes
~~~~~~~~~~~~~~~~~~~~~~~~~

CppVerify also tracks initialized local scalar ``new``/``delete`` lifetimes:

.. code-block:: cpp

   namespace cv = cppverify;

   int roundtrip(int value) cv::post(cv::result == value) {
     int *p = new int;
     *p = value;
     int observed = *p;
     delete p;
     return observed;
   }

Use-after-delete, double-delete, overlapping live allocations, and reads before
initialization are proof failures. See :doc:`language/dynamic-storage` for the
bounded local and inferred fresh-owned factory subset.

Address-preserving scalar references
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contracted executable free functions may use scalar ``T&`` and ``const T&``
parameters:

.. code-block:: cpp

   namespace cv = cppverify;

   void increment(int& value)
     cv::pre(value < 2147483647)
     cv::modifies(value)
     cv::post(value == cv::old(value) + 1)
   {
     ++value;
   }

Reference values lower to heap loads, writes lower to stores, and ``cppverify::old`` reads
the entry heap. The bounded scalar slice supports direct forwarding, direct
``*p`` bindings, fields and elements of local objects and of parameter buffers,
ordinary initialized scalar local actuals, and chained local reference aliases.
Conditional bindings, temporaries, reference returns, and non-scalar referents
remain fail-closed. See
:doc:`language/pointers`.

Backends and modular calls
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: bash

   cpp-verify --backend=portfolio --cvc5-path=/usr/bin/cvc5 critical.cpp
   cpp-verify --backend=bmc --unroll=3 loops.cpp
   cpp-verify --lean-fallback=proof hard_goal.cpp
   cpp-verify --dump-ir=3,4 debug.cpp
   cpp-verify --lower-only --obligation-out=goals.cpv debug.cpp
   cpp-verify --obligation-in=goals.cpv --backend=z3

See :doc:`book/part-ii/ch17-backends-modular-calls` for Z3, bounded analysis,
editable Lean certification, and chained calls like ``f(g(x))``.

Learn more
----------

.. grid:: 1 2 2 4
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

   .. grid-item-card:: Case studies
      :link: case-studies/index
      :link-type: doc

      LLVM ULEB128, UTF-8 validation, and binary search.

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

.. toctree::
   :hidden:
   :caption: Case studies
   :maxdepth: 2

   case-studies/index

.. toctree::
   :hidden:
   :caption: Releases
   :maxdepth: 1

   release-notes
