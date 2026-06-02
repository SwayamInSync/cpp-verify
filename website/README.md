# CppVerify documentation site

Dual build:

| Output | Tool | Path |
|--------|------|------|
| Book + language reference | **Sphinx** (Furo) | `website/build/` |
| C++ verifier API | **Doxygen** | `website/build/doxygen/` |

## Build

**Doxygen is required** for the C++ API (install once: `brew install doxygen` or `apt install doxygen`).

```bash
./website/scripts/build-docs.sh
open website/build/index.html          # book home
open website/build/doxygen/index.html  # C++ API
```

Auto-install Doxygen when possible: `AUTO_INSTALL_DOXYGEN=1 ./website/scripts/build-docs.sh`

## Structure

- `source/book/part-i/` — Foundations (Ch 1–8), no CppVerify syntax required first
- `source/book/part-ii/` — CppVerify practice (Ch 9–16)
- `source/language/` — Desk reference (syntax lookup)
- `source/api/` — Link page into Doxygen
- `doxygen/Doxyfile` — Scans `llvm-project/clang/lib/Verify/*.h`
- `source/_static/logo-todo.svg` — Replace with your logo when ready

## Replace logo

Drop your asset as `source/_static/logo.svg` and set in `conf.py`:

```python
"light_logo": "logo.svg",
"dark_logo": "logo.svg",
```