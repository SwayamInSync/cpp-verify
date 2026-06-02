# CppVerify documentation site

Published at [swayaminsync.github.io/cpp-verify](https://swayaminsync.github.io/cpp-verify/).

## Outputs

| Output | Tool | Location |
|--------|------|----------|
| Book + language reference | Sphinx (Furo) | `website/build/` |
| C++ verifier API | Doxygen | `website/build/doxygen/` |

## Build (from repository root)

Doxygen is required for the C++ API (`brew install doxygen` or `apt install doxygen`).

```bash
./website/scripts/build-docs.sh
open website/build/index.html
open website/build/doxygen/index.html
```

Auto-install Doxygen when possible:

```bash
AUTO_INSTALL_DOXYGEN=1 ./website/scripts/build-docs.sh
```

## Structure

| Path | Content |
|------|---------|
| `source/index.rst` | Home — install, quick start, links |
| `source/book/part-i/` | Foundations (Ch 1–8) |
| `source/book/part-ii/` | CppVerify practice (Ch 9–17) |
| `source/language/` | Contract syntax reference |
| `source/api/` | Link into Doxygen |
| `source/_static/` | Logos, diagrams, `custom.css` |
| `doxygen/Doxyfile` | Scans `clang/lib/Verify` headers |

## Branding

Logos live in `source/_static/` (`logo.svg`, `logo-dark.svg`, `favicon.svg`). The product repo also ships PNGs under top-level `logos/` for the GitHub README.

## RST tables

Use ``.. list-table::`` with ``:header-rows: 1`` and ``:widths:``. Avoid grid tables (``+---+``) — they break easily when column widths do not match exactly.