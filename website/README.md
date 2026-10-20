# CppVerify documentation site

Published at [swayaminsync.github.io/cpp-verify](https://swayaminsync.github.io/cpp-verify/):

| Path | Documents | Built from |
|------|-----------|------------|
| `/` | The latest release | Its tag |
| `/X.Y/` | Release series X.Y (`/0.1/`) | The series' latest tag; before its release, its latest candidate |
| `/dev/` | The development version | `main` |

A banner on every page names the version and links to the others.
`scripts/build-site.sh` builds all of them into `website/site/` (each tag from
`git archive`, so tags must be fetched), and `cppverify-docs.yml` publishes
it whenever `main` changes. Only `main` may deploy, so publishing a release
(`cppverify-release.yml`) runs that workflow on `main` to add the new tag.

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

The whole site, every version:

```bash
./website/scripts/build-site.sh
open website/site/index.html
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