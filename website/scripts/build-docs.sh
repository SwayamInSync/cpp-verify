#!/usr/bin/env bash
# Build Sphinx site + Doxygen C++ API (both required).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WEB="$ROOT/website"
SRC="$WEB/source"
BUILD="$WEB/build"
DOXY="$WEB/doxygen"

ensure_doxygen() {
  if command -v doxygen >/dev/null 2>&1; then
    return 0
  fi

  # Auto-install in CI or when AUTO_INSTALL_DOXYGEN=1
  if [[ -n "${GITHUB_ACTIONS:-}" ]] || [[ "${AUTO_INSTALL_DOXYGEN:-0}" == "1" ]]; then
    case "$(uname -s)" in
      Darwin)
        if command -v brew >/dev/null 2>&1; then
          echo "==> Installing Doxygen (brew)…"
          brew install doxygen
        fi
        ;;
      Linux)
        if command -v apt-get >/dev/null 2>&1; then
          echo "==> Installing Doxygen (apt)…"
          sudo apt-get update -qq
          sudo apt-get install -y -qq doxygen
        fi
        ;;
    esac
  fi

  if command -v doxygen >/dev/null 2>&1; then
    return 0
  fi

  cat >&2 <<'EOF'
error: Doxygen is required to build the C++ API docs.

  macOS:   brew install doxygen
  Ubuntu:  sudo apt install doxygen
  Fedora:  sudo dnf install doxygen

Then rerun:  ./website/scripts/build-docs.sh

Or auto-install:  AUTO_INSTALL_DOXYGEN=1 ./website/scripts/build-docs.sh
EOF
  exit 1
}

verify_doxygen_output() {
  local index="$BUILD/doxygen/index.html"
  if [[ ! -f "$index" ]]; then
    echo "error: Doxygen did not produce $index" >&2
    exit 1
  fi
  local size
  size="$(wc -c < "$index" | tr -d ' ')"
  if [[ "$size" -lt 4096 ]]; then
    echo "error: Doxygen output looks like a stub (${size} bytes). Check Doxyfile and INPUT paths." >&2
    exit 1
  fi
}

cd "$ROOT"

echo "==> Doxygen (C++ API)"
ensure_doxygen
mkdir -p "$BUILD/doxygen"
rm -f "$BUILD/doxygen/index.html"  # remove stale placeholder if present
(cd "$DOXY" && doxygen Doxyfile)
verify_doxygen_output
echo "    API pages: $BUILD/doxygen/index.html"

echo "==> Sphinx (book + reference)"
pip install -q -r "$WEB/requirements.txt"
sphinx-build -W -b html "$SRC" "$BUILD"
python3 "$WEB/scripts/verify-book-sidebar.py"

# Sphinx does not remove doxygen/, but confirm it survived
verify_doxygen_output

echo "==> Done"
echo "    Site:  file://$BUILD/index.html"
echo "    API:   file://$BUILD/doxygen/index.html"