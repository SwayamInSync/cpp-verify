#!/usr/bin/env bash
# Build the published site: the latest release at the root, each release
# series at /X.Y/ (its latest release, or its latest candidate before one),
# and this tree, the development version, at /dev/. A banner on every page
# says which version it documents.
#
# usage: build-site.sh [OUT]   (default: website/site)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:-$ROOT/website/site}"
SITE_URL="${CPPVERIFY_SITE_URL:-https://swayaminsync.github.io/cpp-verify}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

pip install -q -r "$ROOT/website/requirements.txt"

# Builds the documentation of the tree at $1 into $2: Doxygen, then Sphinx
# with the title and banner given, and the book's sidebar check.
build_tree() {
  local tree="$1" out="$2" title="$3" banner="$4"
  mkdir -p "$tree/website/build/doxygen"
  (cd "$tree/website/doxygen" && doxygen Doxyfile > /dev/null)
  sphinx-build -q -W -b html \
    -D "html_title=$title" \
    -D "html_theme_options.announcement=$banner" \
    "$tree/website/source" "$tree/website/build"
  python3 "$tree/website/scripts/verify-book-sidebar.py"
  mkdir -p "$out"
  cp -R "$tree/website/build/." "$out/"
}

# The release series and the tag each publishes, newest first, as
# "SERIES TAG" lines; a final release is preferred to its candidates.
releases="$(git -C "$ROOT" tag -l 'v[0-9]*' | python3 -c '
import re, sys
def key(tag):
    m = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)(?:-rc\.(\d+))?", tag)
    if not m:
        return None
    major, minor, patch, rc = m.groups()
    # A release sorts after its candidates.
    return (int(major), int(minor), int(patch), 1 if rc is None else 0,
            int(rc or 0))
latest = {}
for tag in sys.stdin.read().split():
    k = key(tag)
    if k and (k[:2] not in latest or k > latest[k[:2]][0]):
        latest[k[:2]] = (k, tag)
for series in sorted(latest, reverse=True):
    print("%d.%d %s" % (series + (latest[series][1],)))
')"
# The newest final release, documented at the root.
latest_tag="$(echo "$releases" | awk '$2 !~ /-rc\./ { print $2; exit }')"
latest="${latest_tag#v}"

rm -rf "$OUT"
mkdir -p "$OUT"

dev="$(sed -n 's/^set(CPPVERIFY_VERSION \(.*\))$/\1/p' "$ROOT/clang/CMakeLists.txt")"
if [[ -n "$latest" ]]; then
  dev_banner="This is the documentation of the development version, $dev, \
built from <code>main</code>. The latest release is $latest: \
<a href=\"$SITE_URL/\">its documentation</a>."
else
  dev_banner="This is the documentation of the development version, $dev, \
built from <code>main</code>."
fi
echo "==> dev: $dev"
build_tree "$ROOT" "$OUT/dev" "CppVerify $dev" "$dev_banner"

while read -r series tag; do
  [[ -n "$tag" ]] || continue
  version="${tag#v}"
  if [[ "$tag" == "$latest_tag" ]]; then
    banner="This is the documentation of cpp-verify $version, the latest \
release. <a href=\"$SITE_URL/dev/\">The development version</a> documents \
what <code>main</code> adds."
  else
    banner="This is the documentation of cpp-verify $version. The latest \
release is $latest: <a href=\"$SITE_URL/\">its documentation</a>."
  fi
  echo "==> $series: $tag"
  tree="$WORK/$tag"
  mkdir -p "$tree"
  git -C "$ROOT" archive "$tag" website docs clang/lib/Verify | tar -x -C "$tree"
  build_tree "$tree" "$OUT/$series" "CppVerify $version" "$banner"
  if [[ "$tag" == "$latest_tag" ]]; then
    cp -R "$OUT/$series/." "$OUT/"
  fi
done <<< "$releases"

# Before any release, the development version is the root.
if [[ -z "$latest" ]]; then
  cp -R "$OUT/dev/." "$OUT/"
fi

echo "==> Done"
echo "    Site:  file://$OUT/index.html"
