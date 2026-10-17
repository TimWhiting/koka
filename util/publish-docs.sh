#!/bin/sh
# Publishes a documentation build (util/docs.kk --publish) into a checkout of
# the gh-pages branch.
#
#   util/publish-docs.sh <build-dir> <pages-dir> dev
#   util/publish-docs.sh <build-dir> <pages-dir> <tag> [latest]
#
# Layout of gh-pages (https://koka-lang.github.io/koka/...):
#
#   doc/           the newest stable release, the default that everything links to
#   stable/doc/    the newest stable release
#   dev/doc/       the dev branch
#   <tag>/doc/     every release tag, e.g. v3.2.9/doc/
#   versions.html  the list of all of them
#
# `latest` marks the tag as the newest stable release, which also publishes it
# to doc/ and stable/doc/. stable/, dev/ and a tag's directory are replaced on
# each publish; doc/ is copied over without deleting, so links to pages that a
# release dropped keep working. The pages link to each other relatively, so one
# build serves every location.
set -eu
build=$1; pages=$2; channel=$3; latest=${4:-}
[ -f "$build/book.html" ] || { echo "publish-docs: no book.html in $build" >&2; exit 1; }

# put <dir> [--delete]: copy the build to <dir>/doc, and let <dir>/ lead to it
put() {
  mkdir -p "$pages/$1/doc"
  rsync -a ${2:-} "$build/" "$pages/$1/doc/"
  if [ "$1" != . ]; then
    printf '%s\n' '<!DOCTYPE html><meta charset="utf-8"><meta http-equiv="refresh" content="0; url=doc/index.html"><a href="doc/index.html">Koka documentation</a>' > "$pages/$1/index.html"
  fi
}

case "$channel" in
  dev) put dev --delete ;;
  v*)
    put "$channel" --delete
    if [ "$latest" = latest ]; then
      put stable --delete
      echo "$channel" > "$pages/stable/version.txt"
      put .
    fi ;;
  *) echo "publish-docs: unknown channel $channel" >&2; exit 1 ;;
esac

# versions.html: every published version, newest first
stable=$(cat "$pages/stable/version.txt" 2>/dev/null || true)
{
  printf '%s\n' '<!DOCTYPE html>' '<html lang="en"><head><meta charset="utf-8">' \
    '<meta name="viewport" content="width=device-width, initial-scale=1">' \
    '<title>Koka documentation versions</title>' \
    '<style>body{font-family:system-ui,sans-serif;max-width:40em;margin:2em auto;padding:0 1em;line-height:1.6}li span{color:#777}</style>' \
    '</head><body><h1>Koka documentation</h1><ul>'
  [ -n "$stable" ] && printf '<li><a href="stable/doc/index.html">stable</a> <span>(%s)</span></li>\n' "$stable"
  [ -d "$pages/dev/doc" ] && printf '%s\n' '<li><a href="dev/doc/index.html">dev</a> <span>(development version)</span></li>'
  for d in $(cd "$pages" && ls -d v*/doc 2>/dev/null | sed 's|/doc$||' | sort -rV); do
    printf '<li><a href="%s/doc/index.html">%s</a></li>\n' "$d" "$d"
  done
  printf '%s\n' '</ul></body></html>'
} > "$pages/versions.html"
