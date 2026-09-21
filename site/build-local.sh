#!/usr/bin/env bash
# Assemble the full site locally -- the homepage at the root with the tools as
# siblings, exactly the layout the deployed site uses (digama0.github.io/mm0/)
# -- into ./_site, then serve it. Run from the `site/` directory.
#
#   ./build-local.sh            build what has changed, then serve on :8000
#   ./build-local.sh --homepage copy just the homepage in, then serve (instant)
#   ./build-local.sh --serve    serve ./_site as it stands, build nothing
#   ./build-local.sh --fast     as the default, but skip wasm-opt in /editor
#   ./build-local.sh --clean    discard ./_site and build everything again
#   ./build-local.sh --no-serve  build and stop, which is what CI deploys from
#   DOC_FILE=examples/set.mm1 ./build-local.sh   pick the docgen target
#
# Each part records a hash of its inputs, and is skipped when they have not
# changed. That matters because wasm-pack has no result cache of its own: it
# re-runs wasm-opt over the module on every invocation whether or not the wasm
# differs, which is three to five minutes on its own.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/.." && pwd)"
out="$here/_site"
stamps="$here/.stamps"        # build metadata, kept out of what gets published
port="${PORT:-8000}"
doc_file="${DOC_FILE:-examples/peano.mm1}"
fast=""
do_serve=1
# MM0RS points at a prebuilt binary, which is how CI reuses the one the rest of
# the workflow already built rather than compiling mm0-rs a second time.
mm0rs="${MM0RS:-$repo/mm0-rs/target/release/mm0-rs}"
# The libraries the explorer offers, built from examples/ at ship time. Keep in
# step with the data-example buttons in mm0-js/index.html.
mmb_examples="peano hol"

serve() { echo "serving $out on http://localhost:$port  (Ctrl-C to stop)"; cd "$out"; exec python3 -m http.server "$port"; }

homepage() {
  echo "==> homepage"
  mkdir -p "$out"
  cp "$here/index.html" "$here/style.css" "$out/"
  # the assets the page fetches: the favicon and the heading face. The mark
  # itself is inlined, and logos/ is a repo directory rather than something the
  # site serves. OFL.txt travels with the font, as its licence requires.
  cp "$here/favicon.svg" "$out/"
  mkdir -p "$out/fonts"; cp "$here"/fonts/* "$out/fonts/"
  cp "$here"/*.pdf "$out/"
}


case "${1:-}" in
  --serve)    serve ;;
  --homepage) homepage; serve ;;
  --clean)    rm -rf "$out" "$stamps" ;;
  --fast)     fast=1 ;;
  --no-serve) do_serve="" ;;
  "")         ;;
  *)          echo "unknown option: $1" >&2; exit 2 ;;
esac

# A part is rebuilt when the hash of everything it is built from changes.
stamp() { find "$@" -type f -print0 2>/dev/null | sort -z | xargs -0 sha1sum | sha1sum; }
changed() {           # changed <name> <hash> -- true if it differs from last time
  local f="$stamps/$1"
  [ -f "$f" ] && [ "$(cat "$f")" = "$2" ] && return 1
  return 0
}
mark() { mkdir -p "$stamps"; printf '%s' "$2" > "$stamps/$1"; }
need_mm0rs() {                                     # 'doc' is a default feature
  [ -n "${MM0RS:-}" ] && return 0
  ( cd "$repo/mm0-rs" && cargo build --release --locked )
}

homepage

h=$(stamp "$repo/m0e/src" "$repo/m0e/Cargo.toml" "$repo/m0e/package.json" \
          "$repo/m0e/webpack.config.js" "$repo/mm0-rs/src" "$repo/mm0-rs/components")"$fast"
if changed editor "$h" || [ ! -d "$out/m0e" ]; then
  echo "==> /m0e  (the editor, wasm)"
  [ -n "$fast" ] && echo "    (--fast: skipping wasm-opt; the wasm is larger but builds in seconds)"
  ( cd "$repo/m0e" && npm install --silent \
    && M0E_EXPLORER_URL=../mmb/ M0E_FAST="$fast" npm run build )
  rm -rf "$out/m0e"; cp -r "$repo/m0e/dist" "$out/m0e"
  mark editor "$h"
else
  echo "==> /m0e  (unchanged, skipped)"
fi

srcs=""; for n in $mmb_examples; do srcs="$srcs $repo/examples/$n.mm1"; done
h=$(stamp "$repo/mm0-js/src" "$repo/mm0-js/ui" "$repo/mm0-js/index.html" \
          "$repo/mm0-js/package.json" "$repo/mm0-rs/src" $srcs)
if changed mmb "$h" || [ ! -d "$out/mmb" ]; then
  echo "==> /mmb  (proof explorer)"
  ( cd "$repo/mm0-js" && npm install --silent && npm run build )
  rm -rf "$out/mmb"; mkdir -p "$out/mmb/dist" "$out/mmb/test"
  cp "$repo/mm0-js/index.html" "$out/mmb/"
  cp -r "$repo/mm0-js/ui"        "$out/mmb/ui"
  cp -r "$repo/mm0-js/dist/src"  "$out/mmb/dist/src"
  cp -r "$repo/mm0-js/dist/ui"   "$out/mmb/dist/ui"
  # The explorer's example buttons ask for test/<name>.mmb relative to itself.
  # Compile them from examples/ so the site ships what the sources say now;
  # mm0-js/test holds fixtures pinned for its unit suite, which is a different
  # thing. No -s: the explorer reads the index for declaration names.
  need_mm0rs
  for n in $mmb_examples; do
    echo "    compiling examples/$n.mm1"
    ( cd "$repo/examples" && "$mm0rs" compile "$n.mm1" "$out/mmb/test/$n.mmb" )
  done
  mark mmb "$h"
else
  echo "==> /mmb  (unchanged, skipped)"
fi

# Each docgen run lands under its own name, so doc/ can hold more than one set.
# The homepage links doc/peano/; DOC_FILE builds a different one beside it.
doc_name="$(basename "${doc_file%.*}")"
h=$(stamp "$repo/mm0-rs/src" "$repo/$doc_file")"$doc_file"
if changed "doc-$doc_name" "$h" || [ ! -d "$out/doc/$doc_name" ]; then
  echo "==> /doc/$doc_name  (docgen for $doc_file)"
  need_mm0rs
  rm -rf "$out/doc/$doc_name"; mkdir -p "$out/doc"
  ( cd "$repo" && "$mm0rs" doc "$doc_file" "$out/doc/$doc_name" )
  mark "doc-$doc_name" "$h"
else
  echo "==> /doc/$doc_name  (unchanged, skipped)"
fi

echo "==> done"
if [ -n "$do_serve" ]; then serve; fi
