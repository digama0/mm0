## The Metamath Zero homepage

The landing page for the language: a self-contained static site (`index.html` +
`style.css`, no build step, no external requests). It is the front door that
routes to the pieces that already exist -- install instructions, the language
docs, and the three in-browser tools.

### Deploy layout

The page is written to be the **root** of the deployed site, with the tools as
siblings, which is how GitHub Pages already serves the repo
(`digama0.github.io/mm0/`). The links in `index.html` assume:

```
/                 this page (index.html, style.css, favicon.svg)
/thesis.pdf       the thesis, and thesis-slides.pdf beside it
/m0e/             the m0e editor         (m0e:     npm run build -> m0e/dist)
/mmb/             the MMB proof explorer (mm0-js:  its dist/, plus libraries
                                          compiled from examples/)
/doc/peano/       generated docs         (mm0-rs doc examples/peano.mm1)
```

`build-local.sh` assembles that tree and serves it, and is what CI deploys from
(`--no-serve`). Each part is skipped when its inputs have not changed, so a
second run costs seconds; `--homepage` rebuilds only this page, which has no
build step at all.

### The editor -> explorer handoff

`m0e` no longer bundles the explorer. It links to one only when built with
`M0E_EXPLORER_URL` set (there is no default -- unset means the "open in explorer"
button is dropped). For this layout the editor is built with the explorer one
level up:

```sh
cd ../m0e
M0E_EXPLORER_URL=../mmb/ npm run build
```

The handoff writes the compiled `.mmb` into a per-origin IndexedDB store and
navigates to `../mmb/#/<name>`; because the store is keyed by origin, not path,
`/editor` and `/mmb` share it.

### Editing

Open `index.html` directly, or serve the folder (`python3 -m http.server`) so the
relative `style.css` loads. The `⊢`, the theme toggle, the base16 semantic
palette (term = blue, axiom = orange, theorem = purple, sort/hypothesis = green)
and the light/dark handling all match the explorer, on purpose.
