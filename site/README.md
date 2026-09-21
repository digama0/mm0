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
/                 this page (index.html, style.css, favicon.svg, fonts/)
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

### The heading face

`fonts/EBGaramond08.woff2` (39 KB) is what the headings and the name in the nav
and the footer are set in: the same face, at the same weight, that the readme's
wordmark is drawn from.

EB Garamond is cut at two optical sizes, and this is the one for small text.
Beside the text cut it carries an x-height .71 of its cap height against .62,
and a stem 22% heavier; at the sizes this page sets, the text cut reads thin
and this one holds up. They are different drawings, not one scaled, and a font
server asked for the family name may hand you either.

It is held here rather than fetched from a font service: the page makes no
third party requests, and a visitor's browser does not have to reach a second
origin before the headings can settle. `OFL.txt` beside it is the licence it
comes under, which requires that it travel with the font.

The file is a subset, cut down to latin, latin-1 and the punctuation a heading
can hold. Rebuild it from the upstream project's built fonts
([georgd/EB-Garamond](https://github.com/georgd/EB-Garamond), the `nightly`
release, `EBGaramond.zip`) with:

```sh
python3 -c '
from fontTools.ttLib import TTFont
from fontTools.subset import Subsetter, Options
f = TTFont("EBGaramond08-Regular.otf")
o = Options(); o.flavor = "woff2"; o.hinting = False
o.layout_features = ["kern", "liga", "calt", "ccmp", "locl"]
o.name_IDs = [0, 1, 2, 3, 4, 6, 13, 14]; o.name_legacy = False
s = Subsetter(options=o)
s.populate(unicodes=[*range(0x20, 0x7f), *range(0xa0, 0x100),
                     0x2013, 0x2014, 0x2018, 0x2019, 0x201c, 0x201d,
                     0x2022, 0x2026, 0x2039, 0x203a, 0x2192, 0x2212, 0x00d7])
s.subset(f); f.save("fonts/EBGaramond08.woff2")'
```

`logos/wordmark.py` draws the readme's lockup from that same file, so the two
are one drawing.

Headings carry no `letter-spacing`: any value but `normal` turns ligatures off
in blink, which costs the `fi` in a word like "Specifications". Nor any
`font-weight`: the file holds one weight, and asking for another gets a
synthesized bold.

The three faces divide the page: the serif for headings and the name, the sans
for everything you read or click, and the mono for what is code, which is code
samples, file and command names, and the MM0/MM1/MMB/MMC labels.

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
