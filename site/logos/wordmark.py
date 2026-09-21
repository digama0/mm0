#!/usr/bin/env python3
"""Draw the readme leader: the mark locked up with 'Metamath Zero'.

The type is taken from the same font file the site serves (the upstream EB
Garamond variable font, instanced at the weight the page sets) and converted to
outlines here, so the readme and the site are the same drawing and neither
depends on a font being installed to be read.
"""
import os
from fontTools.ttLib import TTFont
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.boundsPen import BoundsPen
from fontTools.misc.transform import Transform

# EB Garamond is cut at two optical sizes, and this is the one for small text,
# which site/fonts/EBGaramond08.woff2 is also cut from: beside the text cut it
# carries a larger x-height and a heavier stem, and holds up where the other
# reads thin. Get it from the upstream project's built fonts
# (github.com/georgd/EB-Garamond, the `nightly` release, EBGaramond.zip) and
# put it beside this script. A font server asked for the family name may well
# hand you the text cut instead, which is a different drawing.
SRC = "EBGaramond08-Regular.otf"
TEXT = "Metamath Zero"
EM = 1000                   # the type is drawn at this size, as font units
BASELINE = 1000.0           # y of the baseline in the svg's own coordinates
OUT = os.path.dirname(os.path.abspath(__file__)) + "/"

# How much to close the M against the e, past what the font's own kerning does.
# Nothing. The M here has no right sidebearing at all, and the font kerns the
# pair a further 10, which leaves 13 units of ink between them, the tightest
# pair in the word (the rest run 27 to 47). An earlier version of this lockup
# took 60 more out of it, having been traced through inkscape, which set the e
# 78 units further out than the font's own metrics do.
KERN_ME = 0.0

# the lockup, in cap heights: the mark stands 1.55 caps tall, .85 of one clear
# of the word, its middle on the middle of the M
MARK_CAPS = 1.55
GAP_CAPS = 0.85

# the mark's own drawing region (mark.svg's viewBox)
MK_X, MK_Y, MK_W, MK_H = 59.75, 152.5, 1078.5, 895.0

font = TTFont(SRC)        # a single weight, so nothing to instance
glyphs = font.getGlyphSet()
cmap = font.getBestCmap()
hmtx = font["hmtx"]
names = [cmap[ord(c)] for c in TEXT]

def kern_pairs():
  """Every pair the font's `kern` feature adjusts, flattened."""
  pairs = {}
  for lookup in font["GPOS"].table.LookupList.Lookup:
    for st in lookup.SubTable:
      if getattr(st, "Format", None) == 1 and hasattr(st, "PairSet"):
        for first, ps in zip(st.Coverage.glyphs, st.PairSet):
          for rec in ps.PairValueRecord:
            v = getattr(rec.Value1, "XAdvance", 0) or 0
            if v: pairs[(first, rec.SecondGlyph)] = v
      elif getattr(st, "Format", None) == 2 and hasattr(st, "Class1Record"):
        c1 = st.ClassDef1.classDefs if st.ClassDef1 else {}
        c2 = st.ClassDef2.classDefs if st.ClassDef2 else {}
        for g1 in st.Coverage.glyphs:
          for g2 in c2:
            rec = st.Class1Record[c1.get(g1, 0)].Class2Record[c2.get(g2, 0)]
            v = getattr(rec.Value1, "XAdvance", 0) or 0
            if v: pairs.setdefault((g1, g2), v)
  return pairs

kerns = kern_pairs()

def cap_height():
  bp = BoundsPen(glyphs); glyphs[cmap[ord("M")]].draw(bp)
  return bp.bounds[3]

CAP = cap_height()
MARK_H = MARK_CAPS * CAP
GAP = GAP_CAPS * CAP

# where each glyph sits, and the path for the run that follows the M
pen_x, runs, x_first = 0.0, [], None
for i, name in enumerate(names):
  d = SVGPathPen(glyphs)
  # font units are y up from the baseline; the svg's are y down from its top
  glyphs[name].draw(TransformPen(d, Transform(1, 0, 0, -1, pen_x, BASELINE)))
  runs.append((name, d.getCommands()))
  adv = hmtx[name][0]
  if i + 1 < len(names):
    adv += kerns.get((name, names[i + 1]), 0)
    if TEXT[i] == "M": adv += KERN_ME
  pen_x += adv

def ink_bounds():
  """The drawn extent of the word, which is what the lockup is measured from."""
  x0 = y0 = 1e9; x1 = y1 = -1e9
  x = 0.0
  for i, name in enumerate(names):
    bp = BoundsPen(glyphs); glyphs[name].draw(bp)
    if bp.bounds:
      a, b, c, d2 = bp.bounds
      x0, x1 = min(x0, x + a), max(x1, x + c)
      y0, y1 = min(y0, b), max(y1, d2)
    adv = hmtx[name][0]
    if i + 1 < len(names):
      adv += kerns.get((name, names[i + 1]), 0)
      if TEXT[i] == "M": adv += KERN_ME
    x += adv
  return x0, x1, y0, y1

TEXT_X0, TEXT_X1, _, _ = ink_bounds()
TEXT_W = TEXT_X1 - TEXT_X0

s = MARK_H / MK_H
tx = -MK_X * s
cap_mid = BASELINE - CAP / 2
top = cap_mid - MARK_H / 2
ty = top - MK_Y * s
text_dx = MK_W * s + GAP - TEXT_X0
vb_w = MK_W * s + GAP + TEXT_W
vb = f"0 {top:.2f} {vb_w:.2f} {MARK_H:.2f}"

d_m = runs[0][1]
d_rest = " ".join(c for _, c in runs[1:])

TEMPLATE = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="{vb}" width="{w:.2f}" height="{h:.2f}"
     role="img" aria-label="Metamath Zero">
<title>Metamath Zero</title>
<!--
  The readme leader: the mark, then the name in EB Garamond 08, converted to
  outlines from the same font file site/fonts serves, so the two are one
  drawing and neither needs the font installed to be read.

    cap height     {cap:g} of the 1000 unit em, which the type is set at
    mark height    {mark_h:.2f}, {mark_caps:g} cap heights
    gap            {gap:.2f}, {gap_caps:g} of a cap height
    mark middle    on the middle of the M, at y {cap_mid:g}
    kern           the font's own: M against e comes out 13 units clear,
                   the tightest pair in the word, and wants nothing added

  width and height are the viewBox at a tenth, so that a viewer which sizes
  this by itself gets the lockup's proportions rather than the 300x150 an svg
  falls back to.

  {which}.
  README.md picks between the two with a <picture>, so neither file carries a
  media query of its own.
-->
<style>
  .t, .c {{ fill: none; stroke: {ink}; stroke-width: 120 }}
  .c {{ opacity: 0.45 }}
  .w {{ fill: {ink} }}
</style>
<defs>
  <clipPath id="w-out"><circle cx="600" cy="600" r="538.188"/></clipPath>
  <!-- the rect spares the apex, which stands 2.11 outside the circle at x=59.70 -->
  <clipPath id="w-chev">
    <circle cx="600" cy="600" r="538.188"/><rect width="150" height="1200"/>
  </clipPath>
  <clipPath id="w-in"><circle cx="600" cy="600" r="391.25"/></clipPath>
  <!-- maskUnits explicit: the default bounding-box region would crop the apex.
       The display cut, 38 clear of the stem: this is only ever drawn large. -->
  <mask id="w-clear" maskUnits="userSpaceOnUse" x="0" y="0" width="1200" height="1200">
    <rect width="1200" height="1200" fill="#fff"/>
    <rect x="502" width="197" height="1200" fill="#000"/>
  </mask>
</defs>
<g transform="translate({tx:.2f},{ty:.2f}) scale({s:.6f})">
  <line class="t" x1="600" y1="0" x2="600" y2="1200" clip-path="url(#w-in)"/>
  <line class="t" x1="600" y1="600" x2="1200" y2="600" clip-path="url(#w-out)"/>
  <polyline class="c" points="1087.25,120.2519 187.25,600 1087.25,1079.7481" stroke-linejoin="miter"
            clip-path="url(#w-chev)" mask="url(#w-clear)"/>
</g>
<path class="w" transform="translate({text_dx:.2f},0)" d="{d_m} {d_rest}"/>
</svg>
"""

for name, ink, which in [("wordmark.svg", "#2b2b2b", "The light theme file, dark ink"),
                         ("wordmark-dark.svg", "#d8d8d8", "The dark theme file, light ink")]:
  out = TEMPLATE.format(vb=vb, cap=CAP, mark_h=MARK_H, gap=GAP, cap_mid=cap_mid,
                        mark_caps=MARK_CAPS, gap_caps=GAP_CAPS,
                        ink=ink, which=which, tx=tx, ty=ty, s=s, text_dx=text_dx,
                        d_m=d_m, d_rest=d_rest, w=vb_w / 10, h=MARK_H / 10)
  assert "--" not in out[out.index("<!--") + 4:out.index("-->")], "double hyphen in XML comment"
  open(OUT + name, "w").write(out)
  print(name, len(out), "bytes")

print(f"cap {CAP:g}  viewBox {vb}  scale {s:.6f}  text_dx {text_dx:.2f}")
