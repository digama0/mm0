import mm0.basic

namespace mm0

@[mm0 strict provable] def wff : Type := Prop
@[mm0 ax] def imp : wff → wff → wff := (→)
@[mm0 ax] def neg : wff → wff := not
attribute [mm0_alias neg] not
local infixr ` => `:30 := imp
local prefix `~` := neg
notation `wi` := imp
notation `wn` := neg

@[mm0 ax] theorem ax_1 {ph ps : wff} : ph => ps => ph := λ h _, h
@[mm0 ax] theorem ax_2 {ph ps ch : wff} :
  (ph => ps => ch) => (ph => ps) => ph => ch := λ h1 h2 h3, h1 h3 (h2 h3)
@[mm0 ax] theorem ax_3 {ph ps : wff} : (~ph => ~ps) => ps => ph :=
λ h1 h2, classical.by_contradiction $ λ h3, h1 h3 h2
@[mm0 ax] theorem ax_mp {ph ps : wff} : ph → (ph => ps) → ps := λ h1 h2, h2 h1

@[mm0] theorem a1i {ph ps: wff} (h : ph) : ps => ph := ax_mp h ax_1

@[mm0] def iff (ph ps : wff) := ~((ph => ps) => ~(ps => ph))
local infix ` <-> `:20 := iff

@[mm0] theorem a2i {ph ps ch: wff} (h: (imp ph (imp ps ch))):
  (imp (imp ph ps) (imp ph ch)) :=
(ax_mp h (ax_2 ))

@[mm0] theorem mpd {ph ps ch: wff}
  (h1: (imp ph ps)) (h2: (imp ph (imp ps ch))): (imp ph ch) :=
(ax_mp h1 (a2i h2))

@[mm0] theorem syl {ph ps ch: wff}
  (h1: (imp ph ps)) (h2: (imp ps ch)): (imp ph ch) :=
(mpd h1 (a1i h2))

@[mm0] theorem id (ph: wff): (imp ph ph) :=
(mpd (@ax_1 _ ph) ax_1)

@[mm0] theorem a1d {v0 v1 v2: wff}
  (v3: (wi v0 v1)): (wi v0 (wi v2 v1)) :=
(syl v3 (ax_1))

@[mm0] theorem sylcom {ph ps ch th: wff}
  (h1: (imp ph (imp ps ch))) (h2: (imp ps (imp ch th))): (imp ph (imp ps th)) :=
(syl h1 (a2i h2))

@[mm0] theorem syl6 {ph ps ch th: wff}
  (h1: (imp ph (imp ps ch))) (h2: (imp ch th)): (imp ph (imp ps th)) :=
(sylcom h1 (a1i h2))

/-
theorem con2d {v0 v1 v2: wff}
  (v3: (wi v0 (wi v1 (wn v2)))): (wi v0 (wi v2 (wn v1))) =
(con4d (syl5 (notnot2) v3))

theorem con2 (v0: wff) (v1: wff),: (wi (wi v0 (wn v1)) (wi v1 (wn v0))) =
(con2d [(wi v0 (wn v1))=v2] v0 v1 (id v2))

@[mm0] theorem mt2d {ph ps ch: wff}
  (h1: ph => ch) (h2: ph => ps => ~ch) : ph => ~ps :=
mpd _ (con2d _)

@[mm0] theorem nsyl3 {ph ps ch: wff}
  (h1: (imp ph (neg ps))) (h2: (imp ch ps)): (imp ch (neg ph)) :=
mt2d h2 (a1i h1)

@[mm0] theorem con2i (ph: wff) (ps: wff) (h: (imp ph (neg ps))): (imp ps (neg ph)) :=
(nsyl3 ph ps ps h (id ps))

@[mm0] theorem notnot1 (ph: wff): (imp ph (neg (neg ph))) :=
(con2i [(neg ph)=a] ph (id a))

@[mm0] theorem con4d {ph ps ch: wff}
  (h: (imp ph (imp (neg ps) (neg ch)))): (imp ph (imp ch ps)) :=
(syl ph (imp (neg ps) (neg ch)) (imp ch ps) h (ax_3 ps ch))

@[mm0] theorem con1d {ph ps ch: wff}
  (h: (imp ph (imp (neg ps) ch))): (imp ph (imp (neg ch) ps)) :=
(con4d ph ps [(neg ch)=a] (syl6 ph (neg ps) ch (neg a) h (notnot1 ch)))

@[mm0] theorem mt3d {ph ps ch: wff}
  (h1: (imp ph (neg ch))) (h2: (imp ph (imp (neg ps) ch))): (imp ph ps) :=
(mpd ph (neg ch) ps h1 (con1d ph ps ch h2))

@[mm0] theorem nsyl2 {ph ps ch: wff}
  (h1: (imp ph (neg ps))) (h2: (imp (neg ch) ps)): (imp ph ch) :=
(mt3d ph ch ps h1 (a1i (imp (neg ch) ps) ph h2))

@[mm0] theorem con1i (ph: wff) (ps: wff) (h: (imp (neg ph) ps)): (imp (neg ps) ph) :=
(nsyl2 [(neg ps)=a] ps ph (id a) h)

@[mm0] theorem pm2_21 (ph: wff) (ps: wff): (imp (neg ph) (imp ph ps)) :=
?

@[mm0] theorem simplim (ph: wff) (ps: wff): (imp (neg (imp ph ps)) ph) :=
(con1i ph (imp ph ps) (pm2_21 ph ps))
-/

def wb (ph: wff) (ps: wff): wff := (neg (imp (imp ph ps) (neg (imp ps ph))))

-- @[mm0] theorem bi1 {ph ps : wff} : (ph <-> ps) => ph => ps := _

@[mm0] def and (ph ps : wff) := ~(ph => ~ps)
@[mm0] def or (ph ps : wff) := ~ph => ps
@[mm0 ax] def tru : wff := true
@[mm0] def fal := ~tru

attribute [mm0] nat
@[mm0 ax] def al (ph : ∀ x : nat, wff) : wff := ∀ x, ph x
notation `⋀` binders `, ` r:(scoped f, al f) := r

@[mm0] def ex (ph : ∀ x : nat, wff) : wff := ~⋀ x, ~ph x
notation `⋁` binders `, ` r:(scoped f, ex f) := r

end mm0
