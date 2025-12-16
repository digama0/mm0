import set_theory.zfc.basic data.quot

namespace Set

noncomputable def image' (f : Set → Set) : Set → Set :=
@image f (classical.all_definable _)

@[simp] theorem mem_image' {f : Set → Set} {x y : Set} :
  y ∈ image' f x ↔ ∃z ∈ x, f z = y := by apply mem_image

noncomputable def Union' {α : Type*} (S : α → Set) : Set := sUnion (range S)

@[simp] theorem mem_Union' {α : Type*} {S : α → Set} {x : Set} :
  x ∈ Union' S ↔ ∃ i, x ∈ S i :=
by simp [Union']; exact
  ⟨λ ⟨_, ⟨i, rfl⟩, h⟩, ⟨i, h⟩, λ ⟨i, h⟩, ⟨_, ⟨i, rfl⟩, h⟩⟩

end Set

instance : has_ssubset Class := by dunfold Class; apply_instance

namespace Class
universe u

@[simp] theorem mem_hom_left (x : Set.{u}) (A : Class.{u}) : (x : Class.{u}) ∈ A ↔ A x :=
to_Set_of_Set _ _

@[simp] theorem mem_hom_right (x y : Set.{u}) : (y : Class.{u}) x ↔ x ∈ y := iff.rfl

@[simp] theorem ssubset_iff : ∀ {x y : Class.{u}}, x ⊂ y ↔ x ⊆ y ∧ x ≠ y :=
  λ x y : set Set, show x ⊂ y ↔ x ⊆ y ∧ x ≠ y, from ssubset_iff_subset_ne

end Class
