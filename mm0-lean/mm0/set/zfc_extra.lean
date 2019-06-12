import set_theory.zfc data.quot

namespace Set

noncomputable def image' (f : Set → Set) : Set → Set :=
@image f (classical.all_definable _)

@[simp] theorem mem_image' {f : Set → Set} {x y : Set} :
  y ∈ image' f x ↔ ∃z ∈ x, f z = y := by apply mem_image

noncomputable def range {α : Type*} (f : α → Set) : Set :=
Set.mk $ pSet.mk _ (λ x, (f x).out)

@[simp] theorem mem_range {α : Type*} {f : α → Set} {x : Set} :
  x ∈ range f ↔ ∃ i, f i = x :=
quotient.induction_on x $ λ x, exists_congr $ λ i,
  show x ≈ quotient.out (f i) ↔ f i = ⟦x⟧,
  by rw [← quotient.eq, eq_comm, quotient.out_eq]

noncomputable def Union' {α : Type*} (S : α → Set) : Set := Union (range S)

@[simp] theorem mem_Union' {α : Type*} {S : α → Set} {x : Set} :
  x ∈ Union' S ↔ ∃ i, x ∈ S i :=
by simp [Union']; exact
  ⟨λ ⟨_, ⟨i, rfl⟩, h⟩, ⟨i, h⟩, λ ⟨i, h⟩, ⟨_, ⟨i, rfl⟩, h⟩⟩

end Set

instance : has_ssubset Class := by dunfold Class; apply_instance
