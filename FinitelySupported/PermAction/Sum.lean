import FinitelySupported.PermAction.Prod

namespace PermAction.Sum

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

@[simps]
instance : PermAction 𝔸 (X ⊕ Y) where
  perm π := Sum.map (perm π) (perm π)
  perm_one := by simp only [Sum.forall, Sum.map_inl, perm_one, implies_true, Sum.map_inr, and_self]
  perm_mul := by simp only [
    Sum.map_map, Sum.forall, Sum.map_inl, Function.comp_apply,
    perm_mul, implies_true, Sum.map_inr, and_self]

@[simp]
lemma isHom_inl : IsHom 𝔸 (Sum.inl : X → X ⊕ Y) := by
  use ∅
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, perm_def, Sum.map_inl]

@[fun_prop]
lemma isHom_inl' {f : X → Y} (hf : IsHom 𝔸 f) : IsHom 𝔸 (fun x ↦ (Sum.inl (f x) : Y ⊕ Z)) :=
  isHom_comp' isHom_inl hf

@[simp]
lemma isHom_inr : IsHom 𝔸 (Sum.inr : Y → X ⊕ Y) := by
  use ∅
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, perm_def, Sum.map_inr]

@[fun_prop]
lemma isHom_inr' {f : X → Z} (hf : IsHom 𝔸 f) : IsHom 𝔸 (fun x ↦ (Sum.inr (f x) : Y ⊕ Z)) :=
  isHom_comp' isHom_inr hf

@[fun_prop]
lemma isHom_elim
    {f : X → Y → W} (hf : IsHom 𝔸 fun (x, y) ↦ f x y)
    {g : X → Z → W} (hg : IsHom 𝔸 fun (x, y) ↦ g x y)
    {h : X → Y ⊕ Z} (hh : IsHom 𝔸 h)
    : IsHom 𝔸 (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  classical
  rcases hf with ⟨A, hA⟩
  rcases hg with ⟨B, hB⟩
  rcases hh with ⟨C, hC⟩
  use A ∪ B ∪ C
  intros π x hπ
  simp (disch := grind) only [← hC, perm_def]
  simp only [Prod.forall] at hA hB
  cases h x with
  | inl _ => simp (disch := grind) only [Sum.elim_inl, hA, Sum.map_inl]
  | inr _ => simp (disch := grind) only [Sum.elim_inr, hB, Sum.map_inr]

@[simp]
lemma isSupp_iff (A : Finset 𝔸) (x : X ⊕ Y) : IsSupp A x ↔ Sum.elim (IsSupp A) (IsSupp A) x := by
  apply Iff.intro
  · intro ⟨h⟩
    simp only [perm_def] at h
    cases x with
    | inl x =>
      simp only [Sum.elim_inl]
      constructor
      grind
    | inr x =>
      simp only [Sum.elim_inr]
      constructor
      grind
  · cases x with
    | inl x =>
      simp only [Sum.elim_inl]
      rintro ⟨h⟩
      constructor
      simp only [perm_def, Sum.map_inl, Sum.inl.injEq]
      exact h
    | inr x =>
      simp only [Sum.elim_inr]
      rintro ⟨h⟩
      constructor
      simp only [perm_def, Sum.map_inr, Sum.inr.injEq]
      exact h

end PermAction.Sum
