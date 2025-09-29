import NominalSets.Prod

/-!
# Sum Types

This file formalizes definitions and results about permutations and supports for sum types.
-/

namespace NominalSets.Sum

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

/-!
## Permutations
-/

@[simps -isSimp]
instance : PermAction 𝔸 (X ⊕ Y) where
  perm π := Sum.map (perm π) (perm π)
  perm_one := by simp only [
    Sum.forall, Sum.map_inl, perm_one,
    implies_true, Sum.map_inr, and_self]
  perm_mul := by simp only [
    Sum.map_map, Sum.forall, Sum.map_inl, Function.comp_apply,
    perm_mul, implies_true, Sum.map_inr, and_self]

@[simp]
lemma perm_inl (π : Perm 𝔸) (x : X) : perm π (.inl x : X ⊕ Y) = .inl (perm π x) := by rfl

@[simp]
lemma perm_inr (π : Perm 𝔸) (x : Y) : perm π (.inr x : X ⊕ Y) = .inr (perm π x) := by rfl

@[simp]
lemma perm_elim
    (π : Perm 𝔸) (f : X → Z) (g : Y → Z) (x : X ⊕ Y)
    : perm π (Sum.elim f g x) = Sum.elim (perm π f) (perm π g) (perm π x) := by
  cases x
  · simp only [Sum.elim_inl, perm_inl, Function.perm_def, perm_mul, inv_mul_cancel, perm_one]
  · simp only [Sum.elim_inr, perm_inr, Function.perm_def, perm_mul, inv_mul_cancel, perm_one]

instance [DiscretePermAction 𝔸 X] [DiscretePermAction 𝔸 Y] : DiscretePermAction 𝔸 (X ⊕ Y) where
  perm_discrete := by
    simp only [Sum.forall, Sum.perm_inl, perm_discrete, implies_true, Sum.perm_inr, and_self]

/-!
## Supports
-/

@[simp]
lemma isSupportOf_inl
    (A : Finset 𝔸) (x : X)
    : IsSupportOf A (.inl x : X ⊕ Y) ↔ IsSupportOf A x := by
  simp only [isSupportOf_def, perm_inl, Sum.inl.injEq]

@[simp]
lemma isSupportOf_inr
    (A : Finset 𝔸) (x : Y)
    : IsSupportOf A (.inr x : X ⊕ Y) ↔ IsSupportOf A x := by
  simp only [isSupportOf_def, perm_inr, Sum.inr.injEq]

@[simp]
lemma isSupported_inl (x : X) : IsSupported 𝔸 (.inl x : X ⊕ Y) ↔ IsSupported 𝔸 x := by
  simp only [isSupported_def, isSupportOf_inl]

@[simp]
lemma isSupported_inr (x : Y) : IsSupported 𝔸 (.inr x : X ⊕ Y) ↔ IsSupported 𝔸 x := by
  simp only [isSupported_def, isSupportOf_inr]

instance [Nominal 𝔸 X] [Nominal 𝔸 Y] : Nominal 𝔸 (X ⊕ Y) where
  supported := by simp only [
    Sum.forall, isSupported_inl, Nominal.supported,
    implies_true, isSupported_inr, and_self]

@[simp]
lemma supp_inl [Nominal 𝔸 X] [Nominal 𝔸 Y] (x) : supp 𝔸 (.inl x : X ⊕ Y) = supp 𝔸 x := by
  ext a
  simp only [mem_supp, isSupportOf_inl]

@[simp]
lemma supp_inr [Nominal 𝔸 X] [Nominal 𝔸 Y] (x) : supp 𝔸 (.inr x : X ⊕ Y) = supp 𝔸 x := by
  ext a
  simp only [mem_supp, isSupportOf_inr]

@[simp, fun_prop]
lemma isSupportedF_inl : IsSupportedF 𝔸 (.inl : X → X ⊕ Y) := by
  use ∅
  simp only [implies_true, perm_inl]

@[simp, fun_prop]
lemma isSupportedF_inr : IsSupportedF 𝔸 (.inr : Y → X ⊕ Y) := by
  use ∅
  simp only [implies_true, perm_inr]

@[fun_prop]
lemma isSupportedF_elim
    {f : X → Y → W} (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    {g : X → Z → W} (hg : IsSupportedF 𝔸 fun (x, y) ↦ g x y)
    {h : X → Y ⊕ Z} (hh : IsSupportedF 𝔸 h)
    : IsSupportedF 𝔸 (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨C, hC⟩ := hh
  use A ∪ B ∪ C
  intro π hπ x
  replace hA : perm π (f x) = f (perm π x) := by
    ext y
    simp only [Prod.forall] at hA
    simp (disch := grind) only [Function.perm_def, hA, perm_mul, mul_inv_cancel, perm_one]
  replace hB : perm π (g x) = g (perm π x) := by
    ext y
    simp only [Prod.forall] at hB
    simp (disch := grind) only [Function.perm_def, hB, perm_mul, mul_inv_cancel, perm_one]
  simp (disch := grind) only [perm_elim, hA, hB, hC]

/-!
## Equivariance
-/

@[simp, fun_prop]
lemma equivariant_inl : Equivariant 𝔸 (.inl : X → X ⊕ Y) := by
  constructor
  simp only [implies_true, perm_inl]

@[simp, fun_prop]
lemma equivariant_inr : Equivariant 𝔸 (.inr : Y → X ⊕ Y) := by
  constructor
  simp only [implies_true, perm_inr]

@[fun_prop]
lemma equivariant_elim
    {f : X → Y → W} (hf : Equivariant 𝔸 fun (x, y) ↦ f x y)
    {g : X → Z → W} (hg : Equivariant 𝔸 fun (x, y) ↦ g x y)
    {h : X → Y ⊕ Z} (hh : Equivariant 𝔸 h)
    : Equivariant 𝔸 (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  constructor
  intro π x
  replace hf : perm π (f x) = f (perm π x) := by
    ext y
    replace ⟨hf⟩ := hf
    simp only [Prod.forall] at hf
    simp (disch := grind) only [Function.perm_def, hf, perm_mul, mul_inv_cancel, perm_one]
  replace hg : perm π (g x) = g (perm π x) := by
    ext y
    replace ⟨hg⟩ := hg
    simp only [Prod.forall] at hg
    simp (disch := grind) only [Function.perm_def, hg, perm_mul, mul_inv_cancel, perm_one]
  simp only [perm_elim, hf, hg, hh.eq]

end NominalSets.Sum
