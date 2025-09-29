import NominalSets.Support.Basic

/-!
# Product Types

This file formalizes definitions and results about permutations and supports for product types.
-/

namespace NominalSets.Prod

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

/-!
## Permutations
-/

@[simps -isSimp]
instance : PermAction 𝔸 (X × Y) where
  perm π x := (perm π x.1, perm π x.2)
  perm_one := by simp only [perm_one, Prod.mk.eta, implies_true]
  perm_mul := by simp only [perm_mul, implies_true]

@[simp]
lemma perm_mk (π : Perm 𝔸) (x : X) (y : Y) : perm π (x, y) = (perm π x, perm π y) := by rfl

@[simp]
lemma perm_fst (π : Perm 𝔸) (x : X × Y) : perm π (Prod.fst x) = Prod.fst (perm π x) := by
  cases x
  simp only [perm_mk]

@[simp]
lemma perm_snd (π : Perm 𝔸) (x : X × Y) : perm π (Prod.snd x) = Prod.snd (perm π x) := by
  cases x
  simp only [perm_mk]

instance [DiscretePermAction 𝔸 X] [DiscretePermAction 𝔸 Y] : DiscretePermAction 𝔸 (X × Y) where
  perm_discrete := by simp only [Prod.forall, Prod.perm_mk, perm_discrete, implies_true]

/-!
## Supports
-/

@[simp]
lemma isSupportOf_mk
    (A : Finset 𝔸) (x : X) (y : Y)
    : IsSupportOf A (x, y) ↔ IsSupportOf A x ∧ IsSupportOf A y := by
  simp only [isSupportOf_def, perm_def]
  grind

@[simp]
lemma isSupported_mk
    (x : X) (y : Y)
    : IsSupported 𝔸 (x, y) ↔ IsSupported 𝔸 x ∧ IsSupported 𝔸 y := by
  classical
  simp only [isSupported_def, isSupportOf_mk]
  apply Iff.intro
  · grind
  · rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
    use A ∪ B
    apply And.intro
    · exact isSupportOf_union_left hA
    · exact isSupportOf_union_right hB

instance [Nominal 𝔸 X] [Nominal 𝔸 Y] : Nominal 𝔸 (X × Y) where
  supported := by simp only [Prod.forall, isSupported_mk, Nominal.supported, and_self, implies_true]

@[simp]
lemma supp_mk
    [DecidableEq 𝔸] [Nominal 𝔸 X] [Nominal 𝔸 Y]
    (x : X) (y : Y)
    : supp 𝔸 (x, y) = supp 𝔸 x ∪ supp 𝔸 y := by
  ext a
  simp only [mem_supp, isSupportOf_mk, and_imp, Finset.mem_union]
  apply Iff.intro
  · intro h
    simp only [or_iff_not_imp_left, not_forall, forall_exists_index]
    intro A hA ha B hB
    specialize h (A ∪ B) (isSupportOf_union_left hA) (isSupportOf_union_right hB)
    grind
  · grind

@[simp, fun_prop]
lemma isSupportedF_fst : IsSupportedF 𝔸 (Prod.fst : X × Y → X) := by
  use ∅
  simp only [implies_true, perm_fst]

@[simp, fun_prop]
lemma isSupportedF_snd : IsSupportedF 𝔸 (Prod.snd : X × Y → Y) := by
  use ∅
  simp only [implies_true, perm_snd]

@[fun_prop]
lemma isSupportedF_mk
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    {g : X → Z} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ (f x, g x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  intros
  simp (disch := grind) only [perm_mk, hA, hB]

/-!
## Equivariance
-/

@[simp, fun_prop]
lemma equivariant_fst : Equivariant 𝔸 (Prod.fst : X × Y → X) := by
  constructor
  simp only [implies_true, perm_fst]

@[simp, fun_prop]
lemma equivariant_snd : Equivariant 𝔸 (Prod.snd : X × Y → Y) := by
  constructor
  simp only [implies_true, perm_snd]

@[fun_prop]
lemma equivariant_mk
    {f : X → Y} (hf : Equivariant 𝔸 f)
    {g : X → Z} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (fun x ↦ (f x, g x)) := by
  constructor
  simp (disch := grind) only [perm_mk, hf.eq, hg.eq, implies_true]

end NominalSets.Prod
