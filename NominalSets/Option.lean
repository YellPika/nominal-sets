import NominalSets.Prod

/-!
# Optional Types

This file formalizes definitions and results about permutations and supports for `Option` types.
-/


namespace NominalSets.Option

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

/-!
## Permutations
-/

@[simps -isSimp]
instance : PermAction 𝔸 (Option X) where
  perm π := Option.map (perm π)
  perm_one x := by cases x <;> simp only [Option.map_none, Option.map_some, perm_one]
  perm_mul π₁ π₂ x := by simp +unfoldPartialApp only [Option.map_map, Function.comp, perm_mul]

@[simp]
lemma perm_none (π : Perm 𝔸) : perm π (.none : Option X) = .none := by rfl

@[simp]
lemma perm_some
    (π : Perm 𝔸) (x : X)
    : perm π (.some x : Option X) = .some (perm π x) := by rfl

@[simp]
lemma perm_elim
    (π : Perm 𝔸) (z : Y) (f : X → Y) (x : Option X)
    : perm π (Option.elim x z f) = Option.elim (perm π x) (perm π z) (perm π f) := by
  cases x
  · simp only [Option.elim_none, perm_none]
  · simp only [Option.elim_some, perm_some, Function.perm_def, perm_mul, inv_mul_cancel, perm_one]

instance [DiscretePermAction 𝔸 X] : DiscretePermAction 𝔸 (Option X) where
  perm_discrete _ x := by
    ext
    cases x <;> simp only [Option.perm_none, Option.perm_some, perm_discrete]

/-!
## Supports
-/

@[simp]
lemma isSupportOf_none (A : Finset 𝔸) : IsSupportOf A (.none : Option X) := by
  simp only [isSupportOf_def, perm_none, implies_true]

@[simp]
lemma isSupportOf_some
    (A : Finset 𝔸) (x : X)
    : IsSupportOf A (.some x : Option X) ↔ IsSupportOf A x := by
  simp only [isSupportOf_def, perm_some, Option.some.injEq]

@[simp]
lemma isSupported_none : IsSupported 𝔸 (.none : Option X) := by
  simp only [isSupported_def, isSupportOf_none, exists_const]

@[simp]
lemma isSupported_some (x : X) : IsSupported 𝔸 (.some x : Option X) ↔ IsSupported 𝔸 x := by
  simp only [isSupported_def, isSupportOf_some]

instance [Nominal 𝔸 X] : Nominal 𝔸 (Option X) where
  supported x := by
    cases x
    · simp only [isSupported_none]
    · simp only [isSupported_some, Nominal.supported]

@[simp]
lemma supp_none [Nominal 𝔸 X] : supp 𝔸 (.none : Option X) = ∅ := by
  ext a
  simp only [mem_supp, isSupportOf_none, forall_const, Finset.notMem_empty, iff_false, not_forall]
  use ∅
  simp only [Finset.notMem_empty, not_false_eq_true]

@[simp]
lemma supp_some [Nominal 𝔸 X] (x : X) : supp 𝔸 (.some x : Option X) = supp 𝔸 x := by
  ext a
  simp only [mem_supp, isSupportOf_some]

@[simp, fun_prop]
lemma isSupportedF_none : IsSupportedF 𝔸 (fun _ : X ↦ (.none : Option Y)) := by
  use ∅
  simp only [implies_true, perm_none]

@[simp, fun_prop]
lemma isSupportedF_some : IsSupportedF 𝔸 (.some : X → Option X) := by
  use ∅
  simp only [implies_true, perm_some]

@[fun_prop]
lemma isSupportedF_elim
    {f : X → Option Y} (hf : IsSupportedF 𝔸 f)
    {g : X → Z} (hg : IsSupportedF 𝔸 g)
    {h : X → Y → Z} (hh : IsSupportedF 𝔸 fun (x, y) ↦ h x y)
    : IsSupportedF 𝔸 (fun x ↦ Option.elim (f x) (g x) (h x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨C, hC⟩ := hh
  use A ∪ B ∪ C
  intro π hπ x
  simp (disch := grind) only [← hA]
  cases f x with
  | none => simp (disch := grind) only [Option.elim_none, hB, perm_none]
  | some _ =>
    simp only [Prod.forall] at hC
    simp (disch := grind) only [Option.elim_some, hC, perm_some]

/-!
## Equivariance
-/

@[simp, fun_prop]
lemma equivariant_none : Equivariant 𝔸 (fun _ : X ↦ (.none : Option Y)) := by
  constructor
  simp only [implies_true, perm_none]

@[simp, fun_prop]
lemma equivariant_some : Equivariant 𝔸 (.some : X → Option X) := by
  constructor
  simp only [implies_true, perm_some]

@[fun_prop]
lemma equivariant_elim
    {f : X → Option Y} (hf : Equivariant 𝔸 f)
    {g : X → Z} (hg : Equivariant 𝔸 g)
    {h : X → Y → Z} (hh : Equivariant 𝔸 fun (x, y) ↦ h x y)
    : Equivariant 𝔸 (fun x ↦ Option.elim (f x) (g x) (h x)) := by
  constructor
  intro π x
  replace hh : perm π (h x) = h (perm π x) := by
    ext y
    replace hh := hh.eq
    simp only [Prod.forall] at hh
    simp only [Function.perm_def, hh, perm_mul, mul_inv_cancel, perm_one]
  simp only [perm_elim, hf.eq, hg.eq, hh]

end NominalSets.Option
