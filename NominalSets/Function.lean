import NominalSets.Prod

namespace NominalSets

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

lemma isSupportOf_function
    (A : Finset 𝔸) (f : X → Y)
    : IsSupportOf A f ↔ (∀π, (∀a ∈ A, π a = a) → ∀x, perm π (f x) = f (perm π x)) := by
  apply Iff.intro
  · intro ⟨hf⟩ π hπ x
    specialize hf π hπ
    nth_rw 2 [←hf]
    simp only [
      Function.perm_def, PermAction.perm_mul,
      inv_mul_cancel, PermAction.perm_one]
  · intro h
    constructor
    intro π hπ
    ext a
    simp only [
      Function.perm_def, h π hπ, PermAction.perm_mul,
      mul_inv_cancel, PermAction.perm_one]

@[simp]
lemma isSupported_iff_isSupportedF (f : X → Y) : IsSupported 𝔸 f ↔ IsSupportedF 𝔸 f := by
  simp only [isSupported_def, isSupportOf_function, isSupportedF_def]

@[fun_prop]
lemma isSupportedF_pi
    {f : X → Y → Z} (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    : IsSupportedF 𝔸 f := by
  obtain ⟨A, hA⟩ := hf
  use A
  intro π hπ x
  ext y
  simp only [Prod.forall] at hA
  simp (disch := grind) only [Function.perm_def, hA, perm_mul, mul_inv_cancel, perm_one]

@[simp]
lemma isSupportedF_pi_iff (f : X → Y → Z)
    : IsSupportedF 𝔸 f ↔ IsSupportedF 𝔸 fun (x, y) ↦ f x y := by
  apply Iff.intro
  · rintro ⟨A, hA⟩
    use A
    intro π hπ ⟨x, y⟩
    simp only [funext_iff, Function.perm_def] at hA
    specialize hA π hπ x (perm π y)
    simp only [perm_mul, inv_mul_cancel, perm_one] at hA
    exact hA
  · exact isSupportedF_pi

lemma isSupportOf_apply
    {A : Finset 𝔸} {f : X → Y} {x : X} (hf : IsSupportOf A f) (hx : IsSupportOf A x)
    : IsSupportOf A (f x) := by
  simp only [isSupportOf_def] at ⊢ hf hx
  intro π hπ
  replace hf := congr_fun (hf π hπ) (perm π x)
  specialize hx π hπ
  simp only [Function.perm_def, perm_mul, inv_mul_cancel, perm_one] at hf
  simp only [hf, hx]

lemma supp_apply [DecidableEq 𝔸] [Nominal 𝔸 X] [Nominal 𝔸 Y]
    (A : Finset 𝔸) (f : X → Y) (hf : IsSupportOf A f) (x : X)
    : supp 𝔸 (f x) \ supp 𝔸 x ⊆ A := by
  intro a ha
  simp only [Finset.mem_sdiff, mem_supp, not_forall] at ha
  rcases ha with ⟨hfx, B, hB, ha⟩
  by_contra ha'
  have : a ∉ A ∪ B := by grind
  apply this
  apply hfx
  apply isSupportOf_apply
  · exact isSupportOf_union_left hf
  · exact isSupportOf_union_right hB

end NominalSets
