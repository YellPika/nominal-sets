import FinitelySupported.PermAction.Prod

namespace PermAction.Function

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

@[simps]
instance : PermAction 𝔸 (X → Y) where
  perm π f x := perm π (f (perm π⁻¹ x))
  perm_one f := by simp only [Perm.inv_one, perm_one]
  perm_mul := by simp only [perm_mul, mul_inv_rev, implies_true]

@[fun_prop]
lemma isHom_pi {f : X → Y → Z} (hf : IsHom 𝔸 (fun x : X × Y ↦ f x.1 x.2)) : IsHom 𝔸 f := by
  obtain ⟨A, hA⟩ := hf
  use A
  intro π x hπ
  ext y
  specialize hA π (x, perm π⁻¹ y) hπ
  simp only [Prod.perm_def, perm_mul, mul_inv_cancel, perm_one, perm_def] at ⊢ hA
  exact hA

@[simp]
lemma isHom_pi_iff {f : X → Y → Z} : IsHom 𝔸 (fun x : X × Y ↦ f x.1 x.2) ↔ IsHom 𝔸 f := by
  apply Iff.intro
  · intro
    fun_prop
  · rintro ⟨A, hA⟩
    use A
    intro π x hπ
    specialize hA π x.1 hπ
    simp only [funext_iff, perm_def] at hA
    specialize hA (perm π x).2
    simp only [Prod.perm_def, perm_mul, inv_mul_cancel, perm_one] at hA
    exact hA

lemma isHom_of_isSupp (A : Finset 𝔸) {f : X → Y} (hf : IsSupp A f) : IsHom 𝔸 f := by
  use A
  intro π x hπ
  replace hf := congr_fun (hf.eq π hπ) (perm π x)
  simp only [Function.perm_def, perm_mul, inv_mul_cancel, perm_one] at hf
  exact hf

lemma exists_isSupp_of_isHom {f : X → Y} (hf : IsHom 𝔸 f) : ∃A : Finset 𝔸, IsSupp A f := by
  obtain ⟨A, hA⟩ := hf
  use A
  constructor
  intro π hπ
  ext x
  specialize hA π (perm π⁻¹ x) hπ
  simp only [perm_mul, mul_inv_cancel, perm_one, Function.perm_def] at ⊢ hA
  rw [hA]

end PermAction.Function
