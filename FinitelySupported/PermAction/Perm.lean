import FinitelySupported.PermAction.Basic

namespace PermAction.Perm

variable {𝔸 : Type*}

@[simps]
instance : PermAction 𝔸 (Perm 𝔸) where
  perm π π' := π * π' * π⁻¹
  perm_one _ := rfl
  perm_mul _ _ _ := rfl

@[simp]
lemma isSupp_supp (π : Perm 𝔸) : IsSupp π.supp π := by
  constructor
  simp only [Perm.mem_supp, ne_eq, perm_def]
  intro π' hπ'
  have : ∀a, π a = a ∨ π' a = a := by grind
  have {a} : π (π' a) = π' (π a) := by
    cases this a with
    | inl h =>
      simp only [h]
      cases this (π' a) with
      | inl h' => exact h'
      | inr h' =>
        have := congr_arg π'.invFun h'
        simp only [Perm.left_inverse] at this
        simp only [this, h]
    | inr h =>
      simp only [h]
      cases this (π a) with
      | inl h' =>
        have := congr_arg π.invFun h'
        simp only [Perm.left_inverse] at this
        simp only [this, h]
      | inr h' => simp only [h']
  ext a
  simp only [Perm.mul_toFun, Perm.inv_toFun, ← this, Perm.right_inverse]

end PermAction.Perm
