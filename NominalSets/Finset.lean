import NominalSets.Prod
import Mathlib.Data.Finset.Union

namespace NominalSets.Finset

variable {𝔸 X : Type*} [PermAction 𝔸 X] [DecidableEq X]

@[simps -isSimp]
instance : PermAction 𝔸 (Finset X) where
  perm π s := s.image (perm π)
  perm_one s := by
    ext
    simp only [Finset.mem_image, perm_one, exists_eq_right]
  perm_mul _ _ _ := by
    ext
    simp only [Finset.mem_image, exists_exists_and_eq_and, perm_mul]

@[simp]
lemma mem_perm
    (x : X) (π : Perm 𝔸) (s : Finset X)
    : x ∈ perm π s ↔ perm π⁻¹ x ∈ s := by
  simp only [perm_def, Finset.mem_image]
  apply Iff.intro
  · rintro ⟨y, h, rfl⟩
    simp only [perm_mul, inv_mul_cancel, perm_one, h]
  · intro h
    use perm π⁻¹ x, h
    simp only [perm_mul, mul_inv_cancel, perm_one]

@[simp]
lemma perm_empty (π : Perm 𝔸) : perm π (∅ : Finset X) = ∅ := by
  ext a
  simp only [mem_perm, Finset.notMem_empty]

@[simp]
lemma perm_insert
    (π : Perm 𝔸) (x : X) (s : Finset X)
    : perm π (insert x s) = insert (perm π x) (perm π s) := by
  ext a
  simp only [mem_perm, Finset.mem_insert]
  apply Iff.intro
  · intro h
    cases h with
    | inl h => simp only [← h, perm_mul, mul_inv_cancel, perm_one, true_or]
    | inr h => simp only [h, or_true]
  · intro h
    cases h with
    | inl h => simp only [h, perm_mul, inv_mul_cancel, perm_one, true_or]
    | inr h => simp only [h, or_true]

instance [DiscretePermAction 𝔸 X] : DiscretePermAction 𝔸 (Finset X) where
  perm_discrete _ _ := by
    ext
    simp only [Finset.mem_perm, perm_discrete]

@[simp]
lemma isSupportOf_empty (A : Finset 𝔸) : IsSupportOf A (∅ : Finset X) := by
  simp only [isSupportOf_def, perm_empty, implies_true]

@[simp]
lemma isSupported_empty : IsSupported 𝔸 (∅ : Finset X) := by
  simp only [isSupported_def, isSupportOf_empty, exists_const]

instance [Nominal 𝔸 X] : Nominal 𝔸 (Finset X) where
  supported s := by
    classical
    have : ∀x : X, ∃A : Finset 𝔸, IsSupportOf A x := by
      intro x
      have ⟨A, hA⟩ := Nominal.supported 𝔸 x
      use A
    choose A hA using this
    use s.biUnion A
    constructor
    simp only [Finset.mem_biUnion, forall_exists_index, and_imp]
    intro π hπ
    ext x
    apply Iff.intro
    · simp only [mem_perm]
      intro h
      simp only [isSupportOf_def] at hA
      specialize hA (perm π⁻¹ x) π
      simp only [perm_mul, mul_inv_cancel, perm_one] at hA
      rw [←hA] at h
      · exact h
      · intro a ha
        apply hπ a (perm π⁻¹ x) ?_ ha
        exact h
    · intro hx
      simp only [mem_perm]
      simp only [isSupportOf_def] at hA
      rw [hA x π⁻¹]
      · exact hx
      · intro a ha
        nth_rw 1 [← hπ a x hx ha]
        simp only [Perm.inv_toFun, Perm.left_inverse]

end NominalSets.Finset
