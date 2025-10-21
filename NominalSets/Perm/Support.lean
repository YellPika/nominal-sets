import NominalSets.Perm.PermAction
import NominalSets.Support.Basic

namespace NominalSets.Perm

variable {𝔸 : Type*}

/-- The support of a permutation is the set of atoms that are modified. -/
noncomputable def supp (π : Perm 𝔸) : Finset 𝔸 :=
  Set.Finite.toFinset (s := {a | π a ≠ a}) (by
    obtain ⟨A, hA⟩ := π.has_supp
    apply Set.Finite.subset (s := A)
    · simp only [Finset.finite_toSet]
    · intro a
      simp only [ne_eq, Set.mem_setOf_eq, Finset.mem_coe]
      grind)

@[simp]
lemma mem_supp (π : Perm 𝔸) (a : 𝔸) : a ∈ supp π ↔ π a ≠ a := by
  simp only [supp, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

@[simp]
lemma isSupportOf_supp (π : Perm 𝔸) : IsSupportOf π.supp π := by
  constructor
  simp only [mem_supp, ne_eq, perm_def]
  intro π' hπ'
  have : ∀a, π a = a ∨ π' a = a := by grind
  have {a} : π (π' a) = π' (π a) := by
    cases this a with
    | inl h =>
      simp only [h]
      cases this (π' a) with
      | inl h' => exact h'
      | inr h' =>
        have := congr_arg (π'⁻¹ : Perm 𝔸) h'
        simp only [left_inverse] at this
        simp only [this, h]
    | inr h =>
      simp only [h]
      cases this (π a) with
      | inl h' =>
        have := congr_arg (π⁻¹ : Perm 𝔸) h'
        simp only [left_inverse] at this
        simp only [this, h]
      | inr h' => simp only [h']
  ext a
  simp only [mul_coe, ← this, right_inverse]

instance : Nominal 𝔸 (Perm 𝔸) where
  supported π := by
    use π.supp
    simp only [isSupportOf_supp]

@[simp]
lemma supp_eq [Infinite 𝔸] (π : Perm 𝔸) : NominalSets.supp 𝔸 π = π.supp := by
  classical
  ext a
  apply Iff.intro
  · simp only [NominalSets.mem_supp, mem_supp, ne_eq]
    intro h₁ h₂
    specialize h₁ π.supp
    simp only [isSupportOf_supp, mem_supp, ne_eq, forall_const] at h₁
    contradiction
  · simp only [mem_supp, ne_eq, NominalSets.mem_supp]
    intro ha A hA
    by_contra ha'
    obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (A ∪ {a, π a})
    simp only [Finset.union_insert, Finset.union_singleton, Finset.mem_insert, not_or] at hb
    rw [isSupportOf_swap] at hA
    specialize hA ha' hb.2.2
    rw [Perm.ext_iff] at hA
    specialize hA a
    simp only [perm_def, inv_swap, mul_coe, swap_coe, ↓reduceIte] at hA
    by_cases hbb : b = π b
    · simp only [← hbb, ↓reduceIte] at hA
      grind
    · simp only [hbb, ↓reduceIte] at hA
      by_cases hab : a = π b
      · subst hab
        grind
      · simp only [hab, ↓reduceIte] at hA
        replace hA := coe_injective π hA
        grind

end NominalSets.Perm
