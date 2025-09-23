import FinitelySupported.Perm.Defs
import Mathlib.Algebra.Group.Defs

namespace Perm

variable {𝔸 : Type*}

@[simp]
lemma injective (π : Perm 𝔸) : Function.Injective π := by
  apply Function.LeftInverse.injective (g := π.invFun)
  simp only [Function.LeftInverse, left_inverse, implies_true]

@[simp]
lemma inj (π : Perm 𝔸) (a b : 𝔸) : π a = π b ↔ a = b := by
  apply Iff.intro
  · apply injective
  · grind

@[ext]
lemma ext {π₁ π₂ : Perm 𝔸} (h : ∀ a, π₁ a = π₂ a) : π₁ = π₂ := by
  rcases π₁ with ⟨π₁₁, π₁₂, hπ₁₁, hπ₁₂, π₁₃⟩
  rcases π₂ with ⟨π₂₁, π₂₂, hπ₂₁, hπ₂₂, π₃₃⟩
  simp only [mk.injEq] at ⊢ h
  apply And.intro
  · ext
    apply h
  · ext
    apply injective ⟨π₁₁, π₁₂, hπ₁₁, hπ₁₂, π₁₃⟩
    simp only [hπ₁₁, h, hπ₂₁]

instance : Group (Perm 𝔸) where
  one_mul _ := rfl
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := by
    ext
    simp only [mul_toFun, inv_toFun, left_inverse, one_toFun]

@[simp]
lemma inv_one : 1⁻¹ = (1 : Perm 𝔸) := by rfl

@[simp]
lemma mul_assoc (π₁ π₂ π₃ : Perm 𝔸) : π₁ * (π₂ * π₃) = π₁ * π₂ * π₃ := by rfl

@[simp]
lemma swap_swap [DecidableEq 𝔸] (a b : 𝔸) : swap a b * swap a b = 1 := by
  ext
  simp only [mul_toFun, swap_toFun, left_eq_ite_iff, one_toFun]
  grind

@[simp]
lemma swap_swap_l [DecidableEq 𝔸] (π) (a b : 𝔸) : π * swap a b * swap a b  = π := by
  simp only [← mul_assoc, swap_swap, mul_one]

lemma swap_comm [DecidableEq 𝔸] (a b : 𝔸) : swap a b = swap b a := by
  ext
  simp only [swap_toFun]
  grind

@[simp]
lemma inv_swap [DecidableEq 𝔸] (a b : 𝔸) : (swap a b)⁻¹ = swap a b := rfl

@[simp]
lemma swap_eq [DecidableEq 𝔸] (a : 𝔸) : swap a a = 1 := by
  ext
  simp only [swap_toFun, one_toFun]
  grind

@[simp]
lemma seq_append [DecidableEq 𝔸] (xs ys : List (𝔸 × 𝔸)) : seq (xs ++ ys) = seq xs * seq ys := by
  ext x
  induction xs with
  | nil => simp only [List.nil_append, seq, one_mul]
  | cons ab xs ih => simp only [List.cons_append, seq, mul_toFun, ih, swap_toFun]

lemma exists_seq [DecidableEq 𝔸] (π : Perm 𝔸) : ∃xs, π = seq xs := by
  obtain ⟨X, hX⟩ := π.has_supp
  induction X using Finset.induction generalizing π with
  | empty =>
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const] at hX
    use []
    ext x
    simp only [seq, one_toFun]
    apply hX
  | insert a s ha ih =>
    by_cases hπ : π a = a
    · apply ih π
      intro b hb
      by_cases hab : b = a
      · simp only [hab, hπ]
      · apply hX
        simp only [Finset.mem_insert, hab, hb, or_self, not_false_eq_true]
    · specialize ih (swap a (π a) * π) ?_
      · intro b hb
        by_cases hab : b = a
        · simp only [hab, mul_toFun, swap_toFun, ↓reduceIte, ite_eq_right_iff]
          grind
        · specialize hX b
          have hab' : a ≠ b := by grind
          simp only [
            Finset.mem_insert, hab, hb, or_self,
            not_false_eq_true, forall_const] at hX
          simp only [
            mul_toFun, hX, swap_toFun, hab', ↓reduceIte,
            ite_eq_right_iff, imp_false, ne_eq]
          rintro rfl
          simp only [inj] at hX
          contradiction
      · rcases ih with ⟨xs, hxs⟩
        use (a, π a) :: xs
        simp only [seq, ← hxs, mul_assoc, swap_swap, one_mul]

@[simp]
lemma mem_supp (π : Perm 𝔸) (a : 𝔸) : a ∈ supp π ↔ π a ≠ a := by
  simp only [supp, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

end Perm
