import NominalSets.Perm.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Countable.Basic

/-!
# Permutations

This file provides lemmas related to finite permutations.
-/

namespace NominalSets.Perm

variable {𝔸 : Type*}

@[simp]
lemma coe_mk (π π' : 𝔸 → 𝔸) (hπ₁ hπ₂ hπ₃) (x) : mk π π' hπ₁ hπ₂ hπ₃ x = π x := rfl

@[ext]
lemma ext {π₁ π₂ : Perm 𝔸} (h : ∀ a, π₁ a = π₂ a) : π₁ = π₂ := by
  rcases π₁ with ⟨π₁₁, π₁₂, hπ₁₁, hπ₁₂, hπ₁₃⟩
  rcases π₂ with ⟨π₂₁, π₂₂, hπ₂₁, hπ₂₂, hπ₃₃⟩
  simp only [coe_mk, mk.injEq] at ⊢ h
  grind

@[simp]
lemma coe_injective (π : Perm 𝔸) : Function.Injective π := by
  apply Function.LeftInverse.injective (g := (π⁻¹ : Perm 𝔸))
  simp only [Function.LeftInverse, left_inverse, implies_true]

@[simp]
lemma coe_inj (π : Perm 𝔸) (a b : 𝔸) : π a = π b ↔ a = b := by
  apply Iff.intro
  · apply coe_injective
  · grind

@[simp]
lemma inv_injective : Function.Injective (· ⁻¹ : Perm 𝔸 → Perm 𝔸) := by
  intro π₁ π₂ hπ
  simp only at hπ
  simp only [Perm.ext_iff] at ⊢ hπ
  intro a
  specialize hπ (π₁ a)
  simp only [left_inverse] at hπ
  nth_rw 2 [hπ]
  simp only [right_inverse]

@[simp]
lemma inv_inj {π₁ π₂ : Perm 𝔸} : π₁⁻¹ = π₂⁻¹ ↔ π₁ = π₂ := by
  apply Iff.intro
  · apply inv_injective
  · grind

@[simp]
lemma eta {π₁ π₂ : Perm 𝔸} : (π₁ : 𝔸 → 𝔸) = π₂ ↔ π₁ = π₂ := by
  apply Iff.intro
  · intro h
    ext
    rw [h]
  · grind

instance : Group (Perm 𝔸) where
  one_mul _ := rfl
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := by
    ext
    simp only [mul_coe, left_inverse, one_coe]

@[simp]
lemma inv_one : 1⁻¹ = (1 : Perm 𝔸) := by rfl

@[simp]
lemma mul_assoc (π₁ π₂ π₃ : Perm 𝔸) : π₁ * (π₂ * π₃) = π₁ * π₂ * π₃ := by rfl

@[simp]
lemma swap_swap [DecidableEq 𝔸] (a b : 𝔸) : swap a b * swap a b = 1 := by
  ext
  simp only [mul_coe, swap_coe, left_eq_ite_iff, one_coe]
  grind

@[simp]
lemma swap_swap_l [DecidableEq 𝔸] (π) (a b : 𝔸) : π * swap a b * swap a b  = π := by
  simp only [← mul_assoc, swap_swap, mul_one]

lemma swap_comm [DecidableEq 𝔸] (a b : 𝔸) : swap a b = swap b a := by
  ext
  simp only [swap_coe]
  grind

@[simp]
lemma inv_swap [DecidableEq 𝔸] (a b : 𝔸) : (swap a b)⁻¹ = swap a b := rfl

@[simp]
lemma swap_eq [DecidableEq 𝔸] (a : 𝔸) : swap a a = 1 := by
  ext
  simp only [swap_coe, one_coe]
  grind

lemma swap_mul
    [DecidableEq 𝔸] (a b : 𝔸) (π : Perm 𝔸)
    : swap a b * π = π * swap (π⁻¹ a) (π⁻¹ b) := by
  ext c
  simp only [mul_coe, swap_coe]
  by_cases hac : a = π c
  · simp only [hac, ↓reduceIte, left_inverse, right_inverse]
  · simp only [hac, ↓reduceIte]
    by_cases hbc : b = π c
    · have : π⁻¹ a ≠ c := by
        rintro rfl
        simp only [right_inverse, not_true_eq_false] at hac
      simp only [hbc, ↓reduceIte, this, left_inverse, right_inverse]
    · simp only [hbc, ↓reduceIte]
      have hac' : π⁻¹ a ≠ c := by
        rintro rfl
        simp only [Perm.right_inverse, not_true_eq_false] at hac
      simp only [hac', ↓reduceIte, coe_inj, right_eq_ite_iff]
      rintro rfl
      simp only [Perm.right_inverse, not_true_eq_false] at hbc

lemma mul_swap
    [DecidableEq 𝔸] (a b : 𝔸) (π : Perm 𝔸)
    : π * swap a b = swap (π a) (π b) * π := by
  simp only [swap_mul, left_inverse]

@[simp]
lemma seq_append [DecidableEq 𝔸] (xs ys : List (𝔸 × 𝔸)) : seq (xs ++ ys) = seq xs * seq ys := by
  ext x
  induction xs with
  | nil => simp only [List.nil_append, seq, one_mul]
  | cons ab xs ih => simp only [List.cons_append, seq, mul_coe, ih, swap_coe]

lemma exists_seq [DecidableEq 𝔸] (π : Perm 𝔸) : ∃xs, π = seq xs := by
  obtain ⟨X, hX⟩ := π.has_supp
  induction X using Finset.induction generalizing π with
  | empty =>
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const] at hX
    use []
    ext x
    simp only [seq, one_coe]
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
        · simp only [hab, mul_coe, swap_coe, ↓reduceIte, ite_eq_right_iff]
          grind
        · specialize hX b
          have hab' : a ≠ b := by grind
          simp only [
            Finset.mem_insert, hab, hb, or_self,
            not_false_eq_true, forall_const] at hX
          simp only [mul_coe, hX, swap_coe, hab', ↓reduceIte, ite_eq_right_iff, imp_false, ne_eq]
          rintro rfl
          simp only [coe_inj] at hX
          contradiction
      · rcases ih with ⟨xs, hxs⟩
        use (a, π a) :: xs
        simp only [seq, ← hxs, mul_assoc, swap_swap, one_mul]

instance [Countable 𝔸] : Countable (Perm 𝔸) := by
  classical
  have lem (π : Perm 𝔸) := exists_seq π
  choose toList prop using lem
  apply Function.Injective.countable (f := toList)
  intro π₁ π₂ hπ
  have := congr_arg seq hπ
  simpa only [← prop] using this

end NominalSets.Perm
