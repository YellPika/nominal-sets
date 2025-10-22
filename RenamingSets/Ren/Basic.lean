import RenamingSets.Ren.Defs
import Mathlib.Algebra.Group.Defs

/-! # Finitely-Supported Renamings

This file provides basic lemmas about finitely-supported renamings.
-/

variable {𝔸 : Type*}

namespace RenamingSets.Ren

@[simp]
lemma mk_coe (σ : 𝔸 → 𝔸) (hσ a) : mk σ hσ a = σ a := rfl

lemma exists_support (ρ : Ren 𝔸) : ∃A : Finset 𝔸, ∀a ∉ A, ρ a = a :=
  ρ.exists_support'

@[ext]
lemma ext {ρ₁ ρ₂ : Ren 𝔸} (h : ∀ a, ρ₁ a = ρ₂ a) : ρ₁ = ρ₂ := by
  rcases ρ₁
  rcases ρ₂
  simp only [mk.injEq]
  ext a
  apply h

instance : Monoid (Ren 𝔸) where
  mul_assoc := by simp only [Ren.ext_iff, mul_coe, implies_true]
  one_mul := by simp only [Ren.ext_iff, mul_coe, one_coe, implies_true]
  mul_one := by simp only [Ren.ext_iff, mul_coe, one_coe, implies_true]

@[simp]
lemma mem_supp (a : 𝔸) (ρ : Ren 𝔸) : a ∈ supp ρ ↔ ρ a ≠ a := by
  apply Iff.intro
  · simp only [supp, ne_eq, Finset.mem_filter, and_imp, imp_self, implies_true]
  · intro h
    simp only [supp, ne_eq, Finset.mem_filter, h, not_false_eq_true, and_true]
    by_contra h'
    apply h
    apply ρ.exists_support'.choose_spec
    exact h'

@[simp]
lemma swap_swap [DecidableEq 𝔸] (a b : 𝔸) : swap a b * swap a b = 1 := by
  ext c
  simp only [mul_coe, swap_coe, ite_eq_left_iff, one_coe]
  grind

@[simp]
lemma swap_swap_r [DecidableEq 𝔸] (a b : 𝔸) (σ : Ren 𝔸) : swap a b * (swap a b * σ) = σ := by
  ext c
  simp only [mul_coe, swap_coe, ite_eq_left_iff]
  grind

end RenamingSets.Ren
