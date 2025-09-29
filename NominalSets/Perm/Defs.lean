import Mathlib.Tactic.FunProp
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Set.Finite.Basic

/-!
# Permutations

This file defines finite permutations and related operations.
-/

namespace NominalSets

/-- The type of finite permutations on a type `𝔸`. -/
structure Perm (𝔸 : Type*) where
  /-- The forward permutation. -/
  toFun : 𝔸 → 𝔸
  /-- The inverse permutation. -/
  invFun : 𝔸 → 𝔸
  /-- `invFun` is a right inverse of `toFun`. -/
  right_inverse (x : 𝔸) : toFun (invFun x) = x
  /-- `invFun` is a left inverse of `toFun`. -/
  left_inverse (x : 𝔸) : invFun (toFun x) = x
  /-- `toFun` is finitely supported. -/
  has_supp : ∃X : Finset 𝔸, ∀x ∉ X, toFun x = x

namespace Perm

variable {𝔸 : Type*}

attribute [simp] right_inverse left_inverse

instance : CoeFun (Perm 𝔸) (fun _ ↦ 𝔸 → 𝔸) where
  coe := toFun

@[simps]
instance : One (Perm 𝔸) where
  one := {
    toFun a := a
    invFun a := a
    right_inverse _ := rfl
    left_inverse _ := rfl
    has_supp := by
      simp only [implies_true, exists_const_iff, and_true]
      exact ⟨∅⟩
  }

@[simps]
instance : Mul (Perm 𝔸) where
  mul π₁ π₂ := {
    toFun a := π₁ (π₂ a)
    invFun a := π₂.invFun (π₁.invFun a)
    right_inverse a := by simp only [right_inverse]
    left_inverse := by simp only [left_inverse, implies_true]
    has_supp := by
      classical
      rcases π₁.has_supp with ⟨X₁, hX₁⟩
      rcases π₂.has_supp with ⟨X₂, hX₂⟩
      use X₁ ∪ X₂
      simp only [Finset.mem_union, not_or, and_imp]
      intro a ha₁ ha₂
      rw [hX₂ a ha₂, hX₁ a ha₁]
  }

@[simps]
instance : Inv (Perm 𝔸) where
  inv π := {
    toFun := π.invFun
    invFun := π.toFun
    right_inverse := by simp only [left_inverse, implies_true]
    left_inverse := by simp only [right_inverse, implies_true]
    has_supp := by
      rcases π.has_supp with ⟨X, hX⟩
      use X
      intro a ha
      specialize hX a ha
      nth_rw 1 [←hX]
      simp only [left_inverse]
  }

/-- The permutation that simply swaps two elements. -/
@[simps]
def swap (a b : 𝔸) [DecidableEq 𝔸] : Perm 𝔸 where
  toFun c :=
    if a = c then b else
    if b = c then a else c
  invFun c :=
    if a = c then b else
    if b = c then a else c
  right_inverse _ := by grind only [cases Or]
  left_inverse _ := by grind only [cases Or]
  has_supp := by
    use {a, b}
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    grind only

/-- A sequence of pairs induces a permutation constructed as a sequences of `swap`s. -/
@[simp]
def seq [DecidableEq 𝔸] : List (𝔸 × 𝔸) → Perm 𝔸
  | [] => 1
  | (a, b) :: xs => swap a b * seq xs

end Perm

end NominalSets
