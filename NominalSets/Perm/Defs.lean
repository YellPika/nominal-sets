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
  right_inverse' (a : 𝔸) : toFun (invFun a) = a
  /-- `invFun` is a left inverse of `toFun`. -/
  left_inverse' (a : 𝔸) : invFun (toFun a) = a
  /-- `toFun` is finitely supported. -/
  has_supp' : ∃A : Finset 𝔸, ∀a ∉ A, toFun a = a

namespace Perm

variable {𝔸 : Type*}

instance : FunLike (Perm 𝔸) 𝔸 𝔸 where
  coe := toFun
  coe_injective' π₁ π₂ hπ := by
    rcases π₁ with ⟨f, f', hf₁, hf₂, hf₃⟩
    rcases π₂ with ⟨g, g', hg₁, hg₂, hg₃⟩
    dsimp only at hπ
    simp only [hπ, mk.injEq, true_and]
    ext a
    nth_rw 2 [← hf₁ a]
    simp only [hπ, hg₂]

instance : Inv (Perm 𝔸) where
  inv π := {
    toFun := π.invFun
    invFun := π.toFun
    right_inverse' := by simp only [left_inverse', implies_true]
    left_inverse' := by simp only [right_inverse', implies_true]
    has_supp' := by
      rcases π.has_supp' with ⟨X, hX⟩
      use X
      intro a ha
      specialize hX a ha
      nth_rw 1 [←hX]
      simp only [left_inverse']
  }

/-- A simps projection for function coercion. -/
def Simps.coe (π : Perm 𝔸) : 𝔸 → 𝔸 := π

/-- A simps projection for inverse function coercion. -/
def Simps.inv_coe (π : Perm 𝔸) : 𝔸 → 𝔸 := (π⁻¹ : Perm 𝔸)

initialize_simps_projections Perm (toFun → coe, invFun → inv_coe)

@[simp]
lemma right_inverse (π : Perm 𝔸) (a : 𝔸) : π (π⁻¹ a) = a :=
  π.right_inverse' a

@[simp]
lemma left_inverse (π : Perm 𝔸) (a : 𝔸) : π⁻¹ (π a) = a :=
  π.left_inverse' a

lemma has_supp (π : Perm 𝔸) : ∃A : Finset 𝔸, ∀a ∉ A, π a = a :=
  π.has_supp'

@[simps]
instance : One (Perm 𝔸) where
  one := {
    toFun a := a
    invFun a := a
    right_inverse' _ := rfl
    left_inverse' _ := rfl
    has_supp' := by
      simp only [implies_true, exists_const_iff, and_true]
      exact ⟨∅⟩
  }

@[simps]
instance : Mul (Perm 𝔸) where
  mul π₁ π₂ := {
    toFun a := π₁ (π₂ a)
    invFun a := π₂⁻¹ (π₁⁻¹ a)
    right_inverse' := by simp only [right_inverse, implies_true]
    left_inverse' := by simp only [left_inverse, implies_true]
    has_supp' := by
      classical
      rcases π₁.has_supp with ⟨X₁, hX₁⟩
      rcases π₂.has_supp with ⟨X₂, hX₂⟩
      use X₁ ∪ X₂
      simp only [Finset.mem_union, not_or, and_imp]
      intro a ha₁ ha₂
      rw [hX₂ a ha₂, hX₁ a ha₁]
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
  right_inverse' _ := by grind only [cases Or]
  left_inverse' _ := by grind only [cases Or]
  has_supp' := by
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
