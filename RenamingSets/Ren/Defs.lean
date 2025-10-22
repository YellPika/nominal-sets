import Mathlib.Data.Set.Finite.Basic

/-! # Finitely-Supported Renamings

This file defines finitely-supported renamings and related operations.
A finitely-supported renaming on `𝔸` is a function `σ : 𝔸 → 𝔸` such that
`σ a ≠ a` for only finitely many `a : 𝔸`.
-/

namespace RenamingSets

/-- The type of finitely supported renamings. -/
structure Ren (𝔸 : Type*) where
  /-- The underlying function. -/
  toFun : 𝔸 → 𝔸

  /--
  The underlying function is the identity everywhere except for finitely many
  elements.
  -/
  exists_support' : ∃A : Finset 𝔸, ∀a ∉ A, toFun a = a

namespace Ren

variable {𝔸 : Type*}

instance : FunLike (Ren 𝔸) 𝔸 𝔸 where
  coe := toFun
  coe_injective' ρ₁ ρ₂ hρ := by
    rcases ρ₁
    rcases ρ₂
    simp_all only

/-- A simps projection for function coercion. -/
def Simps.coe (f : Ren 𝔸) : 𝔸 → 𝔸 := f

initialize_simps_projections Ren (toFun → coe)

@[simps]
instance : One (Ren 𝔸) where
  one := {
    toFun a := a
    exists_support' := by simp only [implies_true, exists_const]
  }

@[simps]
instance : Mul (Ren 𝔸) where
  mul ρ₁ ρ₂ := {
    toFun a := ρ₁ (ρ₂ a)
    exists_support' := by
      classical
      rcases ρ₁ with ⟨ρ₁, A₁, hρ₁⟩
      rcases ρ₂ with ⟨ρ₂, A₂, hρ₂⟩
      use A₁ ∪ A₂
      simp only [Finset.mem_union, not_or, DFunLike.coe, and_imp]
      grind
  }

/-- Constructs a renaming by restricting a function to a finite set. -/
@[simps]
def restrict [DecidableEq 𝔸] (A : Finset 𝔸) (f : 𝔸 → 𝔸) : Ren 𝔸 where
  toFun a := if a ∈ A then f a else a
  exists_support' := by
    use A
    grind

/-- `assign a b` is the renaming which re-assigns `b` to `a`. -/
abbrev assign [DecidableEq 𝔸] (a b : 𝔸) : Ren 𝔸 := restrict {a} fun _ ↦ b

/-- The renaming which swaps two variables. -/
@[simps]
def swap [DecidableEq 𝔸] (a b : 𝔸) : Ren 𝔸 where
  toFun c := if c = a then b else if c = b then a else c
  exists_support' := by
    use {a, b}
    grind

/--
The support of a renaming `ρ` is the set of all elements on which `ρ` is _not_
the identity.
-/
noncomputable def supp (ρ : Ren 𝔸) : Finset 𝔸 :=
  open Classical in
  ρ.exists_support'.choose.filter fun a ↦ ρ a ≠ a

end Ren

end RenamingSets
