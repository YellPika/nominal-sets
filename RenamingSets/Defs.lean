import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.FunProp

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

end Ren

/-- A type with a (nominal) _renaming action_ is equipped with -/
class RenameAction (𝔸 X : Type*) where
  /-- 1. A _renaming operation_, such that -/
  rename : Ren 𝔸 → X → X
  /-- 2. applying the _identity renaming_ is the identity, and -/
  rename_one (x) : rename 1 x = x
  /-- 3. composition of renamings is equal to renaming by the composition. -/
  rename_mul (f g : Ren 𝔸) (x : X) : rename f (rename g x) = rename (f * g) x

export RenameAction (rename rename_one rename_mul)

attribute [simp] rename_mul

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

@[simps]
instance : Inhabited (RenameAction 𝔸 X) where
  default := {
    rename _ x := x
    rename_one := by simp only [implies_true]
    rename_mul := by simp only [implies_true]
  }

@[simps]
instance (priority := default) : RenameAction 𝔸 𝔸 where
  rename σ := σ
  rename_one := by simp only [Ren.one_coe, implies_true]
  rename_mul := by simp only [Ren.mul_coe, implies_true]

variable (𝔸) in
/-- A function `f : X → Y` is _equivariant_ if it preserves renamings. -/
@[fun_prop]
structure Equivariant (f : X → Y) : Prop where
  /-- Renamings are preserved by `f`. -/
  eq (σ : Ren 𝔸) x : rename σ (f x) = f (rename σ x)

/--
A set `A` is a _support_ of an element `x` if applying any two renamings behaves
identically as long as the renamings agree on `A`.

Intuitively, `A` can be thought of as a superset of `x`'s free variables.
-/
structure IsSupportOf (A : Finset 𝔸) (x : X) where
  /-- Applying any two renamings behaves identically as long as the renamings agree on `A`. -/
  eq ⦃f g⦄ : (∀a ∈ A, f a = g a) → rename f x = rename g x

/--
A (nominal) _renaming set_ is a type with a renaming action such that every
element has a support.
-/
class RenamingSet (𝔸 X : Type*) [RenameAction 𝔸 X] where
  /-- Every element has a support. -/
  exists_support (𝔸) (x : X) : ∃A : Finset 𝔸, IsSupportOf A x

export RenamingSet (exists_support)

/-- Every renaming set has a minimal support, denoted by `supp`. -/
noncomputable def supp (𝔸) [RenameAction 𝔸 X] [RenamingSet 𝔸 X] (x : X) : Finset 𝔸 :=
  Set.Finite.toFinset (s := ⋂A, ⋂(_ : IsSupportOf A x), A.toSet) (by
    obtain ⟨A, hA⟩ := exists_support 𝔸 x
    apply Set.Finite.subset
    · apply A.finite_toSet
    · apply Set.iInter_subset_of_subset A
      simp only [hA, Set.iInter_true, subset_refl])

end RenamingSets
