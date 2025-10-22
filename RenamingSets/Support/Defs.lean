import RenamingSets.RenameAction.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.FunProp

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

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
