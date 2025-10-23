import RenamingSets.RenameAction.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.FunProp

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

/--
A set `A` is a _support_ of an element `x` if applying any two renamings behaves
identically as long as the renamings agree on `A`.

Intuitively, `A` can be thought of as a superset of `x`'s free variables.
-/
structure IsSupportOf (A : Finset 𝔸) (x : X) where
  /-- Applying any two renamings behaves identically as long as the renamings agree on `A`. -/
  eq ⦃f g⦄ : (∀a ∈ A, f a = g a) → rename f x = rename g x

/--
An alternative formulation of support for functions.

NOTE: `IsSupportOfF` is actually only equivalent to `IsSupportOf` when the
function in question satisfies `IsSupportedF`.
-/
structure IsSupportOfF (A : Finset 𝔸) (f : X → Y) where
  /-- Any renaming which does not touch the support commutes with the function. -/
  eq ⦃σ : Ren 𝔸⦄ : (∀a ∈ A, σ a = a) → ∀x, rename σ (f x) = f (rename σ x)

variable (𝔸) in
/-- An element `x : X` is _supported_ if it has a finite support. -/
inductive IsSupported (x : X) : Prop where
  /-- Applying any two renamings behaves identically as long as the renamings agree on `A`. -/
  | intro (A : Finset 𝔸) : IsSupportOf A x → IsSupported x

variable (𝔸) in
/--
An alternative formulation of supportedness for functions.

NOTE: This is actually a stronger condition that `IsSupported`.
-/
@[fun_prop]
inductive IsSupportedF (f : X → Y) : Prop where
  /-- Any renaming which does not touch the support commutes with the function. -/
  | intro (A : Finset 𝔸) : IsSupportOfF A f → IsSupportedF f

variable (𝔸) in
/-- A function `f : X → Y` is _equivariant_ if it preserves renamings. -/
@[fun_prop]
inductive Equivariant (f : X → Y) : Prop where
  /-- Renamings are preserved by `f`. -/
  | intro : IsSupportOfF (∅ : Finset 𝔸) f → Equivariant f

/--
A (nominal) _renaming set_ is a type with a renaming action such that every
element has a support.
-/
class RenamingSet (𝔸 X : Type*) [RenameAction 𝔸 X] where
  /-- Every element has a support. -/
  isSupported (𝔸) (x : X) : IsSupported 𝔸 x

export RenamingSet (isSupported)

attribute [grind ←, simp] isSupported

/-- Every renaming set has a minimal support, denoted by `supp`. -/
noncomputable def supp (𝔸) [RenameAction 𝔸 X] [RenamingSet 𝔸 X] (x : X) : Finset 𝔸 :=
  Set.Finite.toFinset (s := ⋂A, ⋂(_ : IsSupportOf A x), A.toSet) (by
    obtain ⟨A, hA⟩ := isSupported 𝔸 x
    apply Set.Finite.subset
    · apply A.finite_toSet
    · apply Set.iInter_subset_of_subset A
      simp only [hA, Set.iInter_true, subset_refl])

end RenamingSets
