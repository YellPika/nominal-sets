import NominalSets.PermAction.Basic
import Mathlib.Data.Set.Lattice

namespace NominalSets

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

/-- A _finite support_ of an element `x` is, intuitively, any superset of `x`'s free variables. -/
structure IsSupportOf (A : Finset 𝔸) (x : X) where
  /-- Any permutation which preserves the support acts as the identity. -/
  eq : ∀π, (∀a ∈ A, π a = a) → perm π x = x

@[inherit_doc IsSupportOf]
scoped notation "IsSupportOf[" inst "]" => @IsSupportOf _ _ inst

variable (𝔸) in
/-- An element is _supported_ if it has a support. -/
inductive IsSupported (x : X) : Prop
  /-- Introduces a proof of supported-ness. -/
  | intro (A : Finset 𝔸) : IsSupportOf A x → IsSupported x

@[inherit_doc IsSupported]
scoped notation "IsSupported[" inst "]" => @IsSupported _ _ inst

variable (𝔸) in
/-- Like `IsSupported`, specialized for functions. -/
@[fun_prop]
inductive IsSupportedF (f : X → Y) : Prop
  /-- Introduces a proof of supported-ness. -/
  | intro (A : Finset 𝔸)
    : (∀π, (∀a ∈ A, π a = a) → ∀x, perm π (f x) = f (perm π x))
    → IsSupportedF f

variable (𝔸) in
/-- An equivariant function preserves permutations. -/
@[fun_prop]
structure Equivariant (f : X → Y) : Prop where
  /-- `f` preserves permutations. -/
  eq (π : Perm 𝔸) (x : X) : perm π (f x) = f (perm π x)

/-- Every element of a _nominal type_ has a support. -/
class Nominal (𝔸 X) [PermAction 𝔸 X] where
  /-- Every element has a support. -/
  supported (𝔸) (x : X) : IsSupported 𝔸 x := by simp

attribute [simp] Nominal.supported

@[inherit_doc Nominal]
scoped notation "Nominal[" inst "]" => @Nominal _ _ inst

/-- Every finitely-supported element has a minimal support. -/
noncomputable def supp (𝔸) [PermAction 𝔸 X] [Nominal 𝔸 X] (x : X) : Finset 𝔸 :=
  Set.Finite.toFinset (s := ⋂A, ⋂(_ : IsSupportOf A x), A.toSet) (by
    obtain ⟨A, hA⟩ := Nominal.supported 𝔸 x
    apply Set.Finite.subset
    · apply A.finite_toSet
    · apply Set.iInter_subset_of_subset A
      simp only [hA, Set.iInter_true, subset_refl])

end NominalSets
