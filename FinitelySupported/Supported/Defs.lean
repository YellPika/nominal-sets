import FinitelySupported.PermAction.Function
import FinitelySupported.Perm.Basic
import Mathlib.Data.Set.Lattice

/-- A _(finitely) supported type_ is a `PermAction` type with a finite support. -/
class Supported (𝔸 : Type*) (X : Type*) [PermAction 𝔸 X] where
  /-- Proof that each element has a finite support. -/
  has_supp (𝔸) (x : X) : ∃A : Finset 𝔸, IsSupp A x

namespace Supported

open PermAction

variable {𝔸 X Y : Type*}

/-- Every finitely-supported element has a minimal support. -/
noncomputable def supp (𝔸) [PermAction 𝔸 X] [Supported 𝔸 X] (x : X) : Finset 𝔸 :=
  Set.Finite.toFinset (s := ⋂A, ⋂(_ : IsSupp A x), A.toSet) (by
    obtain ⟨A, hA⟩ := has_supp 𝔸 x
    apply Set.Finite.subset
    · apply A.finite_toSet
    · apply Set.iInter_subset_of_subset A
      simp only [hA, Set.iInter_true, subset_refl])

/--
For any `PermAction` type `X`, we can form a `Supported` type `FS 𝔸 X` which is
simply `X` restricted to those elements which have a finite support.
-/
@[ext]
structure FS (𝔸) (X : Type*) [PermAction 𝔸 X] where
  /-- The underlying element. -/
  val : X
  /-- The element has a finite support. -/
  property : ∃A : Finset 𝔸, IsSupp A val

namespace FS

@[simps]
instance {𝔸 X : Type*} [PermAction 𝔸 X] : PermAction 𝔸 (FS 𝔸 X) where
  perm π x := {
    val := perm π x.val,
    property := by
      classical
      have ⟨A, hA⟩ := x.property
      use A.image π
      constructor
      intro π' hπ'
      simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hπ'
      have : ∀a ∈ A, (π⁻¹ * π' * π) a = a := by
        intro a ha
        simp only [Perm.mul_toFun, hπ' a ha, Perm.inv_toFun, Perm.left_inverse]
      have := hA.eq _ this
      nth_rw 2 [←this]
      simp only [perm_mul, Perm.mul_assoc, mul_inv_cancel_left]
  }
  perm_one := by simp only [perm_one, implies_true]
  perm_mul := by simp only [perm_mul, implies_true]

instance {𝔸 X Y} [PermAction 𝔸 X] [PermAction 𝔸 Y] : CoeFun (FS 𝔸 (X → Y)) (fun _ ↦ X → Y) where
  coe := val

end FS

end Supported
