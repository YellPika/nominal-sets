import NominalSets.Perm.Basic

namespace NominalSets

/-- A _permutable type_ `X` has a `Perm`-action. -/
class PermAction (𝔸 : Type*) (X : Type*) where
  /-- Applies a permutation to an element. -/
  perm : Perm 𝔸 → X → X
  /-- The identity permutation acts as the identity. -/
  perm_one (x : X) : perm 1 x = x
  /-- Composition of permutations is composition of actions. -/
  perm_mul (π₁ π₂ : Perm 𝔸) (x : X) : perm π₁ (perm π₂ x) = perm (π₁ * π₂) x

export PermAction (perm perm_one perm_mul)

/-- A _discrete permutable type_'s elements are not affected by permutation. -/
class DiscretePermAction (𝔸 : Type*) (X : Type*) [PermAction 𝔸 X] where
  /-- Permutation does nothing. -/
  perm_discrete (π : Perm 𝔸) (x : X) : perm π x = x

export DiscretePermAction (perm_discrete)

@[inherit_doc DiscretePermAction]
scoped notation "DiscretePermAction[" inst "]" => @DiscretePermAction _ _ inst

attribute [simp] perm_one perm_mul perm_discrete

variable {𝔸 X Y : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y]

namespace PermAction

variable (𝔸) in
/-- We can construct `PermAction` instances via a bijection. -/
def lift (eq : X ≃ Y) : PermAction 𝔸 Y where
  perm π x := eq (perm π (eq.invFun x))
  perm_one := by simp only [Equiv.invFun_as_coe, perm_one, Equiv.apply_symm_apply, implies_true]
  perm_mul := by simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply, perm_mul, implies_true]

instance : Inhabited (PermAction 𝔸 X) where
  default := {
    perm _ x := x
    perm_one _ := rfl
    perm_mul _ _ _ := rfl
  }

@[simps]
instance (priority := default) : PermAction 𝔸 𝔸 where
  perm π x := π x
  perm_one := by simp only [Perm.one_toFun, implies_true]
  perm_mul := by simp only [Perm.mul_toFun, implies_true]

end PermAction

namespace Bool
instance : PermAction 𝔸 Bool := default
end Bool

namespace Empty
instance : PermAction 𝔸 Empty := default
end Empty

namespace PEmpty
instance : PermAction 𝔸 PEmpty := default
end PEmpty

namespace Unit
instance : PermAction 𝔸 Unit := default
end Unit

namespace PUnit
instance : PermAction 𝔸 PUnit := default
end PUnit

namespace Function

@[simps]
instance : PermAction 𝔸 (X → Y) where
  perm π f x := perm π (f (perm π⁻¹ x))
  perm_one _ := by
    ext
    simp only [Perm.inv_one, perm_one]
  perm_mul _ _ _ := by
    ext
    simp only [perm_mul, mul_inv_rev]

end Function

end NominalSets
