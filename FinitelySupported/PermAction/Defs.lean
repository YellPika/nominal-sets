import FinitelySupported.Perm.Basic

variable {𝔸 X Y : Type*}

/-- A _permutable type_ `X` has a `Perm`-action. -/
class PermAction (𝔸 : Type*) (X : Type*) where
  /-- Applies a permutation to an element. -/
  perm : Perm 𝔸 → X → X
  /-- The identity permutation acts as the identity. -/
  perm_one (x : X) : perm 1 x = x
  /-- Composition of permutations is composition of actions. -/
  perm_mul (π₁ π₂ : Perm 𝔸) (x : X) : perm π₁ (perm π₂ x) = perm (π₁ * π₂) x

/-- A _finite support_ of an element `x` is, intuitively, any superset of `x`'s free variables. -/
structure IsSupp [PermAction 𝔸 X] (A : Finset 𝔸) (x : X) : Prop where
  /-- Any permutation which preserves the support acts as the identity. -/
  eq (π : Perm 𝔸) : (∀x ∈ A, π x = x) → PermAction.perm π x = x

namespace PermAction

attribute [simp] perm_one perm_mul

/-- We can construct `PermAction` instances via a bijection. -/
def lift (𝔸) [PermAction 𝔸 X] (eq : X ≃ Y) : PermAction 𝔸 Y where
  perm π x := eq (perm π (eq.invFun x))
  perm_one := by simp only [Equiv.invFun_as_coe, perm_one, Equiv.apply_symm_apply, implies_true]
  perm_mul := by simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply, perm_mul, implies_true]

@[simps]
instance : Inhabited (PermAction 𝔸 X) where
  default := {
    perm _ x := x
    perm_one _ := rfl
    perm_mul _ _ _ := rfl
  }

/-- Morphisms are exactly the set of finitely-supported functions. -/
@[fun_prop]
inductive IsHom (𝔸) [PermAction 𝔸 X] [PermAction 𝔸 Y] (f : X → Y) : Prop
  /--
  For convenience, we provide a different (but equivalent) definition instead
  of directly using `HasSupp`.
  -/
  | intro (A : Finset 𝔸)
    : (∀(π : Perm 𝔸) (x : X), (∀a ∈ A, π a = a) → perm π (f x) = f (perm π x))
    → IsHom 𝔸 f

@[inherit_doc IsHom]
scoped notation "IsHom[" inst₁ ", " inst₂ "]" => @IsHom _ _ _ inst₁ inst₂

end PermAction
