import NominalSets.PermAction.Defs

namespace NominalSets

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

lemma perm_lift {Y} (eq : X ≃ Y) (π y) : @perm 𝔸 Y (.lift 𝔸 eq) π y = eq (perm π (eq.symm y)) := rfl

@[simp]
lemma perm_one' : perm (𝔸 := 𝔸) (X := X) 1 = id := by
  ext
  simp only [perm_one, id_eq]

@[simp]
lemma perm_injective (π : Perm 𝔸) : Function.Injective (perm π : X → X) := by
  intro x y h
  have {x : X} : x = perm π⁻¹ (perm π x) := by simp only [perm_mul, inv_mul_cancel, perm_one]
  rw [@this x, @this y, h]

@[simp]
lemma perm_inj (π : Perm 𝔸) (x y : X) : perm π x = perm π y ↔ x = y := by
  apply Iff.intro
  · apply perm_injective
  · rintro rfl
    rfl

namespace PermAction

instance : DiscretePermAction[(default : PermAction 𝔸 X)] := by
  let : PermAction 𝔸 X := default
  constructor
  simp only [perm, implies_true]

end PermAction

namespace Function
instance [DiscretePermAction 𝔸 X] [DiscretePermAction 𝔸 Y] : DiscretePermAction 𝔸 (X → Y) where
  perm_discrete _ _ := by
    ext
    simp only [Function.perm_def, perm_discrete]
end Function

end NominalSets
