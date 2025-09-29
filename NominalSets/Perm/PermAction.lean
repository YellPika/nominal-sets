import NominalSets.PermAction.Basic

namespace NominalSets.Perm

variable {𝔸 : Type*}

@[simps -isSimp]
instance : PermAction 𝔸 (Perm 𝔸) where
  perm π π' := π * π' * π⁻¹
  perm_one := by simp only [one_mul, Perm.inv_one, mul_one, implies_true]
  perm_mul := by simp only [Perm.mul_assoc, mul_inv_rev, implies_true]

end NominalSets.Perm
