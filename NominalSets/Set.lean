import NominalSets.Function

namespace NominalSets.Set

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

@[simps -isSimp]
instance : PermAction 𝔸 (Set X) where
  perm π s := perm π '' s
  perm_one := by simp only [perm_one, Set.image_id', implies_true]
  perm_mul _ _ _ := by
    ext
    simp only [Set.mem_image, exists_exists_and_eq_and, perm_mul]

@[simp]
lemma mem_perm (x : X) (π : Perm 𝔸) (s : Set X) : x ∈ perm π s ↔ perm π⁻¹ x ∈ s := by
  simp only [perm_def, Set.mem_image]
  apply Iff.intro
  · rintro ⟨y, h, rfl⟩
    simp only [perm_mul, inv_mul_cancel, perm_one, h]
  · intro h
    use perm π⁻¹ x, h
    simp only [perm_mul, mul_inv_cancel, perm_one]

@[simp]
lemma perm_union (π : Perm 𝔸) (s t : Set X) : perm π (s ∪ t) = perm π s ∪ perm π t := by
  ext a
  simp only [mem_perm, Set.mem_union]

@[simp]
lemma perm_inter (π : Perm 𝔸) (s t : Set X) : perm π (s ∩ t) = perm π s ∩ perm π t := by
  ext a
  simp only [mem_perm, Set.mem_inter_iff]

@[simp]
lemma perm_compl (π : Perm 𝔸) (s : Set X) : perm π sᶜ = (perm π s)ᶜ := by
  ext a
  simp only [mem_perm, Set.mem_compl_iff]

lemma finite (π : Perm 𝔸) {s : Set X} (hs : s.Finite) : (perm π s).Finite := by
  exact Set.Finite.image (perm π) hs

instance [DiscretePermAction 𝔸 X] : DiscretePermAction 𝔸 (Set X) where
  perm_discrete _ _ := by
    ext
    simp only [Set.mem_perm, perm_discrete]

end NominalSets.Set
