import RenamingSets.Support.Basic

namespace RenamingSets.Prod

variable {𝔸 X Y : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y]

@[simps -isSimp]
instance : RenameAction 𝔸 (X × Y) where
  rename σ x := (rename σ x.1, rename σ x.2)
  rename_one := by simp only [rename_one, Prod.mk.eta, implies_true]
  rename_mul := by simp only [rename_mul, implies_true]

@[simp, grind =]
lemma rename_mk
    (σ : Ren 𝔸) (x : X) (y : Y)
    : rename σ (x, y) = (rename σ x, rename σ y) := by
  simp only [rename_def]

@[simp, grind =]
lemma isSupportOf_mk
    (A : Finset 𝔸) (x : X) (y : Y)
    : IsSupportOf A (x, y) ↔ IsSupportOf A x ∧ IsSupportOf A y := by
  apply Iff.intro
  · simp only [isSupportOf_def, rename_mk, Prod.mk.injEq]
    intro h
    apply And.intro
    · intro f g h'
      apply (h h').1
    · intro f g h'
      apply (h h').2
  · simp only [isSupportOf_def, rename_mk, Prod.mk.injEq, and_imp]
    grind

variable [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]

instance : RenamingSet 𝔸 (X × Y) where
  exists_support x := by
    classical
    rcases x with ⟨x, y⟩
    simp only [isSupportOf_mk]
    obtain ⟨A, hA⟩ := exists_support 𝔸 x
    obtain ⟨B, hB⟩ := exists_support 𝔸 y
    use A ∪ B
    apply And.intro
    · apply isSupportOf_union_left hA
    · apply isSupportOf_union_right hB

@[simp, grind =]
lemma supp_mk [DecidableEq 𝔸] (x : X) (y : Y) : supp 𝔸 (x, y) = supp 𝔸 x ∪ supp 𝔸 y := by
  ext a
  simp only [mem_supp, isSupportOf_mk, and_imp, Finset.mem_union]
  apply Iff.intro
  · intro h
    by_cases h' : ∀ (A : Finset 𝔸), IsSupportOf A x → a ∈ A
    · grind
    · simp only [not_forall] at h'
      rcases h' with ⟨A, hA₁, hA₂⟩
      right
      intro B hB
      specialize h (A ∪ B) (isSupportOf_union_left hA₁) (isSupportOf_union_right hB)
      grind
  · grind

end RenamingSets.Prod
