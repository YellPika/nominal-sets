import FinitelySupported.Supported.Basic
import FinitelySupported.PermAction.Prod

open PermAction

namespace Supported.Prod

variable {𝔸 X Y : Type*}
  [PermAction 𝔸 X] [Supported 𝔸 X]
  [PermAction 𝔸 Y] [Supported 𝔸 Y]

instance : Supported 𝔸 (X × Y) where
  has_supp x := by
    classical
    rcases has_supp 𝔸 x.1 with ⟨A, hA⟩
    rcases has_supp 𝔸 x.2 with ⟨B, hB⟩
    use A ∪ B
    simp only [Prod.isSupp_iff]
    apply And.intro
    · apply IsSupp.monotone _ _ hA
      simp only [Finset.le_eq_subset, Finset.subset_union_left]
    · apply IsSupp.monotone _ _ hB
      simp only [Finset.le_eq_subset, Finset.subset_union_right]

@[simp]
lemma supp_eq [DecidableEq 𝔸] (x : X × Y) : supp 𝔸 x = supp 𝔸 x.1 ∪ supp 𝔸 x.2 := by
  classical
  ext a
  simp only [mem_supp, Prod.isSupp_iff, and_imp, Finset.mem_union]
  apply Iff.intro
  · intro h
    by_cases h' : ∀ (A : Finset 𝔸), IsSupp A x.1 → a ∈ A
    · exact .inl h'
    · simp only [not_forall] at h'
      rcases h' with ⟨A, hA₁, hA₂⟩
      right
      intro B hB
      specialize h (A ∪ B) (IsSupp.union_left hA₁) (IsSupp.union_right hB)
      grind
  · grind

end Supported.Prod
