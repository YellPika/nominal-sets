import FinitelySupported.Supported.List
import FinitelySupported.PermAction.Rose

namespace Supported.Rose

variable {𝔸 X : Type*} [PermAction 𝔸 X] [Supported 𝔸 X]

instance [Supported 𝔸 X] : Supported 𝔸 (Rose X) where
  has_supp t := by
    classical
    induction t with | mk label children ih =>
    obtain ⟨A, hA⟩ := has_supp 𝔸 label
    choose B hB using ih
    use A ∪ children.toFinset.attach.biUnion fun x ↦ B x.val (by
      have := x.property;
      simp only [List.mem_toFinset] at this
      exact this)
    simp only [PermAction.Rose.isSupp_mk]
    apply And.intro
    · apply IsSupp.union_left hA
    · rw [PermAction.List.isSupp_iff]
      intro a ha
      apply IsSupp.monotone _ _ (hB a ha)
      intro b hb
      simp only [
        Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists, List.mem_toFinset]
      grind

@[simp]
lemma supp_mk
    [DecidableEq 𝔸] (x : X) (xs : List (Rose X))
    : supp 𝔸 (Rose.mk x xs) = supp 𝔸 x ∪ supp 𝔸 xs := by
  have : supp 𝔸 (Rose.mk x xs) = supp 𝔸 (x, xs) := by
    ext a
    simp only [mem_supp, PermAction.Rose.isSupp_mk, and_imp, PermAction.Prod.isSupp_iff]
  ext a
  simp only [this, Prod.supp_eq, Finset.mem_union, mem_supp]

end Supported.Rose
