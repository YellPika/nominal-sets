import FinitelySupported.Supported.Prod
import FinitelySupported.PermAction.List

open PermAction

namespace Supported.List

variable {𝔸 X Y : Type*}
  [PermAction 𝔸 X] [Supported 𝔸 X]
  [PermAction 𝔸 Y] [Supported 𝔸 Y]

instance : Supported 𝔸 (List X) where
  has_supp xs := by
    classical
    induction xs with
    | nil => simp only [List.isSupp_nil, exists_const]
    | cons head tail ih =>
      simp only [List.isSupp_cons]
      have ⟨A, hA⟩ := has_supp 𝔸 head
      have ⟨B, hB⟩ := ih
      use A ∪ B
      apply And.intro
      · apply IsSupp.union_left hA
      · apply IsSupp.union_right hB

@[simp]
lemma supp_nil : supp 𝔸 ([] : List X) = ∅ := by
  ext a
  simp only [mem_supp, List.isSupp_nil, forall_const, Finset.notMem_empty, iff_false, not_forall]
  use ∅
  simp only [Finset.notMem_empty, not_false_eq_true]

@[simp]
lemma supp_cons
    [DecidableEq 𝔸] (x : X) (xs : List X)
    : supp 𝔸 (x :: xs) = supp 𝔸 x ∪ supp 𝔸 xs := by
  ext a
  have : supp 𝔸 (x :: xs) = supp 𝔸 (x, xs) := by
    ext a
    simp only [mem_supp, List.isSupp_cons, and_imp, Prod.isSupp_iff]
  simp only [this, Prod.supp_eq, Finset.mem_union, mem_supp]

end Supported.List
