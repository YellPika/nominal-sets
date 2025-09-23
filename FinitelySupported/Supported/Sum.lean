import FinitelySupported.Supported.Basic
import FinitelySupported.PermAction.Sum

open PermAction

namespace Supported.Sum

variable {𝔸 X Y : Type*}
  [PermAction 𝔸 X] [Supported 𝔸 X]
  [PermAction 𝔸 Y] [Supported 𝔸 Y]

instance : Supported 𝔸 (X ⊕ Y) where
  has_supp x := by
    simp only [Sum.isSupp_iff]
    cases x with
    | inl x =>
      simp only [Sum.elim_inl]
      apply has_supp
    | inr x =>
      simp only [Sum.elim_inr]
      apply has_supp

@[simp]
lemma supp_eq (x : X ⊕ Y) : supp 𝔸 x = Sum.elim (supp 𝔸) (supp 𝔸) x := by
  classical
  ext a
  cases x with
  | inl x => simp only [mem_supp, Sum.isSupp_iff, Sum.elim_inl]
  | inr x => simp only [mem_supp, Sum.isSupp_iff, Sum.elim_inr]

end Supported.Sum
