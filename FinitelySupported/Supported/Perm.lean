import FinitelySupported.PermAction.Perm
import FinitelySupported.Supported.Basic

open PermAction

namespace Supported.Perm

variable {𝔸 : Type*}

instance : Supported 𝔸 (Perm 𝔸) where
  has_supp π := by
    classical
    use π.supp
    simp only [PermAction.Perm.isSupp_supp]

@[simp]
lemma supp_eq [Infinite 𝔸] (π : Perm 𝔸) : Supported.supp 𝔸 π = π.supp := by
  classical
  ext a
  apply Iff.intro
  · simp only [mem_supp, Perm.mem_supp, ne_eq]
    intro h₁ h₂
    specialize h₁ π.supp
    simp only [PermAction.Perm.isSupp_supp, Perm.mem_supp, ne_eq, forall_const] at h₁
    contradiction
  · simp only [Perm.mem_supp, ne_eq, mem_supp]
    intro ha A hA
    by_contra ha'
    obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (A ∪ {a, π a})
    simp only [Finset.union_insert, Finset.union_singleton, Finset.mem_insert, not_or] at hb
    rw [IsSupp.swap] at hA
    specialize hA ha' hb.2.2
    rw [Perm.ext_iff] at hA
    specialize hA a
    simp only [Perm.perm_def, Perm.inv_swap, Perm.mul_toFun, Perm.swap_toFun, ↓reduceIte] at hA
    by_cases hbb : b = π b
    · simp only [← hbb, ↓reduceIte] at hA
      grind
    · simp only [hbb, ↓reduceIte] at hA
      by_cases hab : a = π b
      · subst hab
        grind
      · simp only [hab, ↓reduceIte] at hA
        replace hA := Perm.injective π hA
        grind

end Supported.Perm
