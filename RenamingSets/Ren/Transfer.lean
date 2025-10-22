import RenamingSets.Ren.Basic

namespace RenamingSets.Ren

variable {𝔸 : Type*}

noncomputable irreducible_def transfer (A : Finset 𝔸) (σ₁ σ₂ : Ren 𝔸) : Ren 𝔸 where
  toFun a :=
    open Classical in
    if h : ∃b ∈ A, a = σ₁ b then σ₂ h.choose else a
  exists_support' := by
    classical
    use A.image σ₁
    grind

@[simp, grind =]
lemma transfer_of_mem
    {A : Finset 𝔸} {σ₁ σ₂ : Ren 𝔸} (hσ₁ : Set.InjOn σ₁ A) {a} (ha : a ∈ A)
    : transfer A σ₁ σ₂ (σ₁ a) = σ₂ a := by
  have : ∃ b ∈ A, σ₁ a = σ₁ b := by grind
  simp only [transfer_def, mk_coe, this, ↓reduceDIte]
  change σ₂ this.choose = σ₂ a
  congr 1
  apply hσ₁
  · exact this.choose_spec.1
  · exact ha
  · exact this.choose_spec.2.symm

@[simp, grind =]
lemma transfer_of_notMem
    [DecidableEq 𝔸]
    {A : Finset 𝔸} {σ₁ σ₂ : Ren 𝔸} {a} (ha : ∀ x ∈ A, σ₁ x ≠ a)
    : transfer A σ₁ σ₂ a = a := by
  simp only [transfer_def, mk_coe]
  grind

end RenamingSets.Ren
