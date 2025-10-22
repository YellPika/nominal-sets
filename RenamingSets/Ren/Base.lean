import RenamingSets.Ren.Basic

namespace RenamingSets.Ren

variable {𝔸 : Type*}

/--
Every renaming `σ` has a "base" renaming `base σ` such that `σ * base σ = σ` and
`σ (base σ a) = σ (base σ b) ↔ base σ a = base σ b`.
-/
noncomputable irreducible_def base (A : Finset 𝔸) (σ : Ren 𝔸) : Ren 𝔸 where
  toFun a :=
    open Classical in
    if h : a ∈ A then
      have : ∃b ∈ A, σ a = σ b := by use a
      this.choose
    else
      a
  exists_support' := by
    classical
    use A
    intro a ha
    grind

@[simp, grind =]
lemma coe_base (A : Finset 𝔸) (σ : Ren 𝔸) (a : 𝔸) : σ (σ.base A a) = σ a := by
  by_cases ha : a ∈ A
  · have : ∃b ∈ A, σ a = σ b := by use a
    simp only [base_def, mk_coe, ha, ↓reduceDIte]
    exact this.choose_spec.2.symm
  · simp only [base_def, mk_coe, ha, ↓reduceDIte]

@[simp, grind =]
lemma mul_base (A : Finset 𝔸) (σ : Ren 𝔸) : σ * σ.base A = σ := by
  ext a
  simp only [mul_coe, coe_base]

@[simp, grind =]
lemma mul_base_r (A : Finset 𝔸) (σ σ' : Ren 𝔸) : σ * (σ.base A * σ') = σ * σ' := by
  simp only [← mul_assoc, mul_base]

@[simp, grind =]
lemma base_idem (A : Finset 𝔸) (σ : Ren 𝔸) (a : 𝔸) : σ.base A (σ.base A a) = σ.base A a := by
  by_cases ha : a ∈ A
  · have h : ∃b ∈ A, σ a = σ b := by use a
    simp only [base_def, mk_coe, ha, ↓reduceDIte, h.choose_spec.1, ← h.choose_spec.2]
  · simp only [base_def, mk_coe, ha, ↓reduceDIte]

@[simp, grind =]
lemma base_idem' (A : Finset 𝔸) (σ : Ren 𝔸) : σ.base A * σ.base A = σ.base A := by
  ext a
  simp only [mul_coe, base_idem]

@[simp, grind =]
lemma base_mem (A : Finset 𝔸) (σ : Ren 𝔸) (a : 𝔸) : σ.base A a ∈ A ↔ a ∈ A := by
  by_cases ha : a ∈ A
  · have : ∃ b ∈ A, σ a = σ b := by use a
    simp only [base_def, mk_coe, ha, ↓reduceDIte, iff_true]
    exact this.choose_spec.1
  · simp only [ha, iff_false]
    intro ha'
    simp only [base_def, mk_coe, ha, ↓reduceDIte] at ha'

@[simp, grind =]
lemma base_of_notMem (σ : Ren 𝔸) {A a} (ha : a ∉ A) : σ.base A a = a := by
  simp only [base_def, mk_coe, ha, ↓reduceDIte]

@[grind =]
lemma base_eq_iff
    {a b : 𝔸} (A : Finset 𝔸) (ha : a ∈ A) (hb : b ∈ A) (σ : Ren 𝔸)
    : σ.base A a = σ.base A b ↔ σ a = σ b:= by
  have h₁ : ∃c ∈ A, σ a = σ c := by use a
  have h₂ : ∃c ∈ A, σ b = σ c := by use b
  apply Iff.intro
  · intro h
    simp only [base_def, mk_coe, ha, ↓reduceDIte, hb] at h
    rw [h₁.choose_spec.2, h₂.choose_spec.2, h]
  · intro h
    simp only [base_def, mk_coe, ha, ↓reduceDIte, h, hb]

end RenamingSets.Ren
