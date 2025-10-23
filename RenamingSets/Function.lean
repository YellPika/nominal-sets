import RenamingSets.PartialHom

namespace RenamingSets.Function

variable {𝔸 : Type*} [Infinite 𝔸]
  {X : Type*} [RenameAction 𝔸 X] [RenamingSet 𝔸 X]
  {Y : Type*} [RenameAction 𝔸 Y]

lemma ext'
    [DecidableEq 𝔸] (A : Finset 𝔸)
    {f : X → Y} (hf : IsSupportOfF A f)
    {g : X → Y} (hg : IsSupportOfF A g)
    (hA : ∀ x, supp 𝔸 x ∩ A = ∅ → f x = g x)
    : f = g := by
  replace ⟨hf⟩ := hf
  replace ⟨hg⟩ := hg
  ext x
  let B := supp 𝔸 x ∪ A
  have : rename (.unfresh (supp 𝔸 x) B * .fresh (supp 𝔸 x) B) x = x := by
    apply rename_congr'
    simp only [Ren.mul_coe]
    grind
  rw [← this]
  simp only [← rename_mul]
  rw [← hf, ← hg]
  · congr 1
    apply hA
    ext a
    simp only [
      Ren.fresh_injOn, supp_rename, Finset.mem_inter,
      Finset.mem_rename, rename_def, Finset.notMem_empty,
      iff_false, not_and, forall_exists_index, and_imp]
    grind
  · grind
  · grind

variable [RenamingSet 𝔸 Y]

@[simps -isSimp]
noncomputable instance : RenameAction 𝔸 (X → Y) where
  rename σ f :=
    open Classical in
    if hf : IsSupportedF 𝔸 f
    then (PartialHom.rename σ hf.choose_spec).extend
    else f

  rename_one f := by
    classical
    wlog hf : IsSupportedF 𝔸 f
    · simp only [hf, ↓reduceDIte]
    simp only [hf, ↓reduceDIte]

    suffices ∀{A}, (hf : IsSupportOfF A f) → (PartialHom.rename (1 : Ren 𝔸) hf).extend = f by
      apply this

    intro A hA
    apply ext' (A ∪ Ren.supp 1 ∪ A.image (1 : Ren 𝔸))
    · apply PartialHom.isSupportOfF_extend
    · have := hf.choose_spec
      grind
    · intro x hx
      rw [PartialHom.extend_eq]
      · simp only [PartialHom.rename_toFun, rename_one', id_eq]
      · exact hx

  rename_mul σ₁ σ₂ f := by
    classical
    wlog hf : IsSupportedF 𝔸 f
    · simp only [hf, ↓reduceDIte]
    simp only [hf, ↓reduceDIte, PartialHom.isSupportedF_extend]

    suffices ∀ {A B}
          (hA : IsSupportOfF A f)
          (hB : IsSupportOfF B (PartialHom.rename σ₂ hA).extend),
          (PartialHom.rename σ₁ hB).extend = (PartialHom.rename (σ₁ * σ₂) hA).extend by
      apply this

    intro A B hA hB
    apply ext' (
        B ∪ σ₁.supp ∪ B.image σ₁ ∪
        A ∪ σ₂.supp ∪ A.image σ₂ ∪
        (σ₁ * σ₂).supp ∪ A.image (σ₁ * σ₂))
    · apply PartialHom.isSupportOfF_extend'
      intro a ha
      simp only [Finset.union_assoc, Finset.mem_union] at ⊢ ha
      grind only
    · apply PartialHom.isSupportOfF_extend'
      intro a ha
      simp only [Finset.union_assoc, Finset.mem_union] at ⊢ ha
      grind only
    · intro x hx
      rw [PartialHom.extend_eq, PartialHom.extend_eq]
      · simp only [PartialHom.rename_toFun]
        rw [PartialHom.extend_eq]
        · simp only [PartialHom.rename_toFun, rename_mul]
        · simp only [
            Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
            Finset.mem_union, Finset.notMem_empty] at ⊢ hx
          grind only
      · simp only [
          Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
          Finset.mem_union, Finset.notMem_empty] at ⊢ hx
        grind only
      · simp only [
          Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
          Finset.mem_union, Finset.notMem_empty] at ⊢ hx
        grind only

lemma isSupportOfF_rename
    {A : Finset 𝔸}
    (σ : Ren 𝔸) (hσ₁ : σ.supp ⊆ A) (hσ₂ : ∀ a ∈ A, σ a ∈ A)
    {f : X → Y} (hf : IsSupportOfF A f)
    : IsSupportOfF A (rename σ f) := by
  classical
  change IsSupportOfF A (fun x ↦ _)
  simp only [rename_def]

  have hf' : IsSupportedF 𝔸 f := ⟨A, hf⟩
  simp only [hf', ↓reduceDIte]

  have lemma₁
      : (PartialHom.rename σ hf'.choose_spec).extend
      = (PartialHom.rename σ hf).extend := by
    apply ext' (A ∪ A.image σ ∪ hf'.choose ∪ hf'.choose.image σ ∪ σ.supp)
    · apply PartialHom.isSupportOfF_extend'
      intro a ha
      simp only [Finset.union_assoc, Finset.mem_union] at ⊢ ha
      grind only
    · apply PartialHom.isSupportOfF_extend'
      intro a ha
      simp only [Finset.union_assoc, Finset.mem_union] at ⊢ ha
      grind only
    · intro x hx
      rw [PartialHom.extend_eq, PartialHom.extend_eq]
      · simp only [PartialHom.rename_toFun]
      · simp only [
          Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
          Finset.mem_union, Finset.notMem_empty] at ⊢ hx
        grind only
      · simp only [
          Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
          Finset.mem_union, Finset.notMem_empty] at ⊢ hx
        grind only
  rw [lemma₁]

  apply PartialHom.isSupportOfF_extend'
  intro a ha
  simp only [Finset.union_assoc, Finset.mem_union] at ha
  cases ha with
  | inl ha => exact ha
  | inr ha =>
    cases ha with
    | inl ha => apply hσ₁ ha
    | inr ha =>
      simp only [Finset.mem_image] at ha
      rcases ha with ⟨a, ha, rfl⟩
      apply hσ₂ a ha

@[simp]
lemma isSupportedF_rename
    (σ : Ren 𝔸) (f : X → Y)
    : IsSupportedF 𝔸 (rename σ f) ↔ IsSupportedF 𝔸 f := by
  classical
  by_cases hf : IsSupportedF 𝔸 f
  · simp only [hf, iff_true]
    change IsSupportedF 𝔸 fun _ ↦ _
    simp only [rename_def, hf, ↓reduceDIte, PartialHom.isSupportedF_extend]
  · simp only [hf, iff_false]
    intro hf'
    change IsSupportedF 𝔸 fun _ ↦ _ at hf'
    simp only [rename_def, hf, ↓reduceDIte] at hf'

@[fun_prop]
lemma isSupportedF_rename'
    (σ : Ren 𝔸) {f : X → Y} (hf : IsSupportedF 𝔸 f)
    : IsSupportedF 𝔸 (rename σ f) := by
  simp only [isSupportedF_rename]
  exact hf

@[simp]
lemma rename_apply
    (σ : Ren 𝔸) {f : X → Y} (hf : IsSupportedF 𝔸 f) (x : X)
    : rename σ f (rename σ x) = rename σ (f x) := by
  classical

  generalize hA
    : hf.choose
        ∪ (isSupportedF_rename' σ hf).choose
        ∪ σ.supp
        ∪ supp 𝔸 x
        ∪ (supp 𝔸 x).image σ
        ∪ hf.choose.image σ
    = A
  let τ := Ren.fresh A A
  have : ∀a ∈ A, σ (τ a) = τ a := by
    intro a ha
    have : τ a ∉ σ.supp := by grind
    simpa only [Ren.mem_supp, ne_eq, Decidable.not_not] using this
  let τₜ := Ren.unfresh A A
  let π : Ren 𝔸 := {
    toFun a := if a ∈ A then τ a else if ∃b ∈ A, a = τ b then τₜ a else a
    exists_support' := by
      use A ∪ A.image τ
      intro a ha
      simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at ha
      grind
  }
  have π_coe {a} : π a = if a ∈ A then τ a else if ∃b ∈ A, a = τ b then τₜ a else a := rfl
  let σ' := π * σ * π
  have : ∀a ∈ supp 𝔸 x, (τₜ * σ' * τ) a = σ a := by
    intro a ha
    have h₁ : Ren.fresh A A a ∉ A := by grind
    have h₂ : ∃ b ∈ A, Ren.fresh A A a = Ren.fresh A A b := by grind
    have h₃ : Ren.unfresh A A (Ren.fresh A A a) = a := by grind
    have h₄ : σ a ∈ A := by grind
    simp only [Ren.mul_coe, π_coe, h₁, ↓reduceIte, h₂, h₃, h₄, Ren.unfresh_fresh₁, τₜ, σ', τ]
  have : ∀a ∈ supp 𝔸 (f (rename τ x)), (τₜ * σ' * σ) a = (σ * τₜ) a := by
    intro a ha
    simp only [Ren.mul_coe, π_coe, σ']
    replace ha := supp_apply hf.choose_spec _ ha
    simp only [Finset.mem_union] at ha
    cases ha with
    | inl ha =>
      replace ha : σ a ∈ A := by grind
      have h₁ : σ (τ (σ a)) = τ (σ a) := by grind
      have h₂ : τ (τ (σ a)) = τ (σ a) := by grind
      have h₃ : ∃ b ∈ A, τ (σ a) = τ b := by grind
      have h₄ : τₜ (τ (σ a)) = σ a := by grind
      have h₅ : τₜ a = a := by grind
      have h₆ : τₜ (σ a) = (σ a) := by grind
      simp only [ha, ↓reduceIte, h₁, h₂, h₃, h₄, apply_ite, h₆, ite_self, h₅]
    | inr ha =>
      have ha' := supp_rename_subset' _ _ _ ha
      rcases ha' with ⟨a, ha', rfl⟩
      have h₁ : σ (τ a) = τ a := by grind
      have h₂ : τ a ∉ A := by grind
      have h₃ : ∃ b ∈ A, τ a = τ b := by grind
      have h₄ : τₜ (τ a) = a := by grind
      have h₅ : σ a ∈ A := by grind
      have h₆ : τₜ (τ (σ a)) = (σ a) := by grind
      simp only [h₁, h₂, ↓reduceIte, h₃, h₄, h₅, h₆]
  have : ∀a ∈ (isSupportedF_rename' σ hf).choose, (τₜ * σ') a = a := by
    intro a ha
    have h₁ : a ∈ A := by grind
    have h₂ : σ (τ a) = τ a := by grind
    have h₃ : τ a ∉ A := by grind
    have h₄ : ∃ b ∈ A, τ a = τ b := by grind
    simp only [Ren.mul_coe, π_coe, h₁, ↓reduceIte, σ', h₂, h₃, h₄]
    grind
  have : rename σ x = rename (τₜ * σ') (rename τ x) := by
    simp only [rename_mul]
    apply rename_congr
    grind
  have : (rename σ f) (rename (τₜ * σ') (rename τ x))
       = rename (τₜ * σ') (rename σ f (rename τ x)) := by
    simp only [rename_mul]
    rw [(isSupportedF_rename' σ hf).choose_spec.eq (by grind)]
    simp only [rename_mul]
  have : rename σ f (rename τ x) = rename σ (f (rename τ x)) := by
    simp only [rename_def, hf, ↓reduceDIte]
    rw [PartialHom.extend_eq]
    · simp only [PartialHom.rename_toFun]
    · ext a
      simp only [Finset.union_assoc, Finset.mem_inter, Finset.mem_union, Ren.mem_supp, ne_eq,
        Finset.mem_image, Finset.notMem_empty, iff_false, not_and, not_or, Decidable.not_not,
        not_exists]
      intro ha
      replace ha := supp_rename_subset' _ _ _ ha
      rcases ha with ⟨a, ha, rfl⟩
      have : τ a ∉ A := by grind
      refine ⟨?_, ?_, ?_⟩
      · grind
      · have : τ a ∉ σ.supp := by grind
        simpa only [Ren.mem_supp, ne_eq, Decidable.not_not] using this
      · grind
  have : rename (τₜ * σ') (rename σ (f (rename τ x))) = rename (σ * τₜ) (f (rename τ x)) := by
    simp only [rename_mul]
    apply rename_congr
    grind
  have : rename (σ * τₜ) (f (rename τ x)) = rename σ (f (rename τₜ (rename τ x))) := by
    nth_rw 2 [←hf.choose_spec.eq]
    · simp only [rename_mul]
    · grind
  have : rename τₜ (rename τ x) = x := by
    simp only [rename_mul]
    apply rename_congr'
    simp only [Ren.mul_coe]
    grind
  grind

@[simp]
lemma rename_apply' (σ : Ren 𝔸) {f : X → Y} (hf : ¬ IsSupportedF 𝔸 f) : rename σ f = f := by
  ext x
  simp only [rename_def, hf, ↓reduceDIte]

@[simp, grind ←, grind →]
lemma isSupportOf_of_isSupportOfF
    (A : Finset 𝔸) (f : X → Y) (hf : IsSupportOfF A f)
    : IsSupportOf A f := by
  classical
  have hf' : IsSupportedF 𝔸 f := ⟨A, hf⟩
  simp only [isSupportOf_def]
  intro σ₁ σ₂ hσ
  apply ext' (A ∪ σ₁.supp ∪ σ₂.supp ∪ σ₁.supp.image σ₁ ∪ σ₂.supp.image σ₂)
  · apply isSupportOfF_rename
    · intro a ha
      simp only [Finset.mem_union]
      grind
    · intro a ha
      by_cases ha' : a ∈ σ₁.supp
      · simp only [Finset.mem_union, Finset.mem_image]
        grind only
      · simp only [Ren.mem_supp, ne_eq, Decidable.not_not] at ha'
        grind only
    · apply isSupportOfF_mono f ?_ hf
      simp only [Finset.union_assoc, Finset.le_eq_subset, Finset.subset_union_left]
  · apply isSupportOfF_rename
    · intro a ha
      simp only [Finset.mem_union]
      grind
    · intro a ha
      by_cases ha' : a ∈ σ₂.supp
      · simp only [Finset.mem_union, Finset.mem_image]
        grind only
      · simp only [Ren.mem_supp, ne_eq, Decidable.not_not] at ha'
        grind only
    · apply isSupportOfF_mono f ?_ hf
      simp only [Finset.union_assoc, Finset.le_eq_subset, Finset.subset_union_left]
  · intro x hx
    have : x = rename σ₁ x := by
      rw [rename_congr']
      intro a ha
      simp only [Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
        Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or,
        Decidable.not_not] at hx
      grind
    nth_rw 1 [this]
    have : x = rename σ₂ x := by
      rw [rename_congr']
      intro a ha
      simp only [Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
        Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or,
        Decidable.not_not] at hx
      grind
    nth_rw 2 [this]
    rw [rename_apply σ₁ hf', rename_apply σ₂ hf']
    apply rename_congr
    intro a ha
    replace ha := supp_apply hf x ha
    simp only [Finset.mem_union] at ha
    simp only [Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
      Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or,
      Decidable.not_not] at hx
    grind

end RenamingSets.Function
