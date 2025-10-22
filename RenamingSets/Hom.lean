import RenamingSets.PartialHom
import RenamingSets.Ren.Base

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

/-- Morphisms in the category of nominal renaming sets. -/
structure Hom (𝔸 X Y : Type*) [RenameAction 𝔸 X] [RenameAction 𝔸 Y] where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The function has a finite support. -/
  exists_support' : ∃ A : Finset 𝔸,
    ∀ ⦃σ⦄, (∀a ∈ A, σ a = a) →
    ∀ ⦃x⦄, rename σ (toFun x) = toFun (rename σ x)

namespace Hom

instance : FunLike (Hom 𝔸 X Y) X Y where
  coe := toFun
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simp only [mk.injEq] at ⊢ h
    rw [h]

@[simp]
lemma coe_mk (f : X → Y) (hf : _) (x : X) : mk (𝔸 := 𝔸) f hf x = f x := rfl

lemma exists_support (f : Hom 𝔸 X Y) : ∃ A : Finset 𝔸,
    ∀ ⦃σ⦄, (∀a ∈ A, σ a = a) →
    ∀ ⦃x⦄, rename σ (f x) = f (rename σ x) := by
  exact f.exists_support'

lemma exists_support_subset
    [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [Infinite 𝔸] [DecidableEq 𝔸]
    (f : Hom 𝔸 X Y) (x)
    : supp 𝔸 (f x) ⊆ f.exists_support.choose ∪ supp 𝔸 x := by
  classical
  intro a ha
  by_contra! ha'
  obtain ⟨b, hb⟩ := (f.exists_support.choose ∪ {a}).exists_notMem
  have hx : rename (Ren.restrict {a} fun _ ↦ b) x = x := by
    apply rename_congr'
    simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
    grind
  have := f.exists_support.choose_spec
    (σ := .restrict {a} fun _ ↦ b)
    (by simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
        grind)
    (x := x)
  rw [hx] at this
  rw [←this] at ha
  replace ha := supp_rename_subset' _ _ _ ha
  simp only [Ren.restrict_coe, Finset.mem_singleton] at ha
  grind

@[ext]
lemma ext {f g : Hom 𝔸 X Y} (h : ∀ x, f x = g x) : f = g := by
  rcases f
  rcases g
  simp only [coe_mk, mk.injEq] at ⊢ h
  ext x
  apply h

lemma ext'
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X]
    {f g : Hom 𝔸 X Y} (A : Finset 𝔸)
    (hA : ∀ x, supp 𝔸 x ∩ A = ∅ → f x = g x)
    : f = g := by
  obtain ⟨B, hB⟩ := f.exists_support
  obtain ⟨C, hC⟩ := g.exists_support
  ext x
  let D := supp 𝔸 x ∪ B ∪ C ∪ A
  have : rename (.unfresh (supp 𝔸 x) D * .fresh (supp 𝔸 x) D) x = x := by
    apply rename_congr'
    simp only [Ren.mul_coe]
    grind
  rw [← this]
  simp only [← rename_mul]
  rw [← hB, ← hC]
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

variable [DecidableEq 𝔸] [Infinite 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]

/-- Every `PartialHom` can be uniquely extended to a compatible `Hom`. -/
noncomputable irreducible_def extend {A : Finset 𝔸} (f : PartialHom A X Y) : Hom 𝔸 X Y where
  toFun x := f.extend x
  exists_support' := by
    use A
    grind

@[simp, grind =]
lemma extend_eq
    {A : Finset 𝔸} (f : PartialHom A X Y) {x} (hx : supp 𝔸 x ∩ A = ∅)
    : extend f x = f ⟨x, hx⟩ := by
  simp only [extend_def, coe_mk, hx, PartialHom.extend_eq]

@[simps]
private def rename₀
    (σ : Ren 𝔸) (f : Hom 𝔸 X Y)
    : PartialHom (f.exists_support.choose ∪ σ.supp ∪ f.exists_support.choose.image σ) X Y where
  toFun x := rename σ (f x)
  supported' σ' hσ' x hx₁ hx₂ := by
    dsimp only

    let μ : Ren 𝔸 := .base (supp 𝔸 x) σ'

    have lemma₁ : rename σ' x = rename σ' (rename μ x) := by
      simp only [rename_mul]
      apply rename_congr
      grind
    rw [lemma₁]

    have lemma₂ : f (rename σ' (rename μ x)) = rename σ' (f (rename μ x)) := by
      rw [f.exists_support.choose_spec]
      grind
    rw [lemma₂]

    have lemma₃
        : rename σ (rename σ' (f (rename μ x)))
        = rename σ' (rename σ (f (rename μ x))) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha
      simp only [Ren.mul_coe]
      have := exists_support_subset f _ ha
      simp only [Finset.mem_union] at this
      cases this with
      | inl this => grind
      | inr this =>
        have h₁ : σ' a ∈ supp 𝔸 (rename σ' x) := by
          rw [lemma₁, supp_rename]
          · simp only [Finset.mem_rename, rename_def]
            use a
          · intro b hb c hc hbc
            rcases supp_rename_subset' _ _ _ hb with ⟨b, hb', rfl⟩
            rcases supp_rename_subset' _ _ _ hc with ⟨c, hc', rfl⟩
            grind [= Ren.restrict_coe]
        have h₂ : a ∈ supp 𝔸 x := by
          rcases supp_rename_subset' _ _ _ this with ⟨a, ha', rfl⟩
          grind
        have h₃ : σ (σ' a) = σ' a ∧ σ a = a := by
          simp only [
            Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
            Finset.mem_union, Ren.mem_supp] at hx₁ hx₂
          grind
        simp only [h₃]
    rw [lemma₃]

    have lemma₄ : f (rename μ x) = rename μ (f x) := by
      rw [f.exists_support.choose_spec]
      simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
      grind
    rw [lemma₄]

    have lemma₅ : rename σ (rename μ (f x)) = rename μ (rename σ (f x)) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha
      replace ha := exists_support_subset f _ ha
      simp only [Finset.mem_union] at ha
      cases ha with
      | inl ha =>
        simp only [Ren.mul_coe]
        have : a ∉ supp 𝔸 x := by
          simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
          grind
        have : σ a ∉ supp 𝔸 x := by
          simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
          grind
        grind
      | inr ha =>
        have : σ a = a ∧ σ (μ a) = μ a := by
          simp only [
            Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
            Finset.mem_union, Ren.mem_supp] at hx₁
          grind
        simp only [Ren.mul_coe, this]
    rw [lemma₅]

    simp only [rename_mul, Ren.mul_base_r, μ]

@[simps -isSimp]
noncomputable instance : RenameAction 𝔸 (Hom 𝔸 X Y) where
  rename σ f := extend (rename₀ σ f)

  rename_one f := by
    apply ext' f.exists_support.choose
    intro x hx
    rw [extend_eq]
    · simp only [rename₀_toFun, rename_one', id_eq]
    · ext a
      simp only [Finset.union_assoc, Finset.mem_inter, Finset.mem_union, Ren.mem_supp, Ren.one_coe,
        ne_eq, not_true_eq_false, Finset.mem_image, exists_eq_right, Finset.notMem_empty, iff_false,
        not_and]
      simp only [Finset.ext_iff, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and] at hx
      grind

  rename_mul σ₁ σ₂ f := by
    apply ext' <|
      (extend (rename₀ σ₂ f)).exists_support.choose ∪
      (extend (rename₀ σ₂ f)).exists_support.choose.image σ₁ ∪
      f.exists_support.choose ∪
      f.exists_support.choose.image (σ₁ * σ₂) ∪
      f.exists_support.choose.image σ₂ ∪
      σ₁.supp ∪
      σ₂.supp ∪
      (σ₁ * σ₂).supp
    intro a hx
    simp only [Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
      Finset.mem_image, Ren.mul_coe, Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and,
      not_or, not_exists, Decidable.not_not] at hx
    rw [extend_eq, extend_eq, rename₀_toFun, extend_eq]
    · simp only [rename₀_toFun, rename_mul]
    · ext a
      simp only [Finset.union_assoc, Finset.mem_inter, Finset.mem_union, Finset.mem_image,
        Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or, not_exists,
        Decidable.not_not]
      grind
    · ext a
      simp only [Finset.union_assoc, Finset.mem_inter, Finset.mem_union, Finset.mem_image,
        Ren.mul_coe, Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or,
        not_exists, Decidable.not_not]
      grind
    · ext a
      simp only [Finset.union_assoc, Finset.mem_inter, Finset.mem_union, Finset.mem_image,
        Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or, not_exists,
        Decidable.not_not]
      grind

instance : RenamingSet 𝔸 (Hom 𝔸 X Y) where
  exists_support f := by
    classical
    use f.exists_support.choose
    simp only [isSupportOf_def, rename_def]
    intro σ₁ σ₂ hσ
    apply ext' <|
      f.exists_support.choose
        ∪ σ₁.supp
        ∪ σ₂.supp
        ∪ f.exists_support.choose.image σ₁
        ∪ f.exists_support.choose.image σ₂
    intro x hx
    rw [extend_eq, extend_eq]
    · dsimp only [rename₀_toFun]
      apply rename_congr
      intro a ha
      replace ha := exists_support_subset f _ ha
      simp only [Finset.mem_union] at ha
      cases ha with
      | inl h => exact hσ _ h
      | inr h =>
        have : σ₁ a = a ∧ σ₂ a = a := by
          simp only [
            Finset.union_assoc, Finset.ext_iff, Finset.mem_inter,
            Finset.mem_union, Ren.mem_supp] at hx
          grind
        grind
    · grind
    · grind

@[simp]
lemma rename_apply
    (σ : Ren 𝔸) (f : Hom 𝔸 X Y) (x : X)
    : rename σ f (rename σ x) = rename σ (f x) := by
  classical
  generalize hA
    : f.exists_support.choose
        ∪ (rename σ f).exists_support.choose
        ∪ σ.supp
        ∪ supp 𝔸 x
        ∪ (supp 𝔸 x).image σ
        ∪ f.exists_support.choose.image σ
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
    replace ha := exists_support_subset f _ ha
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
  have : ∀a ∈ (rename σ f).exists_support.choose, (τₜ * σ') a = a := by
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
    rw [(rename σ f).exists_support.choose_spec (by grind)]
    simp only [rename_mul]
  have : rename σ f (rename τ x) = rename σ (f (rename τ x)) := by
    simp only [rename_def]
    rw [extend_eq]
    · simp only [rename₀_toFun]
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
    nth_rw 2 [←f.exists_support.choose_spec]
    · simp only [rename_mul]
    · grind
  have : rename τₜ (rename τ x) = x := by
    simp only [rename_mul]
    apply rename_congr'
    simp only [Ren.mul_coe]
    grind
  grind

lemma supp_subset_iff
    (f : Hom 𝔸 X Y) (A : Finset 𝔸)
    : supp 𝔸 f ⊆ A
    ↔ ∀ σ, (∀ a ∈ A, σ a = a) → ∀ x, rename σ (f x) = f (rename σ x) := by
  apply Iff.intro
  · intro h σ hσ x
    rw [← rename_apply, rename_congr']
    grind
  · intro h
    suffices IsSupportOf A f by exact supp_min this
    simp only [isSupportOf_def']
    intro σ hσ
    apply ext' σ.supp
    intro x hx
    have : ∀a ∈ supp 𝔸 x, σ a = a := by
      simp only [Finset.ext_iff, Finset.mem_inter, Ren.mem_supp] at hx
      grind
    have : f x = f (rename σ x) := by
      rw [rename_congr']
      grind
    have : rename σ (f x) = rename σ f (rename σ x) := by
      rw [rename_apply]
    have : rename σ x = x := by
      apply rename_congr'
      grind
    grind

lemma supp_subset
    (f : Hom 𝔸 X Y) (x : X)
    : supp 𝔸 (f x) ⊆ supp 𝔸 f ∪ supp 𝔸 x := by
  intro a ha
  have : ∀ σ, (∀ a ∈ supp 𝔸 f, σ a = a) → ∀ x, rename σ (f x) = f (rename σ x) := by
    rw [← supp_subset_iff]
  simp only [Finset.mem_union]
  by_contra! ha'
  obtain ⟨b, hb⟩ := (supp 𝔸 f ∪ {a}).exists_notMem
  specialize this
    (.restrict {a} fun _ ↦ b)
    (by simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
        grind)
    x
  have hx : (rename (Ren.restrict {a} fun x ↦ b) x) = x := by
    apply rename_congr'
    simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
    grind
  rw [hx] at this
  rw [←this] at ha
  replace ha := supp_rename_subset' _ _ _ ha
  simp only [Ren.restrict_coe, Finset.mem_singleton] at ha
  grind

@[simps]
private def curry₀
    [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [RenamingSet 𝔸 Z]
    (f : Hom 𝔸 (X × Y) Z) (x : X)
    : Hom 𝔸 Y Z where
  toFun y := f (x, y)
  exists_support' := by
    use supp 𝔸 f ∪ supp 𝔸 x
    intro σ hσ y
    simp only [← rename_apply, Prod.rename_mk]
    rw [rename_congr', rename_congr']
    · grind
    · grind

/-- Currying for morphisms. -/
@[simps!]
def curry
    [Infinite 𝔸] [DecidableEq 𝔸]
    [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [RenamingSet 𝔸 Z]
    (f : Hom 𝔸 (X × Y) Z)
    : Hom 𝔸 X (Hom 𝔸 Y Z) where
  toFun := curry₀ f
  exists_support' := by
    use supp 𝔸 f
    intro σ hσ x
    apply ext' (supp 𝔸 x ∪ supp 𝔸 f ∪ σ.supp)
    intro y hy
    simp only [curry₀_toFun]
    have : rename σ y = y := by
      apply rename_congr'
      simp only [Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
        Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or,
        Decidable.not_not] at hy
      grind
    rw [←this, rename_apply]
    simp only [curry₀_toFun, ← rename_apply, Prod.rename_mk]
    rw [rename_congr']
    grind

/-- The evaluation morphism. -/
@[simps]
def eval
    [Infinite 𝔸] [DecidableEq 𝔸]
    [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [RenamingSet 𝔸 Z]
    : Hom 𝔸 (Hom 𝔸 X Y × X) Y where
  toFun x := x.1 x.2
  exists_support' := by
    use ∅
    intro σ hσ x
    simp only [rename_apply, Prod.rename_def]

end Hom

end RenamingSets
