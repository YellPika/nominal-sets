import RenamingSets.Finset
import RenamingSets.Ren.Base
import RenamingSets.Ren.Fresh
import RenamingSets.Ren.Transfer

namespace RenamingSets

variable {𝔸} [DecidableEq 𝔸]

/--
`PartialHom A X Y` is the type of partial morphisms which are defined everywhere
except for those elements whose support intersects `A`.
-/
structure PartialHom
    (A : Finset 𝔸)
    (X : Type*) [RenameAction 𝔸 X] [RenamingSet 𝔸 X]
    (Y : Type*) [RenameAction 𝔸 Y] [RenamingSet 𝔸 Y] where
  /-- The underlying function. -/
  toFun : {x : X // supp 𝔸 x ∩ A = ∅} → Y
  /-- The function has a finite support. -/
  supported' :
    ∀ ⦃σ⦄, (∀ a ∈ A, σ a = a) →
    ∀ ⦃x⦄ hx₁ hx₂, rename σ (toFun ⟨x, hx₁⟩) = toFun ⟨rename σ x, hx₂⟩

namespace PartialHom

variable {X Y : Type*} [RenameAction 𝔸 X] [RenamingSet 𝔸 X] [RenameAction 𝔸 Y] [RenamingSet 𝔸 Y]

instance {A : Finset 𝔸} : FunLike (PartialHom A X Y) {x : X // supp 𝔸 x ∩ A = ∅} Y where
  coe := toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    simp only [mk.injEq] at ⊢ h
    exact h

lemma supported
    {A : Finset 𝔸} (f : PartialHom A X Y)
    : ∀ ⦃σ⦄, (∀ a ∈ A, σ a = a) →
      ∀ ⦃x⦄ hx₁ hx₂, rename σ (f ⟨x, hx₁⟩) = f ⟨rename σ x, hx₂⟩ :=
  f.supported'

lemma supp_subset [Infinite 𝔸]
    {A : Finset 𝔸} (f : PartialHom A X Y) (x : {x : X // supp 𝔸 x ∩ A = ∅ })
    : supp 𝔸 (f x) ⊆ A ∪ supp 𝔸 x.val := by
  intro a ha
  simp only [Finset.mem_union]
  by_contra! ha'

  obtain ⟨b, hb⟩ := (A ∪ {a}).exists_notMem

  have hx₁ : ∀ a ∈ supp 𝔸 x.val, a ∉ A := by
    have := x.property
    simpa only [Finset.ext_iff, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      using this

  have hx₂ : rename (.assign a b) x.val = x.val := by
    apply rename_congr'
    simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
    grind

  have hx₃ : rename (.assign a b) (f x) = f x := by
    have := f.supported
      (σ := .assign a b)
      (by simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
          grind)
      x.property
      (by grind)
    simpa only [Subtype.coe_eta, hx₂] using this

  have hx₅ : ∃ c ∈ supp 𝔸 (f x), Ren.assign a b c = a := by
    grind [→ supp_rename_subset']

  simp only [Ren.restrict_coe, Finset.mem_singleton] at hx₅
  grind

/-- Any `PartialHom` has a unique, finitely-supported total extension. -/
@[irreducible]
noncomputable def extend
    [Infinite 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    {A : Finset 𝔸} (f : PartialHom A X Y) (x : X)
    : Y :=
  rename (.unfresh (supp 𝔸 x) A)
    <| f
    <| Subtype.mk (rename (.fresh (supp 𝔸 x) A) x)
    <| by ext a
          simp only [
            Ren.fresh_injOn, supp_rename, Finset.mem_inter,
            Finset.mem_rename, rename_def]
          grind

lemma extend_def
    [Infinite 𝔸]
    {A : Finset 𝔸} {x : X}
    (σ σ' : Ren 𝔸)
    (hσ₁ : ∀ a ∈ supp 𝔸 x, σ a ∉ A)
    (hσ₂ : ∀ a ∈ supp 𝔸 x, σ' (σ a) = a)
    (hσ₃ : ∀ a ∈ A, σ' a = a)
    (f : PartialHom A X Y)
    : extend f x
    = (rename σ'
        <| f
        <| Subtype.mk (rename σ x)
        <| by ext a
              grind [→ supp_rename_subset']) := by
  classical
  unfold extend

  have σ_injOn : Set.InjOn σ (supp 𝔸 x) := by
    intro _
    grind

  let τ := Ren.transfer (supp 𝔸 x) σ (.fresh (supp 𝔸 x) A)
  let τ' := Ren.transfer (supp 𝔸 x) (.fresh (supp 𝔸 x) A) σ

  have lemma₁ : rename σ x = rename (τ' * τ * σ) x := by
    grind [= Ren.mul_coe, ← rename_congr]

  have lemma₂ : supp 𝔸 (rename τ (rename σ x)) ∩ A = ∅ := by
    ext a
    simp only [rename_mul, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha
    rcases supp_rename_subset' _ _ _ ha with ⟨a, ha', rfl⟩
    grind [= Ren.mul_coe]

  have lemma₃ : rename (τ * σ) x = rename (.fresh (supp 𝔸 x) A) x := by
    apply rename_congr
    grind [= Ren.mul_coe]

  have lemma₄
      : ∀a ∈ A ∪ supp 𝔸 (rename (.fresh (supp 𝔸 x) A) x),
        Ren.unfresh (supp 𝔸 x) A a = σ' (τ' a) := by
    simp only [Ren.fresh_injOn, supp_rename, Finset.mem_union, Finset.mem_rename, rename_def]
    grind

  simp only [lemma₁]
  simp only [← rename_mul]
  nth_rw 2 [← f.supported]
  · simp only [rename_mul, lemma₃]
    apply rename_congr
    intro a ha
    apply lemma₄
    apply supp_subset f _ ha
  · grind
  · apply lemma₂

@[simp, grind =]
lemma extend_eq
    [Infinite 𝔸] {A : Finset 𝔸}
    (f : PartialHom A X Y) (x : X) (hx : supp 𝔸 x ∩ A = ∅)
    : extend f x = f ⟨x, hx⟩ := by
  have lem : rename (Ren.unfresh (supp 𝔸 x) A * Ren.fresh (supp 𝔸 x) A) x = x := by
    apply rename_congr'
    intro a ha
    simp only [Ren.mul_coe, ha, Ren.unfresh_fresh₁]

  rw [extend_def (.fresh (supp 𝔸 x) A) (.unfresh (supp 𝔸 x) A)]
  · rw [f.supported]
    · simp only [rename_mul, lem]
    · grind
    · simp only [rename_mul, lem, hx]
  · grind
  · grind
  · grind

@[simp, grind ←]
lemma isSupportOfF_extend
    [Infinite 𝔸] {A : Finset 𝔸}
    (f : PartialHom A X Y)
    : IsSupportOfF A (extend f) := by
  simp only [isSupportOfF_def]
  intro σ hσ x

  let τ := Ren.fresh (rename σ (supp 𝔸 x)) A
  let τ' := Ren.unfresh (rename σ (supp 𝔸 x)) A
  let μ := Ren.fresh (supp 𝔸 x) A
  let μ' := Ren.unfresh (supp 𝔸 x) A
  let σ' := Ren.transfer (supp 𝔸 x) μ (τ * σ)

  have lemma₁ : rename τ (rename σ x) = rename σ' (rename μ x) := by
    simp only [rename_mul]
    apply rename_congr
    grind [= Ren.mul_coe, = Ren.mk_coe]

  have lemma₂ : ∀a ∈ A ∪ supp 𝔸 (rename μ x), (σ * μ') a = (τ' * σ') a := by
    grind [= Ren.mul_coe, = rename_def]

  nth_rw 2 [extend_def τ τ'
    (by grind [→ supp_rename_subset'])
    (by grind [→ supp_rename_subset'])
    (by grind)]

  simp only [lemma₁]
  rw [← f.supported
    (by grind)
    (by grind [→ supp_rename_subset'])]

  nth_rw 1 [extend_def μ μ'
    (by grind [→ supp_rename_subset'])
    (by grind [→ supp_rename_subset'])
    (by grind)]

  simp only [rename_mul]
  apply rename_congr
  intro a ha
  apply lemma₂
  exact supp_subset f ⟨rename μ x, _⟩ ha

@[simp, grind ←]
lemma isSupportOfF_extend'
    [Infinite 𝔸] {A B : Finset 𝔸}
    (f : PartialHom A X Y) (h : A ⊆ B)
    : IsSupportOfF B (extend f) := by
  apply isSupportOfF_mono
  · exact h
  · apply isSupportOfF_extend

@[simp, grind ←, fun_prop]
lemma isSupportedF_extend
    [Infinite 𝔸] {A : Finset 𝔸}
    (f : PartialHom A X Y)
    : IsSupportedF 𝔸 (extend f) := by
  use A
  simp only [isSupportOfF_extend]

/-- Every finitely-supported function gives rise to a partial renaming function. -/
@[simps]
def rename
    [Infinite 𝔸]
    (σ : Ren 𝔸) {A : Finset 𝔸} {f : X → Y} (hf : IsSupportOfF A f)
    : PartialHom (A ∪ σ.supp ∪ A.image σ) X Y where
  toFun x := RenamingSets.rename σ (f x)
  supported' σ' hσ' x hx₁ hx₂ := by
    dsimp only

    replace hx₁ : ∀ a ∈ supp 𝔸 x, a ∉ A ∧ a ∉ σ.supp ∧ a ∉ A.image σ := by
      simp only [
        Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
        Finset.notMem_empty, iff_false, not_and, not_or] at hx₁
      exact hx₁

    replace hx₂ : ∀ a ∈ supp 𝔸 (RenamingSets.rename σ' x), a ∉ A ∧ a ∉ σ.supp ∧ a ∉ A.image σ := by
      simp only [
        Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
        Finset.notMem_empty, iff_false, not_and, not_or] at hx₂
      exact hx₂

    let μ : Ren 𝔸 := .base (supp 𝔸 x) σ'

    have lemma₁ : RenamingSets.rename σ' x = RenamingSets.rename σ' (RenamingSets.rename μ x) := by
      simp only [rename_mul]
      apply rename_congr
      simp only [Ren.mul_base, implies_true, μ]
    rw [lemma₁]

    have lemma₂
        : f (RenamingSets.rename σ' (RenamingSets.rename μ x))
        = RenamingSets.rename σ' (f (RenamingSets.rename μ x)) := by
      rw [hf.eq]
      intro a ha
      apply hσ'
      simp only [Finset.union_assoc, Finset.mem_union, ha, Finset.mem_image, true_or]
    rw [lemma₂]

    have lemma₃
        : RenamingSets.rename σ (RenamingSets.rename σ' (f (RenamingSets.rename μ x)))
        = RenamingSets.rename σ' (RenamingSets.rename σ (f (RenamingSets.rename μ x))) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha
      simp only [Ren.mul_coe]
      have := supp_apply hf _ ha
      simp only [Finset.mem_union] at this
      cases this with
      | inl this =>
        rw [hσ', hσ'] <;> grind
      | inr this =>
        have h₁ : σ' a ∈ supp 𝔸 (RenamingSets.rename σ' x) := by
          rw [lemma₁, supp_rename]
          · simp only [Finset.mem_rename, rename_def]
            use a
          · intro b hb c hc hbc
            rcases supp_rename_subset' _ _ _ hb with ⟨b, hb', rfl⟩
            rcases supp_rename_subset' _ _ _ hc with ⟨c, hc', rfl⟩
            simpa only [hb', hc', Ren.base_eq_iff, Ren.coe_base, μ] using hbc
        have h₂ : a ∈ supp 𝔸 x := by
          rcases supp_rename_subset' _ _ _ this with ⟨a, ha', rfl⟩
          simp only [Ren.base_of_mem, ha', μ]
        have h₃ : σ (σ' a) = σ' a := by
          have h : σ' a ∉ σ.supp := by grind
          simpa only [Ren.mem_supp, ne_eq, Decidable.not_not] using h
        have h₄ : σ a = a := by
          have h : a ∉ σ.supp := by grind
          simpa only [Ren.mem_supp, ne_eq, Decidable.not_not] using h
        simp only [h₃, h₄]
    rw [lemma₃]

    have lemma₄ : f (RenamingSets.rename μ x) = RenamingSets.rename μ (f x) := by
      rw [hf.eq]
      intro a ha
      have h : a ∉ supp 𝔸 x := by grind
      simp only [h, not_false_eq_true, Ren.base_of_notMem, μ]
    rw [lemma₄]

    have lemma₅
        : RenamingSets.rename σ (RenamingSets.rename μ (f x))
        = RenamingSets.rename μ (RenamingSets.rename σ (f x)) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha
      replace ha := supp_apply hf _ ha
      simp only [Finset.mem_union] at ha
      cases ha with
      | inl ha =>
        simp only [Ren.mul_coe]
        have h₁ : a ∉ supp 𝔸 x := by grind
        have h₂ : σ a ∉ supp 𝔸 x := by grind
        simp only [h₁, not_false_eq_true, Ren.base_of_notMem, h₂, μ]
      | inr ha =>
        have : σ a = a ∧ σ (μ a) = μ a := by
          simp only [Ren.mem_supp, ne_eq, Decidable.not_not] at hx₁
          have : μ a ∈ supp 𝔸 x := by grind
          simp only [ha, hx₁, this, and_self]
        simp only [Ren.mul_coe, this]
    rw [lemma₅]

    simp only [rename_mul, Ren.mul_base_r, μ]

end PartialHom

end RenamingSets
