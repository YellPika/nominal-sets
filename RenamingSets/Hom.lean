import RenamingSets.Finset
import Mathlib.Data.Part

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

/-- Morphisms in the category of nominal renaming sets. -/
structure Hom (𝔸 X Y : Type*) [RenameAction 𝔸 X] [RenameAction 𝔸 Y] where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The function has a nominal support. -/
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

lemma exists_support (f : Hom 𝔸 X Y) : ∃ A : Finset 𝔸,
    ∀ ⦃σ⦄, (∀a ∈ A, σ a = a) →
    ∀ ⦃x⦄, rename σ (f x) = f (rename σ x) := by
  exact f.exists_support'

@[ext]
lemma ext {f g : Hom 𝔸 X Y} (h : ∀ x, f x = g x) : f = g := by
  rcases f
  rcases g
  simp only [DFunLike.coe, mk.injEq] at ⊢ h
  ext x
  apply h

private lemma exists_fresh_inj
    [Infinite 𝔸] (A : Finset 𝔸) (B : Finset 𝔸)
    : ∃f : 𝔸 → 𝔸, Set.InjOn f A ∧ (∀a ∈ A, f a ∉ B) ∧ (∀a ∉ A, f a = a) := by
  classical
  induction A using Finset.induction with
  | empty =>
    use fun a ↦ a
    simp only [
      Finset.coe_empty, Set.injOn_empty, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, not_false_eq_true, and_self]
  | insert a s ha ih =>
    obtain ⟨f, hf₁, hf₂, hf₃⟩ := ih
    obtain ⟨b, hb⟩ := (B ∪ s.image f).exists_notMem
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hb
    use fun c ↦ if c = a then b else f c
    refine ⟨?_, ?_, ?_⟩
    · intro c₁ hc₁ c₂ hc₂ hc
      simp only at hc
      wlog hc₁a : c₁ ≠ a
      · grind
      wlog hc₂a : c₂ ≠ a
      · grind
      apply hf₁ <;> grind
    · grind
    · grind

private noncomputable def fresh [Infinite 𝔸] (A B : Finset 𝔸) : Ren 𝔸 where
  toFun := (exists_fresh_inj A B).choose
  exists_support' := by
    use A
    have := Classical.choose_spec (exists_fresh_inj A B)
    exact this.2.2

@[simp, grind ←]
private lemma fresh_inj [Infinite 𝔸] (A B : Finset 𝔸) : Set.InjOn (fresh A B) A := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  exact this.1

private lemma fresh_of_mem [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ A, fresh A B a ∉ B := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  exact this.2.1

@[grind ←]
private lemma fresh_of_mem' [Infinite 𝔸] (A B C : Finset 𝔸) : ∀a ∈ A, C ⊆ B → fresh A B a ∉ C := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  simp only [DFunLike.coe]
  grind

@[simp, grind =]
private lemma fresh_of_notMem [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∉ A, fresh A B a = a := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  exact this.2.2

@[simps -isSimp]
private noncomputable def unfresh [Infinite 𝔸] (A B : Finset 𝔸) : Ren 𝔸 where
  toFun a :=
    open Classical in
    if h : ∃b ∈ A, fresh A B b = a then h.choose else a
  exists_support' := by
    classical
    use A.image (fresh A B)
    grind

@[simp, grind =]
private lemma unfresh_of_mem [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ B, unfresh A B a = a := by
  simp only [unfresh_coe, dite_eq_right_iff, forall_exists_index, forall_and_index]
  intro a ha b hb rfl
  have := fresh_of_mem A B
  grind

@[grind =]
private lemma unfresh_of_not_fresh
    [Infinite 𝔸] (A B : Finset 𝔸)
    : ∀ a, (∀ b ∈ A, a ≠ fresh A B b) → unfresh A B a = a := by
  simp only [unfresh_coe]
  grind

@[simp, grind =]
private lemma unfresh_fresh₁
    [Infinite 𝔸] (A B : Finset 𝔸)
    : ∀a ∈ A, unfresh A B (fresh A B a) = a := by
  intro a ha
  have : ∃ b ∈ A, (fresh A B) b = (fresh A B) a := by grind
  simp only [unfresh_coe, this, ↓reduceDIte]
  exact fresh_inj A B this.choose_spec.1 ha this.choose_spec.2

@[simp, grind =]
private lemma unfresh_fresh₂
    [Infinite 𝔸] (A B : Finset 𝔸)
    : ∀a ∈ B, unfresh A B (fresh A B a) = a := by
  intro a ha
  simp only [unfresh_coe]
  by_cases ha' : a ∈ A
  · have : ∃b ∈ A, fresh A B b = fresh A B a := by use a
    simp only [this, ↓reduceDIte]
    have := Classical.choose_spec this
    apply fresh_inj A B this.1 ha' this.2
  · simp only [
      ha', not_false_eq_true, fresh_of_notMem, dite_eq_right_iff,
      forall_exists_index, forall_and_index]
    intro b hb rfl
    have := fresh_of_mem A B b hb
    contradiction

@[simps -isSimp]
private noncomputable def transfer (A : Finset 𝔸) (τ τ' : Ren 𝔸) : Ren 𝔸 where
  toFun a :=
    open Classical in
    if h : ∃b ∈ A, a = τ b then τ' h.choose else a
  exists_support' := by
    classical
    use A.image τ
    grind

private lemma transfer_of_range
    (A : Finset 𝔸) (τ τ' : Ren 𝔸) (a : 𝔸)
    (hτ : Set.InjOn τ A) (ha : a ∈ A)
    : transfer A τ τ' (τ a) = τ' a := by
  have : ∃ b ∈ A, τ a = τ b := by grind
  simp only [transfer_coe, this, ↓reduceDIte]
  congr 1
  have := this.choose_spec
  apply hτ <;> grind

private lemma transfer_of_notRange
    (A : Finset 𝔸) (τ τ' : Ren 𝔸) (a : 𝔸)
    (ha : ∀ b ∈ A, τ b ≠ a)
    : transfer A τ τ' a = a := by
  simp only [transfer_coe, dite_eq_right_iff, forall_exists_index, forall_and_index]
  grind

lemma ext_of_finset
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X]
    (f g : Hom 𝔸 X Y) (A : Finset 𝔸)
    (hA : ∀ x, supp 𝔸 x ∩ A = ∅ → f x = g x)
    : f = g := by
  classical
  rcases f with ⟨f, Cf, hCf⟩
  rcases g with ⟨g, Cg, hCg⟩
  simp only [DFunLike.coe, mk.injEq] at ⊢ hA
  ext x

  let τ := fresh (supp 𝔸 x ∩ A) (supp 𝔸 x ∪ A ∪ Cf ∪ Cg)
  let τ' := unfresh (supp 𝔸 x ∩ A) (supp 𝔸 x ∪ A ∪ Cf ∪ Cg)

  have : x = rename τ' (rename τ x) := by
    simp only [rename_mul]
    nth_rw 1 [←rename_one (𝔸 := 𝔸) x]
    apply rename_congr
    intro a ha
    simp (disch := grind) only [Ren.one_coe, Finset.union_assoc, Ren.mul_coe, unfresh_fresh₂, τ', τ]

  have : f (rename τ x) = g (rename τ x) := by
    apply hA
    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha₁ ha₂
    have := supp_rename_subset τ x ha₁
    simp only [Finset.mem_rename, rename_def, τ] at this
    rcases this with ⟨b, hb, rfl⟩
    by_cases hb' : b ∈ A
    · have := fresh_of_mem (supp 𝔸 x ∩ A) (supp 𝔸 x ∪ A ∪ Cf ∪ Cg) b (by grind)
      grind
    · rw [fresh_of_notMem] at ha₁ ha₂ <;> grind

  have : f (rename τ' (rename τ x)) = rename τ' (f (rename τ x)) := by
    rw [←hCf]
    simp +contextual (disch := grind) [Finset.union_assoc, unfresh_of_mem, implies_true, τ']

  have : g (rename τ' (rename τ x)) = rename τ' (g (rename τ x)) := by
    rw [←hCg]
    simp +contextual (disch := grind) [Finset.union_assoc, unfresh_of_mem, implies_true, τ']

  grind

private structure Partial
    [DecidableEq 𝔸] (A : Finset 𝔸)
    (X : Type*) [RenameAction 𝔸 X] [RenamingSet 𝔸 X]
    (Y : Type*) [RenameAction 𝔸 Y] [RenamingSet 𝔸 Y] where
  toFun : {x : X // supp 𝔸 x ∩ A = ∅} → Y
  property :
    ∀ ⦃σ⦄, (∀ a ∈ A, σ a = a) →
    ∀ ⦃x⦄ hx₁ hx₂, rename σ (toFun ⟨x, hx₁⟩) = toFun ⟨rename σ x, hx₂⟩

private lemma Partial.supp_subset
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    {A : Finset 𝔸} (f : Partial A X Y) (x : {x : X // supp 𝔸 x ∩ A = ∅ })
    : supp 𝔸 (f.toFun x) ⊆ A ∪ supp 𝔸 x.val := by
  intro a ha
  wlog ha' : a ∉ supp 𝔸 x.val
  · simp only [Decidable.not_not] at ha'
    simp only [Finset.mem_union, ha', or_true]
  wlog ha'' : a ∉ A
  · simp only [Decidable.not_not] at ha''
    simp only [Finset.mem_union, ha'', true_or]

  obtain ⟨b, hb⟩ := (A ∪ {a}).exists_notMem

  have hx₁ := x.property
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and] at hx₁

  have hx₂ : rename (.restrict {a} fun _ ↦ b) x.val = x.val := by
    apply rename_congr'
    simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
    grind

  have := f.property
      (σ := .restrict {a} fun _ ↦ b)
      (by simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
          grind)
      x.property
      (by grind)
  simp only [Subtype.coe_eta, hx₂] at this
  rw [←this] at ha
  obtain ⟨c, hc, hc'⟩ := supp_rename_subset' _ _ _ ha
  simp only [Ren.restrict_coe, Finset.mem_singleton] at hc'
  grind

private lemma Partial.extend_fun_eq
    [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [Infinite 𝔸] [DecidableEq 𝔸]
    {A : Finset 𝔸} (f : Partial A X Y)
    (x : X) (τ τ_inv τ' τ'_inv : Ren 𝔸)
    (hτ₁ : ∀ a ∈ supp 𝔸 x, τ a ∉ A)
    (hτ₂ : ∀ a ∈ supp 𝔸 x, τ_inv (τ a) = a)
    (hτ₃ : ∀ a ∈ A, τ_inv a = a)
    (hτ'₁ : ∀ a ∈ supp 𝔸 x, τ' a ∉ A)
    (hτ'₂ : ∀ a ∈ supp 𝔸 x, τ'_inv (τ' a) = a)
    (hτ'₃ : ∀ a ∈ A, τ'_inv a = a)
    : rename τ_inv (f.toFun ⟨rename τ x, by grind⟩)
    = rename τ'_inv (f.toFun ⟨rename τ' x, by grind⟩) := by
  classical

  have τ_injOn : Set.InjOn τ (supp 𝔸 x) := by
    intro _
    grind
  have τ'_injOn : Set.InjOn τ' (supp 𝔸 x) := by
    intro _
    grind

  have lemma₁ : rename τ' x = rename (transfer (supp 𝔸 x) τ τ') (rename τ x) := by
    simp only [rename_mul]
    apply rename_congr
    intro a ha
    simp (disch := grind) only [Ren.mul_coe, transfer_of_range]

  have lemma₂
      : f.toFun ⟨rename τ' x, by grind⟩
      = rename (transfer (supp 𝔸 x) τ τ') (f.toFun ⟨rename τ x, by grind⟩) := by
    simp only [lemma₁]
    rw [f.property]
    intro a ha
    simp (disch := grind) only [transfer_of_notRange]

  rw [lemma₂]
  simp only [rename_mul]
  apply rename_congr
  intro a ha
  simp (disch := grind) only [Ren.mul_coe]
  by_cases h : ∃ b ∈ supp 𝔸 x, a = τ b
  · rcases h with ⟨a, ha', rfl⟩
    simp (disch := grind) only [transfer_of_range]
    grind
  · simp only [not_exists, not_and] at h
    simp (disch := grind) only [transfer_of_notRange]
    have := f.supp_subset _ ha
    grind

@[simps -isSimp]
private noncomputable def Partial.extend
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    {A : Finset 𝔸} (f : Partial A X Y)
    : Hom 𝔸 X Y where
  toFun x :=
    rename (unfresh (supp 𝔸 x) A)
      <| f.toFun
      <| Subtype.mk (rename (fresh (supp 𝔸 x) A) x)
      <| by grind
  exists_support' := by
    use A
    intro σ hσ x
    let τ := fresh (supp 𝔸 x) A
    let τₜ := unfresh (supp 𝔸 x) A
    let τ' := fresh (supp 𝔸 (rename σ x)) A
    let τ'ₜ := unfresh (supp 𝔸 (rename σ x)) A
    let τ'' := fresh (rename σ (supp 𝔸 x)) A
    let τ''ₜ := unfresh (rename σ (supp 𝔸 x)) A
    change rename σ (rename τₜ (f.toFun ⟨rename τ x, _⟩))
         = rename τ'ₜ (f.toFun ⟨rename τ' (rename σ x), _⟩)

    rw [f.extend_fun_eq _ τ' τ'ₜ τ'' τ''ₜ
      (by grind)
      (by grind)
      (by grind)
      (by grind)
      (by grind)
      (by grind)]

    let σ' : Ren 𝔸 := {
      toFun a :=
        if h : ∃b ∈ supp 𝔸 x, a = τ b
        then τ'' (σ h.choose)
        else a
      exists_support' := by
        use (supp 𝔸 x).image τ
        grind
    }
    have σ'_coe {a} : σ' a =
      if h : ∃b ∈ supp 𝔸 x, a = τ b
      then τ'' (σ h.choose)
      else a := by rfl
    have : rename τ'' (rename σ x) = rename σ' (rename τ x) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha
      have : ∃ b ∈ supp 𝔸 x, τ a = τ b := by grind
      simp only [Ren.mul_coe, σ'_coe, this, ↓reduceDIte]
      congr 2
      apply fresh_inj (supp 𝔸 x) A
      · assumption
      · exact this.choose_spec.1
      · exact this.choose_spec.2
    simp only [this]
    nth_rw 2 [←f.property (by grind) (by grind) (by grind)]
    simp only [rename_mul]
    apply rename_congr
    intro a ha
    replace ha := f.supp_subset ⟨rename τ x, by grind⟩ ha
    simp only [Finset.mem_union] at ha
    cases ha with
    | inl ha =>
      simp only [Ren.mul_coe]
      grind
    | inr ha =>
      replace ha := supp_rename_subset' _ _ _ ha
      rcases ha with ⟨a, ha, rfl⟩
      simp only [Ren.mul_coe]
      have ha' : ∃ b ∈ supp 𝔸 x, τ a = τ b := by grind
      simp only [σ'_coe, ha', ↓reduceDIte]
      have := ha'.choose_spec
      have hσ : σ ha'.choose ∈ rename σ (supp 𝔸 x) := by
        simp only [Finset.mem_rename, rename_def]
        grind
      simp (disch := grind) only [unfresh_fresh₁, τₜ, τ, τ''ₜ, τ'']
      congr 1
      apply fresh_inj (supp 𝔸 x) A <;> grind

@[simp]
private noncomputable def Partial.extend_eq
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    {A : Finset 𝔸} (f : Partial A X Y) (x : X) (hx : supp 𝔸 x ∩ A = ∅)
    : f.extend x = f.toFun ⟨x, hx⟩ := by
  simp only [extend_toFun]
  rw [f.property]
  · simp only [rename_mul]
    congr 2
    apply rename_congr'
    intro a ha
    simp (disch := grind) only [Ren.mul_coe, unfresh_fresh₁]
  · grind
  · ext a
    simp only [rename_mul, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha₁ ha₂
    replace ha₁ := supp_rename_subset' _ _ _ ha₁
    rcases ha₁ with ⟨a, ha₁, rfl⟩
    simp (disch := grind) only [Ren.mul_coe, unfresh_fresh₁] at ha₂
    simp only [Finset.ext_iff, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and] at hx
    grind

private lemma mem_supp'
    [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [Infinite 𝔸]
    {f : Hom 𝔸 X Y} {a x} (ha : a ∈ supp 𝔸 (f x))
    : a ∈ f.exists_support.choose ∨ a ∈ supp 𝔸 x := by
  classical
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

@[simps]
private def Partial.rename₀
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    (σ : Ren 𝔸) (f : Hom 𝔸 X Y)
    : Partial (f.exists_support.choose ∪ σ.supp ∪ f.exists_support.choose.image σ) X Y where
  toFun x := rename σ (f x)
  property σ' hσ' x hx₁ hx₂ := by
    dsimp only

    generalize hA : f.exists_support.choose ∪ σ.supp ∪ f.exists_support.choose.image σ = A
    simp only [hA] at hx₁ hx₂ hσ'

    let μ : Ren 𝔸 := {
      toFun a :=
        if ha : a ∈ supp 𝔸 x then
          have : ∃b ∈ supp 𝔸 x, σ' a = σ' b := by use a
          this.choose
        else
          a
      exists_support' := by
        use supp 𝔸 x
        simp +contextual only [↓reduceDIte, implies_true]
    }
    have μ_coe {a}
        : μ a
        = if ha : a ∈ supp 𝔸 x then
            have : ∃b ∈ supp 𝔸 x, σ' a = σ' b := by use a
            this.choose
          else
            a := by
      rfl
    have hμ₁ : ∀a ∈ supp 𝔸 x, μ a ∈ supp 𝔸 x := by
      intro a ha
      simp only [μ_coe, ha, ↓reduceDIte]
      have : ∃ b ∈ supp 𝔸 x, σ' a = σ' b := by use a
      exact this.choose_spec.1
    have hμ₂ : ∀a ∈ A, μ a = a := by
      simp only [μ_coe, dite_eq_right_iff]
      intro a ha₁ ha₂
      simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
      grind
    have hμ₃ {a} : σ' (μ a) = σ' a := by
      by_cases ha : a ∈ supp 𝔸 x
      · simp only [μ_coe, ha, ↓reduceDIte]
        have : ∃ b ∈ supp 𝔸 x, σ' a = σ' b := by use a
        exact this.choose_spec.2.symm
      · simp only [μ_coe, ha, ↓reduceDIte]

    have hx₃ : rename σ' x = rename σ' (rename μ x) := by
      simp only [rename_mul]
      congr 1
      ext a
      simp only [Ren.mul_coe, hμ₃]
    rw [hx₃] at ⊢ hx₂

    have hx₄ : supp 𝔸 (rename σ' (rename μ x)) = rename σ' (supp 𝔸 (rename μ x)) := by
      rw [supp_rename]
      intro a ha b hb hab
      replace ha := supp_rename_subset' _ _ _ ha
      rcases ha with ⟨a, ha, rfl⟩
      replace hb := supp_rename_subset' _ _ _ hb
      rcases hb with ⟨b, hb, rfl⟩
      simp only [hμ₃] at hab
      simp only [μ_coe, ha, ↓reduceDIte, hab, hb]
    rw [hx₄] at hx₂

    have hx₅ : rename σ (rename σ' (f (rename μ x))) = rename σ' (rename σ (f (rename μ x))) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha₁
      simp only [Ren.mul_coe]
      replace ha₁ := mem_supp' ha₁
      cases ha₁ with
      | inl ha₁ => grind
      | inr ha₁ =>
        have ha₂ := supp_rename_subset' _ _ _ ha₁
        rcases ha₂ with ⟨a, ha₂, rfl⟩
        have : μ a ∈ supp 𝔸 x := by grind
        have ha₂ : μ a ∉ σ.supp := by
          simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
          grind
        simp only [Ren.mem_supp, ne_eq, Decidable.not_not] at ha₂
        simp only [ha₂]
        have : σ' (μ a) ∈ rename σ' (supp 𝔸 (rename μ x)) := by
          simp only [Finset.mem_rename, rename_def]
          use μ a
        have : σ' (μ a) ∉ σ.supp := by
          simp only [Finset.ext_iff, Finset.mem_inter] at hx₂
          grind
        simpa only [Ren.mem_supp, ne_eq, Decidable.not_not] using this

    have hx₆ : f (rename μ x) = rename μ (f x) := by
      rw [← f.exists_support.choose_spec]
      grind

    have hx₇ : rename σ (rename μ (f x)) = rename μ (rename σ (f x)) := by
      simp only [rename_mul]
      apply rename_congr
      intro a ha₁
      simp only [Ren.mul_coe]
      replace ha₁ := mem_supp' ha₁
      cases ha₁ with
      | inl ha₁ => grind
      | inr ha₁ =>
        have : a ∉ σ.supp := by
          simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
          grind
        simp only [Ren.mem_supp, ne_eq, Decidable.not_not] at this
        have : μ a ∉ σ.supp := by
          simp only [Finset.ext_iff, Finset.mem_inter] at hx₁
          grind
        simp only [Ren.mem_supp, ne_eq, Decidable.not_not] at this
        grind

    rw [← f.exists_support.choose_spec (by grind), hx₅, hx₆, hx₇]

    simp only [rename_mul]
    apply rename_congr
    simp only [Ren.mul_coe, hμ₃, implies_true]

@[simps -isSimp]
noncomputable instance
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    : RenameAction 𝔸 (Hom 𝔸 X Y) where
  rename σ f := (Partial.rename₀ σ f).extend
  rename_one f := by
    apply ext_of_finset _ _ f.exists_support.choose
    intro x hx
    rw [Partial.extend_eq]
    · simp only [Partial.rename₀_toFun, rename_one', id_eq]
    · ext a
      simp only [Finset.union_assoc, Finset.mem_inter, Finset.mem_union, Ren.mem_supp, Ren.one_coe,
        ne_eq, not_true_eq_false, Finset.mem_image, exists_eq_right, Finset.notMem_empty, iff_false,
        not_and]
      simp only [Finset.ext_iff, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and] at hx
      grind
  rename_mul σ₁ σ₂ f := by
    apply ext_of_finset _ _ <|
      (Partial.rename₀ σ₂ f).extend.exists_support.choose ∪
      (Partial.rename₀ σ₂ f).extend.exists_support.choose.image σ₁ ∪
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
    rw [Partial.extend_eq, Partial.extend_eq, Partial.rename₀_toFun, Partial.extend_eq]
    · simp only [Partial.rename₀_toFun, rename_mul]
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

instance
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    : RenamingSet 𝔸 (Hom 𝔸 X Y) where
  exists_support f := by
    classical
    use f.exists_support.choose
    simp only [isSupportOf_def, rename_def]
    intro σ₁ σ₂ hσ
    apply ext_of_finset _ _ <|
      f.exists_support.choose
        ∪ σ₁.supp
        ∪ σ₂.supp
        ∪ f.exists_support.choose.image σ₁
        ∪ f.exists_support.choose.image σ₂
    intro x hx
    rw [Partial.extend_eq, Partial.extend_eq]
    · dsimp only [Partial.rename₀_toFun]
      apply rename_congr
      intro a ha
      cases mem_supp' ha with
      | inl h => exact hσ _ h
      | inr h =>
        have : σ₁ a = a ∧ σ₂ a = a := by
          simp [Finset.ext_iff] at hx
          grind
        grind
    · grind
    · grind

lemma rename_apply
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]
    (σ : Ren 𝔸) (f : Hom 𝔸 X Y) (x : X)
    : rename σ (f x) = (rename σ f) (rename σ x) := by
  classical
  generalize hA
    : f.exists_support.choose
        ∪ (rename σ f).exists_support.choose
        ∪ σ.supp
        ∪ supp 𝔸 x
        ∪ (supp 𝔸 x).image σ
        ∪ f.exists_support.choose.image σ
    = A
  let τ := fresh A A
  have : ∀a ∈ A, σ (τ a) = τ a := by
    intro a ha
    have : τ a ∉ σ.supp := by grind
    simpa only [Ren.mem_supp, ne_eq, Decidable.not_not] using this
  let τₜ := unfresh A A
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
    have h₁ : (fresh A A) a ∉ A := by grind
    have h₂ : ∃ b ∈ A, (fresh A A) a = (fresh A A) b := by grind
    have h₃ : unfresh A A (fresh A A a) = a := by grind
    have h₄ : σ a ∈ A := by grind
    simp only [unfresh_fresh₁, Ren.mul_coe, π_coe, h₁, ↓reduceIte, h₂, h₃, τₜ, σ', τ, h₄]
  have : ∀a ∈ supp 𝔸 (f (rename τ x)), (τₜ * σ' * σ) a = (σ * τₜ) a := by
    intro a ha
    simp only [Ren.mul_coe, π_coe, σ']
    replace ha := mem_supp' ha
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
    rw [unfresh_fresh₁]
    · rw [unfresh_of_mem]
      grind
    · grind
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
    rw [Partial.extend_eq]
    · simp only [Partial.rename₀_toFun]
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

end Hom

end RenamingSets
