import RenamingSets.Prod

namespace RenamingSets

variable {𝔸 X Y : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y]

namespace Finset

@[simps -isSimp]
instance [DecidableEq X] : RenameAction 𝔸 (Finset X) where
  rename σ := Finset.image (rename σ)
  rename_one := by simp only [rename_one', Finset.image_id, implies_true]
  rename_mul f g xs := by
    simp +unfoldPartialApp only [Finset.image_image, Function.comp]
    congr 1
    ext x
    apply rename_mul

@[simp, grind =]
lemma mem_rename
    [DecidableEq X]
    (x : X) (σ : Ren 𝔸) (xs : Finset X)
    : x ∈ rename σ xs ↔ ∃x' ∈ xs, rename σ x' = x := by
  simp only [rename_def, Finset.mem_image]

@[simp, grind ←]
lemma isSupportOf_empty [DecidableEq X] (A : Finset 𝔸) : IsSupportOf A (∅ : Finset X) := by
  simp only [
    isSupportOf_def, Finset.ext_iff, mem_rename, Finset.notMem_empty,
    false_and, exists_false, implies_true]

@[simp, grind ←]
lemma isSupported_empty [DecidableEq X] : IsSupported 𝔸 (∅ : Finset X) := by
  simp only [isSupported_def, isSupportOf_empty, exists_const]

@[grind ←]
lemma isSupportOf_insert [DecidableEq X]
    {A : Finset 𝔸} {x : X} {xs : Finset X}
    (hx : IsSupportOf A x) (hxs : IsSupportOf A xs)
    : IsSupportOf A (insert x xs) := by
  simp only [isSupportOf_def] at ⊢ hx hxs
  intro f g hfg
  ext a
  specialize hx hfg
  specialize hxs hfg
  simp only [Finset.ext_iff, mem_rename] at hxs
  simp only [mem_rename, Finset.mem_insert, exists_eq_or_imp, hx, hxs]

lemma isSupported_insert [DecidableEq X]
    {x : X} {xs : Finset X}
    (hx : IsSupported 𝔸 x) (hxs : IsSupported 𝔸 xs)
    : IsSupported 𝔸 (insert x xs) := by
  classical
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hxs
  use A ∪ B
  apply isSupportOf_insert <;> grind

lemma rename_mono
    [DecidableEq X] (σ : Ren 𝔸)
    : Monotone (rename σ : Finset X → Finset X) := by
  intro xs ys h
  apply Finset.image_mono
  exact h

variable [RenamingSet 𝔸 X]

instance [DecidableEq X] : RenamingSet 𝔸 (Finset X) where
  isSupported xs := by
    classical
    induction xs using Finset.induction with
    | empty => simp only [isSupported_empty]
    | insert a s _ ih => apply isSupported_insert <;> grind

@[simp, grind =]
lemma supp_empty [DecidableEq X] : supp 𝔸 (∅ : Finset X) = ∅ := by
  ext a
  simp only [mem_supp, isSupportOf_empty, forall_const, Finset.notMem_empty, iff_false, not_forall]
  use ∅
  simp only [Finset.notMem_empty, not_false_eq_true]

end Finset

variable [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]

lemma supp_rename_subset
    [Infinite 𝔸] [DecidableEq 𝔸] (σ : Ren 𝔸) (x : X)
    : supp 𝔸 (rename σ x) ⊆ rename σ (supp 𝔸 x) := by
  apply supp_min
  constructor
  intro f g hfg
  simp only [
    Finset.mem_rename, RenameAction.rename_def, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at hfg
  simp only [rename_mul]
  apply rename_congr
  simp only [Ren.mul_coe]
  exact hfg

lemma supp_rename_subset'
    [Infinite 𝔸] [DecidableEq 𝔸] (σ : Ren 𝔸) (x : X)
    : ∀ a ∈ supp 𝔸 (rename σ x), ∃ b ∈ supp 𝔸 x, σ b = a := by
  intro a ha
  have := supp_rename_subset _ _ ha
  simp only [Finset.mem_rename, RenameAction.rename_def] at this
  exact this

@[simp, grind =]
lemma supp_rename
    [Infinite 𝔸] [DecidableEq 𝔸]
    (σ : Ren 𝔸) (x : X) (hσ : (supp 𝔸 x).toSet.InjOn σ)
    : supp 𝔸 (rename σ x) = rename σ (supp 𝔸 x) := by
  apply le_antisymm
  · simp only [Finset.le_eq_subset, supp_rename_subset]
  · intro a ha
    simp only [Finset.mem_rename, RenameAction.rename_def] at ha
    rcases ha with ⟨b, hb, rfl⟩

    let σ' : Ren 𝔸 := {
      toFun a := if h : ∃b ∈ supp 𝔸 x, a = σ b then h.choose else a
      exists_support' := by
        use (supp 𝔸 x).image σ
        intro a ha
        simp only [Finset.mem_image, not_exists, not_and] at ha
        have : ¬∃ b ∈ supp 𝔸 x, a = σ b := by grind
        simp only [this, ↓reduceDIte]
    }
    have σ'_coe {a} : σ' a = if h : ∃b ∈ supp 𝔸 x, a = σ b then h.choose else a := by rfl
    have : rename σ' (rename σ x) = x := by
      simp only [rename_mul]
      nth_rw 2 [←rename_one (𝔸 := 𝔸) x]
      apply rename_congr
      simp only [Ren.mul_coe, Ren.one_coe]
      intro a ha
      have : ∃ b ∈ supp 𝔸 x, σ a = σ b := by use a
      simp only [σ'_coe, this, ↓reduceDIte]
      apply hσ
      · exact this.choose_spec.1
      · exact ha
      · exact this.choose_spec.2.symm
    rw [←this] at hb

    have := supp_rename_subset _ _ hb
    simp only [Finset.mem_rename, RenameAction.rename_def] at this
    rcases this with ⟨c, hc, rfl⟩

    have := supp_rename_subset _ _ hc
    simp only [Finset.mem_rename, RenameAction.rename_def] at this
    rcases this with ⟨d, hd, rfl⟩

    have : ∃ b ∈ supp 𝔸 x, σ d = σ b := by grind
    simp only [σ'_coe, this, ↓reduceDIte, ←this.choose_spec.2, hc]

lemma isSupportOf_def'
    [Infinite 𝔸] (A : Finset 𝔸) (x : X)
    : IsSupportOf A x
    ↔ (∀⦃f⦄, (∀a ∈ A, f a = a) → rename f x = x) := by
  apply Iff.intro
  · simp only [isSupportOf_def]
    intro h f hf
    nth_rw 2 [←rename_one (𝔸 := 𝔸) x]
    apply h
    simp_all only [Ren.one_coe, implies_true]
  · classical
    intro h
    suffices supp 𝔸 x ⊆ A by
      apply isSupportOf_mono
      · apply this
      · simp only [isSupportOf_supp]
    intro a ha
    obtain ⟨b, hb⟩ := (supp 𝔸 x).exists_notMem
    have : a ∉ supp 𝔸 (rename (.restrict {a} fun _ ↦ b) x) := by
      intro ha
      replace ha := supp_rename_subset _ _ ha
      simp only [
        Finset.mem_rename, RenameAction.rename_def,
        Ren.restrict_coe, Finset.mem_singleton] at ha
      grind

    specialize @h (.restrict {a} fun _ ↦ b)
    simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff] at h
    grind

lemma supp_apply
    [Infinite 𝔸] [DecidableEq 𝔸]
    {A : Finset 𝔸} {f : X → Y} (hf : IsSupportOfF A f) (x)
    : supp 𝔸 (f x) ⊆ A ∪ supp 𝔸 x := by
  classical
  rcases hf with ⟨hf⟩
  intro a ha
  by_contra! ha'
  obtain ⟨b, hb⟩ := (A ∪ {a}).exists_notMem
  have hx : rename (Ren.restrict {a} fun _ ↦ b) x = x := by
    apply rename_congr'
    simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
    grind
  have := hf
    (σ := .restrict {a} fun _ ↦ b)
    (by simp only [Ren.restrict_coe, Finset.mem_singleton, ite_eq_right_iff]
        grind)
    (x := x)
  rw [hx] at this
  rw [←this] at ha
  replace ha := supp_rename_subset' _ _ _ ha
  simp only [Ren.restrict_coe, Finset.mem_singleton] at ha
  grind

end RenamingSets
