import RenamingSets.Support.Basic

namespace RenamingSets.Prod

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

@[simps -isSimp]
instance : RenameAction 𝔸 (X × Y) where
  rename σ x := (rename σ x.1, rename σ x.2)
  rename_one := by simp only [rename_one, Prod.mk.eta, implies_true]
  rename_mul := by simp only [rename_mul, implies_true]

@[simp, grind =]
lemma rename_mk
    (σ : Ren 𝔸) (x : X) (y : Y)
    : rename σ (x, y) = (rename σ x, rename σ y) := by
  simp only [rename_def]

@[simp, grind =]
lemma isSupportOf_mk
    (A : Finset 𝔸) (x : X) (y : Y)
    : IsSupportOf A (x, y) ↔ IsSupportOf A x ∧ IsSupportOf A y := by
  apply Iff.intro
  · simp only [isSupportOf_def, rename_mk, Prod.mk.injEq]
    intro h
    apply And.intro
    · intro f g h'
      apply (h h').1
    · intro f g h'
      apply (h h').2
  · simp only [isSupportOf_def, rename_mk, Prod.mk.injEq, and_imp]
    grind

@[simp, grind =]
lemma isSupported_mk
    (x : X) (y : Y)
    : IsSupported 𝔸 (x, y) ↔ IsSupported 𝔸 x ∧ IsSupported 𝔸 y := by
  classical
  apply Iff.intro
  · grind [isSupported_def]
  · simp only [isSupported_def, isSupportOf_mk, and_imp, forall_exists_index]
    intro A hA B hB
    use A ∪ B
    grind

@[simp, grind ←]
lemma isSupportOfF_fst
    (A : Finset 𝔸)
    : IsSupportOfF A (Prod.fst : X × Y → X) := by
  simp only [isSupportOfF_def, Prod.forall, rename_mk, implies_true]

@[simp, local fun_prop]
lemma equivariant_fst : Equivariant 𝔸 (Prod.fst : X × Y → X) := by
  simp only [equivariant_def, isSupportOfF_fst]

@[simp, local fun_prop]
lemma isSupportedF_fst : IsSupportedF 𝔸 (Prod.fst : X × Y → X) := by
  fun_prop

@[simp, fun_prop]
lemma equivariant_fst'
    {f : X → Y × Z} (hf : Equivariant 𝔸 f)
    : Equivariant 𝔸 (fun x ↦ (f x).1) := by
  fun_prop

@[simp, fun_prop]
lemma isSupportedF_fst'
    {f : X → Y × Z} (hf : IsSupportedF 𝔸 f)
    : IsSupportedF 𝔸 (fun x ↦ (f x).1) := by
  fun_prop

@[simp, grind ←]
lemma isSupportOfF_snd
    (A : Finset 𝔸)
    : IsSupportOfF A (Prod.snd : X × Y → Y) := by
  simp only [isSupportOfF_def, Prod.forall, rename_mk, implies_true]

@[simp, local fun_prop]
lemma equivariant_snd : Equivariant 𝔸 (Prod.snd : X × Y → Y) := by
  simp only [equivariant_def, isSupportOfF_snd]

@[simp, local fun_prop]
lemma isSupportedF_snd : IsSupportedF 𝔸 (Prod.snd : X × Y → Y) := by
  fun_prop

@[simp, fun_prop]
lemma equivariant_snd'
    {f : X → Y × Z} (hf : Equivariant 𝔸 f)
    : Equivariant 𝔸 (fun x ↦ (f x).2) := by
  fun_prop

@[simp, fun_prop]
lemma isSupportedF_snd'
    {f : X → Y × Z} (hf : IsSupportedF 𝔸 f)
    : IsSupportedF 𝔸 (fun x ↦ (f x).2) := by
  fun_prop

@[simp, grind →]
lemma isSupportOfF_mk
    (A : Finset 𝔸)
    {f : X → Y} (hf : IsSupportOfF A f)
    {g : X → Z} (hg : IsSupportOfF A g)
    : IsSupportOfF A (fun x ↦ (f x, g x)) := by
  simp only [isSupportOfF_def, rename_mk, Prod.mk.injEq] at ⊢ hf hg
  grind

@[simp, fun_prop]
lemma equivariant_mk
    {f : X → Y} (hf : Equivariant 𝔸 f)
    {g : X → Z} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (fun x ↦ (f x, g x)) := by
  grind [equivariant_def]

@[simp, fun_prop]
lemma isSupportedF_mk
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    {g : X → Z} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ (f x, g x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  apply isSupportOfF_mk <;> grind

variable [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]

instance : RenamingSet 𝔸 (X × Y) where
  isSupported x := by
    classical
    rcases x with ⟨x, y⟩
    grind

@[simp, grind =]
lemma supp_mk [DecidableEq 𝔸] (x : X) (y : Y) : supp 𝔸 (x, y) = supp 𝔸 x ∪ supp 𝔸 y := by
  ext a
  simp only [mem_supp, isSupportOf_mk, and_imp, Finset.mem_union]
  apply Iff.intro
  · intro h
    by_cases h' : ∀ (A : Finset 𝔸), IsSupportOf A x → a ∈ A
    · grind
    · simp only [not_forall] at h'
      rcases h' with ⟨A, hA₁, hA₂⟩
      right
      intro B hB
      specialize h (A ∪ B) (isSupportOf_union_left hA₁) (isSupportOf_union_right hB)
      grind
  · grind

end RenamingSets.Prod
