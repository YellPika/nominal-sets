import RenamingSets.Prod

namespace RenamingSets.Sum

variable {𝔸 : Type*}
  {X : Type*} [RenameAction 𝔸 X]
  {Y : Type*} [RenameAction 𝔸 Y]
  {Z : Type*} [RenameAction 𝔸 Z]
  {W : Type*} [RenameAction 𝔸 W]

@[simps -isSimp]
instance : RenameAction 𝔸 (X ⊕ Y) where
  rename σ := Sum.map (rename σ) (rename σ)
  rename_one := by simp only [rename_one', Sum.map_id_id, id_eq, implies_true]
  rename_mul := by simp only [
    Sum.map_map, Sum.forall, Sum.map_inl, Function.comp_apply,
    rename_mul, implies_true, Sum.map_inr, and_self]

@[simp, grind =]
lemma rename_inl
    (σ : Ren 𝔸) (x : X)
    : rename σ (.inl x : X ⊕ Y) = .inl (rename σ x) := by
  simp only [rename_def, Sum.map_inl]

@[simp, grind =]
lemma isSupportOf_inl
    (A : Finset 𝔸) (x : X)
    : IsSupportOf A (.inl x : X ⊕ Y) ↔ IsSupportOf A x := by
  simp only [isSupportOf_def, rename_inl, Sum.inl.injEq]

@[simp, grind =]
lemma isSupported_inl (x : X) : IsSupported 𝔸 (.inl x : X ⊕ Y) ↔ IsSupported 𝔸 x := by
  simp only [isSupported_def, isSupportOf_inl]

@[simp, grind ←]
lemma isSupportOfF_inl
    (A : Finset 𝔸)
    : IsSupportOfF A (Sum.inl : X → X ⊕ Y) := by
  simp only [isSupportOfF_def, rename_inl, implies_true]

@[simp, fun_prop]
lemma isSupportedF_inl : IsSupportedF 𝔸 (Sum.inl : X → X ⊕ Y) := by
  use ∅
  simp only [isSupportOfF_inl]

@[simp, fun_prop]
lemma isSupportedF_inl'
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    : IsSupportedF 𝔸 (fun x ↦ (.inl (f x) : Y ⊕ Z)) := by
  fun_prop

@[simp, grind =]
lemma rename_inr
    (σ : Ren 𝔸) (x : Y)
    : rename σ (.inr x : X ⊕ Y) = .inr (rename σ x) := by
  simp only [rename_def, Sum.map_inr]

@[simp, grind =]
lemma isSupportOf_inr
    (A : Finset 𝔸) (x : Y)
    : IsSupportOf A (.inr x : X ⊕ Y) ↔ IsSupportOf A x := by
  simp only [isSupportOf_def, rename_inr, Sum.inr.injEq]

@[simp, grind =]
lemma isSupported_inr (x : Y) : IsSupported 𝔸 (.inr x : X ⊕ Y) ↔ IsSupported 𝔸 x := by
  simp only [isSupported_def, isSupportOf_inr]

@[simp, grind ←]
lemma isSupportOfF_inr
    (A : Finset 𝔸)
    : IsSupportOfF A (Sum.inr : Y → X ⊕ Y) := by
  simp only [isSupportOfF_def, rename_inr, implies_true]

@[simp, fun_prop]
lemma isSupportedF_inr : IsSupportedF 𝔸 (Sum.inr : Y → X ⊕ Y) := by
  use ∅
  simp only [isSupportOfF_inr]

@[simp, fun_prop]
lemma isSupportedF_inr'
    {f : X → Z} (hf : IsSupportedF 𝔸 f)
    : IsSupportedF 𝔸 (fun x ↦ (.inr (f x) : Y ⊕ Z)) := by
  fun_prop

@[simp]
lemma isSupportOfF_elim
    (A : Finset 𝔸)
    {f : X → Y → W} (hf : IsSupportOfF A fun (x, y) ↦ f x y)
    {g : X → Z → W} (hg : IsSupportOfF A fun (x, y) ↦ g x y)
    {h : X → Y ⊕ Z} (hh : IsSupportOfF A h)
    : IsSupportOfF A (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  simp only [isSupportOfF_def, Prod.forall, Prod.rename_mk] at ⊢ hf hg hh
  intro σ hσ x
  cases hx : h x <;> grind

@[simp, fun_prop]
lemma isSupportedF_mk
    {f : X → Y → W} (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    {g : X → Z → W} (hg : IsSupportedF 𝔸 fun (x, y) ↦ g x y)
    {h : X → Y ⊕ Z} (hh : IsSupportedF 𝔸 h)
    : IsSupportedF 𝔸 (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨C, hC⟩ := hh
  use A ∪ B ∪ C
  apply isSupportOfF_elim <;> grind

variable [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y]

instance : RenamingSet 𝔸 (X ⊕ Y) where
  isSupported x := by
    cases x <;>
    · simp only [isSupported_inl, isSupported_inr, isSupported]

@[simp, grind =]
lemma supp_inl [DecidableEq 𝔸] (x : X) : supp 𝔸 (.inl x : X ⊕ Y) = supp 𝔸 x := by
  ext a
  simp only [mem_supp, isSupportOf_inl]

@[simp, grind =]
lemma supp_inr [DecidableEq 𝔸] (x : Y) : supp 𝔸 (.inr x : X ⊕ Y) = supp 𝔸 x := by
  ext a
  simp only [mem_supp, isSupportOf_inr]

end RenamingSets.Sum
