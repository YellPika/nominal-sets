import RenamingSets.Support.Defs
import RenamingSets.RenameAction.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

/-! ## `IsSupportOf` -/

lemma isSupportOf_def
    (A : Finset 𝔸) (x : X)
    : IsSupportOf A x
    ↔ ∀⦃f g⦄, (∀a ∈ A, f a = g a) → rename f x = rename g x := by
  apply Iff.intro
  · apply IsSupportOf.eq
  · apply IsSupportOf.mk

@[grind ←]
lemma isSupportOf_inter
    [DecidableEq 𝔸]
    {A B : Finset 𝔸} {x : X}
    (hA : IsSupportOf A x) (hB : IsSupportOf B x)
    : IsSupportOf (A ∩ B) x := by
  simp_all only [isSupportOf_def, Finset.mem_inter, and_imp]
  intro f g h
  let k : Ren 𝔸 := {
    toFun a := if a ∈ A then f a else g a
    exists_support' := by
      obtain ⟨C, hC⟩ := f.exists_support
      obtain ⟨D, hD⟩ := g.exists_support
      use C ∪ D
      grind
  }
  have k_coe {a} : k a = if a ∈ A then f a else g a := rfl
  specialize @hA f k
  specialize @hB k g
  grind

lemma isSupportOf_mono (x : X) : Monotone ((IsSupportOf · x) : Finset 𝔸 → Prop) := by
  intro A B hAB hA
  simp_all only [Finset.le_eq_subset, isSupportOf_def]
  grind

@[grind ←]
lemma isSupportOf_union_left
    [DecidableEq 𝔸]
    {A B : Finset 𝔸} {x : X}
    : IsSupportOf A x → IsSupportOf (A ∪ B) x := by
  apply isSupportOf_mono
  simp only [Finset.le_eq_subset, Finset.subset_union_left]

@[grind ←]
lemma isSupportOf_union_right
    [DecidableEq 𝔸]
    {A B : Finset 𝔸} {x : X}
    : IsSupportOf B x → IsSupportOf (A ∪ B) x := by
  apply isSupportOf_mono
  simp only [Finset.le_eq_subset, Finset.subset_union_right]

/-! ## `IsSupportOfF` -/

lemma isSupportOfF_def
    (A : Finset 𝔸) (f : X → Y)
    : IsSupportOfF A f
    ↔ ∀ ⦃σ⦄, (∀a ∈ A, σ a = a) → ∀x, rename σ (f x) = f (rename σ x) := by
  apply Iff.intro
  · apply IsSupportOfF.eq
  · apply IsSupportOfF.mk

@[simp]
lemma isSupportOfF_mono (f : X → Y) : Monotone (IsSupportOfF (𝔸 := 𝔸) · f) := by
  intro A B hAB
  simp only [Finset.le_eq_subset, isSupportOfF_def, le_Prop_eq] at ⊢ hAB
  grind

@[simp, grind ←]
lemma isSupportOfF_union_left
    [DecidableEq 𝔸] {A B : Finset 𝔸}
    (f : X → Y) (hf : IsSupportOfF A f)
    : IsSupportOfF (A ∪ B) f := by
  simp only [isSupportOfF_def, Finset.mem_union] at ⊢ hf
  grind

@[simp, grind ←]
lemma isSupportOfF_union_right
    [DecidableEq 𝔸] {A B : Finset 𝔸}
    (f : X → Y) (hf : IsSupportOfF B f)
    : IsSupportOfF (A ∪ B) f := by
  simp only [isSupportOfF_def, Finset.mem_union] at ⊢ hf
  grind

@[simp, grind ←]
lemma isSupportOfF_id (A : Finset 𝔸) : IsSupportOfF A (id : X → X) := by
  simp only [isSupportOfF_def, id_eq, implies_true]

@[simp, grind ←]
lemma isSupportOfF_id' (A : Finset 𝔸) : IsSupportOfF A (fun x : X ↦ x) := by
  simp only [isSupportOfF_def, implies_true]

@[simp, grind ←]
lemma isSupportOfF_comp
    (A : Finset 𝔸)
    {f : Y → Z} (hf : IsSupportOfF A f)
    {g : X → Y} (hg : IsSupportOfF A g)
    : IsSupportOfF A (f ∘ g) := by
  simp only [isSupportOfF_def] at ⊢ hf hg
  grind

@[simp, grind →]
lemma isSupportOfF_comp'
    (A : Finset 𝔸)
    {f : Y → Z} (hf : IsSupportOfF A f)
    {g : X → Y} (hg : IsSupportOfF A g)
    : IsSupportOfF A fun x ↦ f (g x) := by
  simp only [isSupportOfF_def] at ⊢ hf hg
  grind

/-! ## `IsSupportedF` -/

@[simp, fun_prop]
lemma isSupportedF_id : IsSupportedF 𝔸 (id : X → X) := by
  use ∅
  simp only [isSupportOfF_id]

@[simp, fun_prop]
lemma isSupportedF_id' : IsSupportedF 𝔸 (fun x : X ↦ x) := by
  use ∅
  simp only [isSupportOfF_id']

@[simp, fun_prop]
lemma isSupportedF_comp
    {f : Y → Z} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (f ∘ g) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  grind

@[simp, fun_prop]
lemma isSupportedF_comp'
    {f : Y → Z} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 fun x ↦ f (g x) := by
  fun_prop

/-- ## `Equivariant` -/

lemma equivariant_def (f : X → Y)
    : Equivariant 𝔸 f ↔ ∀ (σ : Ren 𝔸) x, rename σ (f x) = f (rename σ x) := by
  apply Iff.intro
  · apply Equivariant.eq
  · apply Equivariant.mk

@[simp, fun_prop]
lemma equivariant_id : Equivariant 𝔸 (id : X → X) := by
  simp only [equivariant_def, id_eq, implies_true]

@[simp, fun_prop]
lemma equivariant_id' : Equivariant 𝔸 (fun x : X ↦ x) := by
  simp only [equivariant_def, implies_true]

@[simp, fun_prop]
lemma equivariant_comp
    {f : Y → Z} (hf : Equivariant 𝔸 f)
    {g : X → Y} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (f ∘ g) := by
  simp_all only [equivariant_def, Function.comp_apply, implies_true]

@[simp, fun_prop]
lemma equivariant_comp'
    {f : Y → Z} (hf : Equivariant 𝔸 f)
    {g : X → Y} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (fun x ↦ f (g x)) := by
  simp_all only [equivariant_def, implies_true]

/-! ## `supp` -/

variable [RenamingSet 𝔸 X]

lemma mem_supp
    (a : 𝔸) (x : X)
    : a ∈ supp 𝔸 x ↔ (∀ A : Finset 𝔸, IsSupportOf A x → a ∈ A) := by
  simp only [supp, Set.Finite.mem_toFinset, Set.mem_iInter, Finset.mem_coe]

lemma supp_min {A : Finset 𝔸} {x : X} (h : IsSupportOf A x) : supp 𝔸 x ⊆ A := by
  intro a h'
  simp only [mem_supp] at h'
  apply h' A h

@[simp, grind ←]
lemma isSupportOf_supp
    (𝔸) [RenameAction 𝔸 X] [RenamingSet 𝔸 X] [Infinite 𝔸] (x : X)
    : IsSupportOf (supp 𝔸 x) x := by
  classical
  obtain ⟨A, hA⟩ := exists_support 𝔸 x

  have : Std.Commutative (· ∩ · : Finset 𝔸 → Finset 𝔸 → Finset 𝔸) := by
    constructor
    apply Finset.inter_comm

  have : Std.Associative (· ∩ · : Finset 𝔸 → Finset 𝔸 → Finset 𝔸) := by
    constructor
    simp only [Finset.inter_assoc, implies_true]

  have : IsSupportOf
      (Finset.fold (· ∩ ·) A
        (fun B ↦ if IsSupportOf B x then B else A)
        A.powerset)
      x := by
    generalize Finset.powerset A = B
    induction B using Finset.induction with
    | empty => simp only [Finset.fold_empty, hA]
    | insert B s ha ih =>
      simp only [ha, not_false_eq_true, Finset.fold_insert]
      apply isSupportOf_inter
      · by_cases hB : IsSupportOf B x
        · simp only [hB, ↓reduceIte]
        · simp only [hB, ↓reduceIte, hA]
      · apply ih

  have : supp 𝔸 x
       = Finset.fold (· ∩ ·) A (fun B ↦ if IsSupportOf B x then B else A) A.powerset := by
    rw [subset_antisymm_iff]
    apply And.intro
    · apply supp_min
      assumption
    · simp only [supp, Set.Finite.subset_toFinset, Set.subset_iInter_iff, Finset.coe_subset]
      intro B hB
      have : A ∩ B ∈ Finset.powerset A := by
        simp only [Finset.mem_powerset, Finset.inter_subset_left]
      have : Finset.powerset A = insert (A ∩ B) ((Finset.powerset A).erase (A ∩ B)) := by
        simp only [Finset.mem_powerset, Finset.inter_subset_left, Finset.insert_erase]
      rw [this]
      have : IsSupportOf (A ∩ B) x := isSupportOf_inter hA hB
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_powerset,
        Finset.inter_subset_left, and_true, not_false_eq_true, Finset.fold_insert,
        this, ↓reduceIte, Finset.inter_assoc]
      trans
      · apply Finset.inter_subset_right
      · apply Finset.inter_subset_left
  rw [this]

  assumption

lemma rename_congr
    [Infinite 𝔸]
    {f g : Ren 𝔸} (x : X) (h : ∀ a ∈ supp 𝔸 x, f a = g a)
    : rename f x = rename g x := by
  have := isSupportOf_supp 𝔸 x
  apply this.eq
  exact h

lemma rename_congr'
    [Infinite 𝔸]
    {f : Ren 𝔸} (x : X) (h : ∀ a ∈ supp 𝔸 x, f a = a)
    : rename f x = x := by
  nth_rw 2 [← rename_one (𝔸 := 𝔸) x]
  apply rename_congr
  exact h

end RenamingSets
