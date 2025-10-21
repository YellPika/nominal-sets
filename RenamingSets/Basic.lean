import RenamingSets.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

/-! ## `Ren` -/

namespace Ren

@[simp]
lemma exists_support (ρ : Ren 𝔸) : ∃A : Finset 𝔸, ∀a ∉ A, ρ a = a :=
  ρ.exists_support'

@[ext]
lemma ext {ρ₁ ρ₂ : Ren 𝔸} (h : ∀ a, ρ₁ a = ρ₂ a) : ρ₁ = ρ₂ := by
  rcases ρ₁
  rcases ρ₂
  simp only [mk.injEq]
  ext a
  apply h

instance : Monoid (Ren 𝔸) where
  mul_assoc _ _ _ := by
    simp only [Ren.ext_iff, mul_coe, implies_true]
  one_mul _ := by
    simp only [Ren.ext_iff, mul_coe, one_coe, implies_true]
  mul_one _ := by
    simp only [Ren.ext_iff, mul_coe, one_coe, implies_true]

@[simp]
lemma mem_supp (a : 𝔸) (ρ : Ren 𝔸) : a ∈ supp ρ ↔ ρ a ≠ a := by
  apply Iff.intro
  · simp only [supp, ne_eq, Finset.mem_filter, and_imp, imp_self, implies_true]
  · intro h
    simp only [supp, ne_eq, Finset.mem_filter, h, not_false_eq_true, and_true]
    by_contra h'
    apply h
    apply ρ.exists_support'.choose_spec
    exact h'

@[simp]
lemma swap_swap [DecidableEq 𝔸] (a b : 𝔸) : swap a b * swap a b = 1 := by
  ext c
  simp only [mul_coe, swap_coe, ite_eq_left_iff, one_coe]
  grind

@[simp]
lemma swap_swap_r [DecidableEq 𝔸] (a b : 𝔸) (σ : Ren 𝔸) : swap a b * (swap a b * σ) = σ := by
  ext c
  simp only [mul_coe, swap_coe, ite_eq_left_iff]
  grind

end Ren

/-! ## `RenameAction` -/

@[simp]
lemma rename_one' : rename (1 : Ren 𝔸) = (id : X → X) := by
  ext a
  simp only [rename_one, id_eq]

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
