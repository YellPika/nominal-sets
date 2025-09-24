import FinitelySupported.Supported.Defs
import FinitelySupported.Perm.Basic
import FinitelySupported.PermAction.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Powerset

open PermAction

namespace Supported

variable {𝔸 X Y Z} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

namespace FS

instance : Supported 𝔸 (FS 𝔸 X) where
  has_supp x := by
    obtain ⟨A, hA⟩ := x.property
    use A
    constructor
    intro π hπ
    ext
    apply hA.eq π hπ

end FS

instance [Supported 𝔸 X] (eq : X ≃ Y) : @Supported 𝔸 Y (.lift 𝔸 eq) := by
  apply @Supported.mk 𝔸 Y (.lift 𝔸 eq)
  intro y
  have ⟨A, hA⟩ := has_supp 𝔸 (eq.symm y)
  use A
  apply @IsSupp.mk 𝔸 Y (.lift 𝔸 eq)
  intro π hπ
  have := hA.eq π hπ
  simp only [PermAction.perm_lift, this, Equiv.apply_symm_apply]

instance {X} : @Supported 𝔸 X default := by
  apply @Supported.mk 𝔸 X default
  simp only [IsSupp.default, exists_const, implies_true]

lemma isHom_of_lift {Y} (eq : X ≃ Y) : IsHom[lift 𝔸 eq, _] eq.symm := by
  use ∅
  simp only [
    Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    lift, Equiv.invFun_as_coe, Equiv.symm_apply_apply]

lemma isHom_to_lift
    {Y} (eq : X ≃ Y) (f : Z → Y)
    : IsHom[_, lift 𝔸 eq] f ↔ IsHom 𝔸 (fun x ↦ eq.symm (f x)) := by
  apply Iff.intro <;>
  · rintro ⟨A, hA⟩
    use A
    simp only [lift, Equiv.invFun_as_coe] at ⊢ hA
    grind

@[simp]
lemma mem_supp
    [Supported 𝔸 X]
    (a : 𝔸) (x : X)
    : a ∈ supp 𝔸 x ↔ ∀A, IsSupp A x → a ∈ A := by
  simp only [supp, Set.Finite.mem_toFinset, Set.mem_iInter, Finset.mem_coe]

lemma supp_min
    {A} [Supported 𝔸 X]
    (x : X) (hA : IsSupp A x)
    : supp 𝔸 x ⊆ A := by
  simp only [supp, Set.Finite.toFinset_subset]
  trans ⋂ (_ : IsSupp A x), A
  · apply Set.iInter_subset
  · simp only [hA, Set.iInter_true, subset_refl]

@[simp]
lemma isSupp_supp
    (𝔸) [PermAction 𝔸 X] [Supported 𝔸 X] [Infinite 𝔸] (x : X)
    : IsSupp (supp 𝔸 x) x := by
  classical
  obtain ⟨A, hA⟩ := has_supp 𝔸 x

  have : Std.Commutative (· ∩ · : Finset 𝔸 → Finset 𝔸 → Finset 𝔸) := by
    constructor
    apply Finset.inter_comm

  have : Std.Associative (· ∩ · : Finset 𝔸 → Finset 𝔸 → Finset 𝔸) := by
    constructor
    simp only [Finset.inter_assoc, implies_true]

  have : IsSupp
      (Finset.fold (· ∩ ·) A
        (fun B ↦ if IsSupp B x then B else A)
        A.powerset)
      x := by
    generalize Finset.powerset A = B
    induction B using Finset.induction with
    | empty => simp only [Finset.fold_empty, hA]
    | insert B s ha ih =>
      simp only [ha, not_false_eq_true, Finset.fold_insert]
      apply IsSupp.inter
      · by_cases hB : IsSupp B x
        · simp only [hB, ↓reduceIte]
        · simp only [hB, ↓reduceIte, hA]
      · apply ih

  have : supp 𝔸 x
       = Finset.fold (· ∩ ·) A (fun B ↦ if IsSupp B x then B else A) A.powerset := by
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
      have : IsSupp (A ∩ B) x := IsSupp.inter hA hB
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_powerset,
        Finset.inter_subset_left, and_true, not_false_eq_true, Finset.fold_insert,
        this, ↓reduceIte, Finset.inter_assoc]
      trans
      · apply Finset.inter_subset_right
      · apply Finset.inter_subset_left
  rw [this]

  assumption

@[simp]
lemma isHom_const [Supported 𝔸 Y] (y : Y) : IsHom 𝔸 (Function.const X y) := by
  obtain ⟨A, hA⟩ := has_supp 𝔸 y
  apply PermAction.isHom_const A hA

@[fun_prop, simp]
lemma isHom_const' [Supported 𝔸 Y] (y : Y) : IsHom 𝔸 (fun _ : X ↦ y) :=
  isHom_const y

@[fun_prop]
lemma isHom_apply [Supported 𝔸 X] (x : X) : IsHom 𝔸 (fun f : X → Y ↦ f x) := by
  obtain ⟨A, hA⟩ := has_supp 𝔸 x
  use A
  intro π f hπ
  simp only [Function.perm_def]
  rw [hA.eq]
  intro a ha
  apply π.injective
  simp only [Perm.inv_toFun, Perm.right_inverse, hπ a ha]

@[fun_prop]
lemma isHom_perm (π : Perm 𝔸) : IsHom 𝔸 ((perm π ·) : X → X) := by
  classical
  apply Function.isHom_of_isSupp π.supp
  rw [IsSupp.swap]
  intro a b ha hb
  ext x
  have : Perm.swap a b * π = π * Perm.swap a b := by
    ext c
    simp only [Perm.mem_supp, ne_eq, Decidable.not_not] at ha hb
    simp only [Perm.mul_toFun, Perm.swap_toFun]
    by_cases hac : a = c
    · grind
    · by_cases hbc : b = c
      · grind
      · have : a ≠ π c := by
          rw [←ha]
          rintro hac'
          have := π.injective hac'
          contradiction
        simp only [this, ↓reduceIte, hac, hbc, ite_eq_right_iff, imp_false]
        rw [←hb]
        intro hbc'
        have := π.injective hbc'
        contradiction
  simp only [Function.perm_def, Perm.inv_swap, perm_mul, Perm.mul_assoc, this, Perm.swap_swap_l]

@[simp]
lemma supp_default {X} (x : X) : @supp X 𝔸 default _ x = ∅ := by
  ext a
  simp only [Finset.notMem_empty, iff_false]
  intro ha
  simp only [mem_supp, IsSupp.default, forall_const] at ha
  specialize ha ∅
  contradiction

@[fun_prop]
lemma FS.isHom_mk
    {f : X → Y} (hf : IsHom 𝔸 f)
    (p : ∀ x, ∃ A, IsSupp A (f x))
    : IsHom 𝔸 (fun x ↦ FS.mk (𝔸 := 𝔸) (f x) (p x)) := by
  obtain ⟨A, hA⟩ := hf
  use A
  intro π x hπ
  ext
  simp only [perm_val]
  grind

end Supported
