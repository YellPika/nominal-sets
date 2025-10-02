import NominalSets.PermAction.Basic
import NominalSets.Support.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Powerset

namespace NominalSets

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

/-! ## IsSupportOf -/

lemma isSupportOf_def
    (A : Finset 𝔸) (x : X)
    : IsSupportOf A x ↔ ∀π, (∀a ∈ A, π a = a) → perm π x = x := by
  apply Iff.intro
  · apply IsSupportOf.eq
  · apply IsSupportOf.mk

@[simp]
lemma isSupportOf_perm
    [DecidableEq 𝔸]
    (A : Finset 𝔸) (π : Perm 𝔸) (x : X)
    : IsSupportOf A (perm π x) ↔ IsSupportOf (A.image π.invFun) x := by
  apply Iff.intro
  · rintro ⟨hA⟩
    constructor
    intro π' hπ'
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hπ'
    have : ∀a ∈ A, (π  * π' * π⁻¹) a = a := by
      intro a ha
      specialize hπ' a ha
      simp only [Perm.mul_toFun, Perm.inv_toFun, hπ', Perm.right_inverse]
    specialize hA _ this
    simp only [perm_mul, inv_mul_cancel_right] at hA
    simp only [← perm_mul, perm_inj] at hA
    exact hA
  · rintro ⟨hA⟩
    constructor
    intro π' hπ'
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hA
    specialize hA (π⁻¹ * π' * π) (by simp_all only [
      Perm.mul_toFun, Perm.right_inverse,
      Perm.inv_toFun, implies_true])
    simp only [← perm_mul] at hA
    nth_rw 2 [←hA]
    simp only [perm_mul, Perm.mul_assoc, mul_inv_cancel_left]

@[simp]
lemma isSupportOf_univ [Fintype 𝔸] (x : X) : IsSupportOf (Finset.univ : Finset 𝔸) x := by
  constructor
  simp only [Finset.mem_univ, forall_const]
  intro π hπ
  have : π = 1 := by
    ext
    simp only [hπ, Perm.one_toFun]
  simp only [this, PermAction.perm_one]

lemma isSupportOf_monotone (x : X) : Monotone (IsSupportOf (𝔸 := 𝔸) · x) := by
  intro A B h hA
  constructor
  intro π hπ
  rw [hA.eq]
  intro x hx
  specialize h hx
  apply hπ
  exact h

lemma isSupportOf_swap
    [DecidableEq 𝔸]
    (A : Finset 𝔸) (x : X)
    : IsSupportOf A x ↔ (∀{a b}, a ∉ A → b ∉ A → perm (.swap a b) x = x) := by
  apply Iff.intro
  · intro hx a b ha hb
    apply hx.eq
    intro c hc
    simp only [Perm.swap_toFun]
    grind
  · intro h
    constructor
    intro π hπ
    have ⟨Y, hπ'⟩ := π.has_supp
    induction Y using Finset.induction generalizing π A x with
    | empty =>
      simp only [Finset.notMem_empty, not_false_eq_true, forall_const] at hπ'
      have : π = 1 := by
        ext
        simp only [hπ', Perm.one_toFun]
      simp only [this, PermAction.perm_one]
    | insert a s ha ih =>
      by_cases hfaa : π a = a
      · apply ih A x h
        · apply hπ
        · intro b hb
          by_cases hab : b = a
          · simp only [hab, hfaa]
          · apply hπ'
            simp only [Finset.mem_insert, hab, hb, or_self, not_false_eq_true]
      · have hfa : ¬π.invFun a = a := by
          intro hfa
          have := congr_arg π hfa
          simp only [Perm.right_inverse] at this
          grind
        have hfa' : π.invFun a ∈ s := by
          by_contra hfa'
          specialize hπ' (π.invFun a)
          simp only [
            Finset.mem_insert, hfa, hfa', or_self, not_false_eq_true,
            Perm.right_inverse, forall_const] at hπ'
          grind
        have ha' : a ∉ A := by
          intro ha'
          specialize hπ a ha'
          contradiction
        have hfa'' : π.invFun a ∉ A := by
          intro hfa''
          specialize hπ (π.invFun a) hfa''
          simp only [Perm.right_inverse] at hπ
          grind
        specialize ih (A \ {a}) x ?_ (π * (.swap a (π.invFun a))) ?_ ?_
        · intro b c hb hc
          simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not] at hb hc
          by_cases hba : b = a
          · subst hba
            by_cases hcb : c = b
            · subst hcb
              simp only [Perm.swap_eq, PermAction.perm_one]
            · simp only [hcb, imp_false] at hc
              apply h ha' hc
          · by_cases hca : c = a
            · subst hca
              simp only [hba, imp_false] at hb
              apply h hb ha'
            · simp only [hca, imp_false, hba] at hc hb
              apply h hb hc
        · intro b hb
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
          have hab : a ≠ b := by grind
          have hfab : π.invFun a ≠ b := by grind
          simp only [Perm.mul_toFun, Perm.swap_toFun, hab, ↓reduceIte, hfab]
          apply hπ
          exact hb.1
        · intro b hb
          by_cases hab : a = b
          · simp only [hab, Perm.mul_toFun, Perm.swap_toFun, ↓reduceIte, Perm.right_inverse]
          · have hfab : π.invFun a ≠ b := by grind
            simp only [Perm.mul_toFun, Perm.swap_toFun, hab, ↓reduceIte, hfab]
            apply hπ'
            simp only [Finset.mem_insert, hb, or_false]
            grind
        specialize h ha' hfa''
        nth_rw 1 [←h]
        simp only [PermAction.perm_mul, ih]

lemma isSupportOf_union_left
    [DecidableEq 𝔸]
    {A B : Finset 𝔸}
    {x : X} (h : IsSupportOf A x)
    : IsSupportOf (A ∪ B) x := by
  have : A ≤ A ∪ B := by
    simp only [Finset.le_eq_subset, Finset.subset_union_left]
  apply isSupportOf_monotone x this h

lemma isSupportOf_union_right
    [DecidableEq 𝔸]
    {A B : Finset 𝔸}
    {x : X} (h : IsSupportOf B x)
    : IsSupportOf (A ∪ B) x := by
  have : B ≤ A ∪ B := by
    simp only [Finset.le_eq_subset, Finset.subset_union_right]
  apply isSupportOf_monotone x this h

lemma isSupportOf_inter
    [PermAction 𝔸 X] [DecidableEq 𝔸] [Infinite 𝔸]
    {A B : Finset 𝔸} {x : X} (hA : IsSupportOf A x) (hB : IsSupportOf B x)
    : IsSupportOf (A ∩ B) x := by
  simp only [isSupportOf_swap, Finset.mem_inter, not_and] at ⊢ hA hB
  intro a b ha hb
  wlog hab : a ≠ b
  · simp only [ne_eq, Decidable.not_not] at hab
    simp only [hab, Perm.swap_eq, PermAction.perm_one]

  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (A ∪ B ∪ {b})
  simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, not_or] at hc

  have : Perm.swap a b = Perm.swap a c * Perm.swap b c * Perm.swap a c := by
    ext d
    simp only [Perm.swap_toFun, Perm.mul_toFun, left_eq_ite_iff]
    grind
  simp only [this, ←PermAction.perm_mul]

  by_cases a ∈ A <;> by_cases b ∈ B <;> grind

@[simp]
lemma isSupportOf_discrete [DiscretePermAction 𝔸 X] {A : Finset 𝔸} (x : X) : IsSupportOf A x := by
  constructor
  simp only [perm_discrete, implies_true]

lemma isSupportOf_lift {Y}
    (eq : X ≃ Y) (A : Finset 𝔸) (y : Y)
    : IsSupportOf[.lift 𝔸 eq] A y ↔ IsSupportOf A (eq.symm y) := by
  let : PermAction 𝔸 Y := .lift 𝔸 eq
  simp only [isSupportOf_def, perm_lift]
  apply Iff.intro
  · intro h π hπ
    nth_rw 2 [←h π hπ]
    simp only [Equiv.symm_apply_apply]
  · intro h π hπ
    simp_all only [implies_true, Equiv.apply_symm_apply]

/-! ## IsSupported -/

lemma isSupported_def (x : X) : IsSupported 𝔸 x ↔ ∃A : Finset 𝔸, IsSupportOf A x := by
  apply Iff.intro <;>
  · rintro ⟨A, hA⟩
    use A

@[simp]
lemma isSupported_perm (π : Perm 𝔸) (x : X) : IsSupported 𝔸 (perm π x) ↔ IsSupported 𝔸 x := by
  classical
  apply Iff.intro
  · rintro ⟨A, hA⟩
    use Finset.image π.invFun A
    simp only [isSupportOf_perm] at hA
    exact hA
  · rintro ⟨A, hA⟩
    use Finset.image π A
    simp +unfoldPartialApp only [
      isSupportOf_perm, Finset.image_image, Function.comp,
      Perm.left_inverse, Finset.image_id', hA]

@[simp]
lemma isSupported_discrete [DiscretePermAction 𝔸 X] (x : X) : IsSupported 𝔸 x := by
  use ∅
  simp only [isSupportOf_discrete]

lemma isSupported_lift {Y}
    (eq : X ≃ Y) (y : Y)
    : IsSupported[.lift 𝔸 eq] y ↔ IsSupported 𝔸 (eq.symm y) := by
  simp only [isSupported_def, isSupportOf_lift]

/-! ## IsSupportedF -/

lemma isSupportedF_def
    (f : X → Y)
    : IsSupportedF 𝔸 f
    ↔ ∃A : Finset 𝔸, ∀π : Perm 𝔸, (∀a ∈ A, π a = a) → ∀x, perm π (f x) = f (perm π x) := by
  apply Iff.intro <;>
  · rintro ⟨A, hA⟩
    use A

@[simp, fun_prop]
lemma isSupportedF_id : IsSupportedF 𝔸 (id : X → X) := by
  use ∅
  simp only [implies_true, id_eq]

@[simp, fun_prop]
lemma isSupportedF_id' : IsSupportedF 𝔸 (fun x : X ↦ x) := by
  use ∅
  simp only [implies_true]

@[fun_prop]
lemma isSupportedF_comp
    {f : Y → Z} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (f ∘ g) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  simp_all only [Finset.mem_union, Function.comp_apply, true_or, implies_true, or_true]

@[fun_prop]
lemma isSupportedF_comp'
    {f : Y → Z} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ f (g x)) := by
  fun_prop

@[simp, fun_prop]
lemma isSupportedF_const [Nominal 𝔸 Y] (y : Y) : IsSupportedF 𝔸 (Function.const X y) := by
  obtain ⟨A, ⟨hA⟩⟩ := Nominal.supported 𝔸 y
  use A
  simp_all only [Function.const_apply, implies_true]

@[simp, fun_prop]
lemma isSupportedF_const' [Nominal 𝔸 Y] (y : Y) : IsSupportedF 𝔸 (fun _ : X ↦ y) :=
  isSupportedF_const y

/-! ## Equivariance -/

@[simp]
lemma isSupportOf_iff_equivariant (f : X → Y) : IsSupportOf (∅ : Finset 𝔸) f ↔ Equivariant 𝔸 f := by
  apply Iff.intro
  · rintro ⟨h⟩
    constructor
    intro π x
    nth_rw 2 [←h π (by grind)]
    simp only [Function.perm_def, perm_mul, inv_mul_cancel, perm_one]
  · rintro ⟨h⟩
    constructor
    intro π _
    ext x
    simp only [Function.perm_def, h π, perm_mul, mul_inv_cancel, perm_one]

@[simp, fun_prop]
lemma equivariant_id : Equivariant 𝔸 (id : X → X) := by
  constructor
  simp only [id_eq, implies_true]

@[simp, fun_prop]
lemma equivariant_id' : Equivariant 𝔸 (fun x : X ↦ x) := by
  constructor
  simp only [implies_true]

@[fun_prop]
lemma equivariant_comp
    {f : Y → Z} (hf : Equivariant 𝔸 f)
    {g : X → Y} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (f ∘ g) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  constructor
  simp only [Function.comp_apply, hf, hg, implies_true]

@[fun_prop]
lemma equivariant_comp'
    {f : Y → Z} (hf : Equivariant 𝔸 f)
    {g : X → Y} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (fun x ↦ f (g x)) := by
  fun_prop

@[simp, fun_prop]
lemma equivariant_const [DiscretePermAction 𝔸 Y] (y : Y) : Equivariant 𝔸 (Function.const X y) := by
  constructor
  simp only [Function.const_apply, perm_discrete, implies_true]

@[simp, fun_prop]
lemma equivariant_const' [DiscretePermAction 𝔸 Y] (y : Y) : Equivariant 𝔸 (fun _ : X ↦ y) :=
  equivariant_const y

/-! ## Nominal -/

namespace PermAction

instance [Nominal 𝔸 X] (eq : X ≃ Y) : Nominal[lift 𝔸 eq] := by
  let : PermAction 𝔸 Y := lift 𝔸 eq
  constructor
  intro y
  simp only [isSupported_lift, Nominal.supported]

instance : Nominal 𝔸 𝔸 where
  supported a := by
    use {a}
    constructor
    intro π hπ
    simp only [Finset.mem_singleton, forall_eq] at hπ
    simp only [perm_def, hπ]

end PermAction

namespace DiscretePermAction
instance [DiscretePermAction 𝔸 X] : Nominal 𝔸 X where
end DiscretePermAction

/-! ## supp -/

lemma mem_supp
    [Nominal 𝔸 X] (a : 𝔸) (x : X)
    : a ∈ supp 𝔸 x ↔ (∀ A : Finset 𝔸, IsSupportOf A x → a ∈ A) := by
  simp only [supp, Set.Finite.mem_toFinset, Set.mem_iInter, Finset.mem_coe]

lemma mem_supp'
    [DecidableEq 𝔸] [Nominal 𝔸 X] (a : 𝔸) (x : X)
    : a ∈ supp 𝔸 x ↔ {b | perm (.swap a b) x ≠ x}.Infinite := by
  apply Iff.intro
  · simp only [mem_supp, ne_eq]
    intro h
    by_contra hx
    simp only [Set.not_infinite] at hx
    specialize h hx.toFinset
    simp only [
      Set.Finite.mem_toFinset, Set.mem_setOf_eq, Perm.swap_eq,
      perm_one, not_true_eq_false, imp_false] at h
    simp only [
      isSupportOf_swap, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_not, not_forall] at h
    rcases h with ⟨b, c, hb, hc, h⟩
    apply h
    wlog hbc : b ≠ c
    · simp only [ne_eq, Decidable.not_not] at hbc
      subst hbc
      simp only [Perm.swap_eq, perm_one]
    wlog hca : c ≠ a
    · simp only [ne_eq, Decidable.not_not] at hca
      subst hca
      rw [Perm.swap_comm, hb]
    have : Perm.swap b c = Perm.swap a b * Perm.swap a c * Perm.swap a b := by
      ext d
      simp only [Perm.swap_toFun, Perm.mul_toFun]
      grind
    simp [this, ←PermAction.perm_mul, hc, hb]
  · intro h
    simp only [mem_supp]
    intro A ⟨hA⟩
    by_contra ha
    obtain ⟨b, hb⟩ := h.exists_notMem_finset (A ∪ {a})
    simp only [ne_eq, Set.mem_setOf_eq, Finset.union_singleton, Finset.mem_insert, not_or] at hb
    specialize hA (.swap a b) (by simp only [Perm.swap_toFun]; grind)
    grind

lemma supp_min [Nominal 𝔸 X] {A : Finset 𝔸} {x : X} (h : IsSupportOf A x) : supp 𝔸 x ⊆ A := by
  intro a h'
  simp only [mem_supp] at h'
  apply h' A h

@[simp]
lemma isSupportOf_supp
    (𝔸) [PermAction 𝔸 X] [Nominal 𝔸 X] [Infinite 𝔸] (x : X)
    : IsSupportOf (supp 𝔸 x) x := by
  classical
  obtain ⟨A, hA⟩ := Nominal.supported 𝔸 x

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

end NominalSets
