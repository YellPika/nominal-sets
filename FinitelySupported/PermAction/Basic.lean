import FinitelySupported.Perm.Basic
import FinitelySupported.PermAction.Defs

open PermAction

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

namespace IsSupp

@[simp]
lemma univ [Fintype 𝔸] (x : X) : IsSupp (Finset.univ : Finset 𝔸) x := by
  constructor
  simp only [Finset.mem_univ, forall_const]
  intro π hπ
  have : π = 1 := by
    ext
    simp only [hπ, Perm.one_toFun]
  simp only [this, perm_one]

lemma monotone (x : X) : Monotone (IsSupp (𝔸 := 𝔸) · x) := by
  intro A B h hA
  constructor
  intro π hπ
  rw [hA.eq]
  intro x hx
  specialize h hx
  apply hπ
  exact h

lemma swap
    [DecidableEq 𝔸]
    (A : Finset 𝔸) (x : X)
    : IsSupp A x ↔ (∀{a b}, a ∉ A → b ∉ A → perm (.swap a b) x = x) := by
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
      simp only [this, perm_one]
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
              simp only [Perm.swap_eq, perm_one]
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
        simp only [perm_mul, ih]

lemma union_left
    [DecidableEq 𝔸]
    {A B : Finset 𝔸}
    {x : X} (h : IsSupp A x)
    : IsSupp (A ∪ B) x := by
  have : A ≤ A ∪ B := by
    simp only [Finset.le_eq_subset, Finset.subset_union_left]
  apply monotone x this h

lemma union_right
    [DecidableEq 𝔸]
    {A B : Finset 𝔸}
    {x : X} (h : IsSupp B x)
    : IsSupp (A ∪ B) x := by
  have : B ≤ A ∪ B := by
    simp only [Finset.le_eq_subset, Finset.subset_union_right]
  apply monotone x this h

lemma inter
    [PermAction 𝔸 X] [DecidableEq 𝔸] [Infinite 𝔸]
    {A B : Finset 𝔸} {x : X} (hA : IsSupp A x) (hB : IsSupp B x)
    : IsSupp (A ∩ B) x := by
  simp only [swap, Finset.mem_inter, not_and] at ⊢ hA hB
  intro a b ha hb
  wlog hab : a ≠ b
  · simp only [ne_eq, Decidable.not_not] at hab
    simp only [hab, Perm.swap_eq, perm_one]

  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (A ∪ B ∪ {b})
  simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, not_or] at hc

  have : Perm.swap a b = Perm.swap a c * Perm.swap b c * Perm.swap a c := by
    ext d
    simp only [Perm.swap_toFun, Perm.mul_toFun, left_eq_ite_iff]
    grind
  simp only [this, ←perm_mul]

  by_cases a ∈ A <;> by_cases b ∈ B <;> grind

end IsSupp

namespace PermAction

lemma perm_lift {Y} (eq : X ≃ Y) (π y) : @perm 𝔸 Y (.lift 𝔸 eq) π y = eq (perm π (eq.symm y)) := rfl

@[simp]
lemma perm_one' : perm (𝔸 := 𝔸) (X := X) 1 = id := by
  ext
  simp only [perm_one, id_eq]

@[simp, fun_prop]
lemma isHom_id : IsHom 𝔸 (id : X → X) := by
  use ∅
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, id_eq]

@[simp, fun_prop]
lemma isHom_id' : IsHom 𝔸 (fun x : X ↦ x) := isHom_id

@[simp, fun_prop]
lemma isHom_comp
    {f : Y → Z} (hf : IsHom 𝔸 f)
    {g : X → Y} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (f ∘ g) := by
  classical
  rcases hf with ⟨A, hA⟩
  rcases hg with ⟨B, hB⟩
  use A ∪ B
  intros
  simp (disch := grind) only [Function.comp_apply, hA, hB]

@[simp, fun_prop]
lemma isHom_comp'
    {f : Y → Z} (hf : IsHom 𝔸 f)
    {g : X → Y} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ f (g x)) :=
  isHom_comp hf hg

end PermAction
