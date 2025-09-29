import NominalSets.Function
import NominalSets.Option
import NominalSets.Nat

namespace NominalSets.List

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

@[simps -isSimp]
instance : PermAction 𝔸 (List X) where
  perm π := List.map (perm π)
  perm_one x := by
    simp only [perm_one', List.map_id_fun, id_eq]
  perm_mul π₁ π₂ x := by
    simp only [List.map_map, List.map_inj_left, Function.comp_apply, perm_mul, implies_true]

@[simp]
lemma perm_nil (π : Perm 𝔸) : perm π ([] : List X) = [] := by rfl

@[simp]
lemma perm_cons
    (π : Perm 𝔸) (x : X) (xs : List X)
    : perm π (x :: xs) = perm π x :: perm π xs := by rfl

@[simp]
lemma perm_foldr
    (π : Perm 𝔸) (f : X → Y → Y) (z : Y) (xs : List X)
    : perm π (List.foldr f z xs) = List.foldr (perm π f) (perm π z) (perm π xs) := by
  induction xs generalizing π with
  | nil => simp only [List.foldr_nil, perm_nil]
  | cons head tail ih =>
    simp only [
      List.foldr_cons, perm_cons, ← ih, Function.perm_def,
      perm_mul, inv_mul_cancel, perm_one]

@[simp]
lemma getElem?_perm (π : Perm 𝔸) (xs : List X) (i : ℕ) : perm π xs[i]? = (perm π xs)[i]? := by
  induction xs generalizing i with
  | nil => simp only [
      perm_nil, List.length_nil, Nat.not_lt_zero,
      not_false_eq_true, getElem?_neg, Option.perm_none]
  | cons head tail ih =>
    cases i with
    | zero => simp only [
      perm_cons, List.length_cons, Nat.zero_lt_succ, getElem?_pos,
      List.getElem_cons_zero, Option.perm_some]
    | succ i => simp only [perm_cons, List.getElem?_cons_succ, ih]

@[simp]
lemma perm_append
    (π : Perm 𝔸) (xs ys : List X)
    : perm π (xs ++ ys) = perm π xs ++ perm π ys := by
  simp only [perm_def, List.map_append]

instance [DiscretePermAction 𝔸 X] : DiscretePermAction 𝔸 (List X) where
  perm_discrete _ xs := by
    induction xs with
    | nil => simp only [perm_nil]
    | cons head tail ih => simp only [perm_cons, perm_discrete, ih]

@[simp]
lemma isSupportOf_nil (A : Finset 𝔸) : IsSupportOf A ([] : List X) := by
  simp only [isSupportOf_def, perm_nil, implies_true]

@[simp]
lemma isSupportOf_cons
    (A : Finset 𝔸) (x : X) (xs : List X)
    : IsSupportOf A (x :: xs) ↔ IsSupportOf A x ∧ IsSupportOf A xs := by
  simp only [isSupportOf_def, perm_cons, List.cons.injEq]
  grind

@[simp]
lemma isSupported_nil : IsSupported 𝔸 ([] : List X) := by
  simp only [isSupported_def, isSupportOf_nil, exists_const]

@[simp]
lemma isSupported_cons
    (x : X) (xs : List X)
    : IsSupported 𝔸 (x :: xs) ↔ IsSupported 𝔸 x ∧ IsSupported 𝔸 xs := by
  have : IsSupported 𝔸 (x :: xs) ↔ IsSupported 𝔸 (x, xs) := by
    simp only [isSupported_def, isSupportOf_cons, Prod.isSupportOf_mk]
  simp only [this, Prod.isSupported_mk]

instance [Nominal 𝔸 X] : Nominal 𝔸 (List X) where
  supported xs := by
    induction xs with
    | nil => simp only [isSupported_nil]
    | cons head tail ih => simp only [isSupported_cons, Nominal.supported, ih, and_self]

@[simp]
lemma supp_nil [Nominal 𝔸 X] : supp 𝔸 ([] : List X) = ∅ := by
  ext a
  simp only [mem_supp, isSupportOf_nil, forall_const, Finset.notMem_empty, iff_false, not_forall]
  use ∅
  simp only [Finset.notMem_empty, not_false_eq_true]

@[simp]
lemma supp_cons
    [DecidableEq 𝔸] [Nominal 𝔸 X] (x : X) (xs : List X)
    : supp 𝔸 (x :: xs) = supp 𝔸 x ∪ supp 𝔸 xs := by
  have : supp 𝔸 (x :: xs) = supp 𝔸 (x, xs) := by
    ext a
    simp only [mem_supp, Prod.isSupportOf_mk, isSupportOf_cons, and_imp]
  simp only [this, Prod.supp_mk]

@[simp, fun_prop]
lemma isSupportedF_nil : IsSupportedF 𝔸 (fun _ : X ↦ ([] : List Y)) := by
  use ∅
  simp only [implies_true, perm_nil]

@[simp, fun_prop]
lemma isSupportedF_cons : IsSupportedF 𝔸 (fun ((x, xs) : X × List X) ↦ x :: xs) := by
  use ∅
  simp only [implies_true, perm_cons]

@[fun_prop]
lemma isSupportedF_foldr
    {f : X → Y → Z → Z} (hf : IsSupportedF 𝔸 fun (x, y, z) ↦ f x y z)
    {g : X → Z} (hg : IsSupportedF 𝔸 g)
    {h : X → List Y} (hh : IsSupportedF 𝔸 h)
    : IsSupportedF 𝔸 (fun x ↦ List.foldr (f x) (g x) (h x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨C, hC⟩ := hh
  use A ∪ B ∪ C
  intro π hπ x
  replace hA : perm π (f x) = f (perm π x) := by
    ext y z
    simp only [Prod.perm_fst, Prod.perm_snd, Prod.forall, Prod.perm_mk] at hA
    simp (disch := grind) only [Function.perm_def, hA, perm_mul, mul_inv_cancel, perm_one]
  simp (disch := grind) only [perm_foldr, hA, hB, hC]

@[simp, fun_prop]
lemma isSupportedF_getElem? : IsSupportedF 𝔸 (fun x : List X × ℕ ↦ x.1[x.2]?) := by
  use ∅
  simp only [Prod.forall, Prod.perm_mk, perm_discrete, getElem?_perm, implies_true]

@[simp, fun_prop]
lemma isSupportedF_append : IsSupportedF 𝔸 (fun x : List X × List X ↦ x.1 ++ x.2) := by
  use ∅
  simp only [perm_append, Prod.perm_fst, Prod.perm_snd, implies_true]

@[fun_prop]
lemma isSupportedF_map
    {f : X → Y → Z} (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    {g : X → List Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ List.map (f x) (g x)) := by
  have {x} : List.map (f x) (g x) = List.foldr (fun y ys ↦ f x y :: ys) [] (g x) := by
    simp only [List.foldr_cons_eq_append, List.append_nil]
  simp only [this]
  fun_prop

end NominalSets.List
