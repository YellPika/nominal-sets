import NominalSets.List
import RoseTree

namespace NominalSets.Rose

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

instance : PermAction 𝔸 (Rose X) where
  perm π := Rose.map (perm π)
  perm_one x := by simp only [perm_one', id_eq, implies_true, Rose.map_id]
  perm_mul π₁ π₂ x := by simp only [Rose.map_map, perm_mul]

lemma perm_def (π : Perm 𝔸) (t : Rose X) : perm π t = Rose.map (perm π) t := rfl

@[simp]
lemma perm_mk
    (π : Perm 𝔸) (x : X) (xs : List (Rose X))
    : perm π (Rose.mk x xs) = .mk (perm π x) (perm π xs) := by
  simp only [
    perm_def, Rose.map_mk, List.perm_def, Rose.mk.injEq,
    List.map_inj_left, implies_true, and_self]

@[simp]
lemma perm_fold
    (π : Perm 𝔸) (f : X → List Y → Y) (t : Rose X)
    : perm π (Rose.fold f t) = Rose.fold (perm π f) (perm π t) := by
  induction t generalizing π with
  | mk label children ih =>
    simp only [
      Rose.fold.eq_1, perm_mk, List.perm_def, List.map_map, Function.perm_def,
      perm_mul, inv_mul_cancel, perm_one, perm_inj]
    congr 1
    simp only [List.map_inj_left, Function.comp_apply]
    intro t ht
    simp only [← ih t ht, perm_mul, inv_mul_cancel, perm_one]

instance [DiscretePermAction 𝔸 X] : DiscretePermAction 𝔸 (Rose X) where
  perm_discrete _ t := by
    induction t with | mk label children ih =>
    simp only [perm_mk, perm_discrete, List.perm_def, Rose.mk.injEq, true_and]
    nth_rw 2 [(by simp only [List.map_id_fun, id_eq] : children = List.map id children)]
    simp only [List.map_inj_left, id_eq]
    exact ih

@[simp]
lemma isSupportOf_mk
    (A : Finset 𝔸) (x : X) (xs : List (Rose X))
    : IsSupportOf A (Rose.mk x xs) ↔ IsSupportOf A x ∧ IsSupportOf A xs := by
  simp only [isSupportOf_def, perm_mk, Rose.mk.injEq]
  grind

@[simp]
lemma isSupported_mk
    (x : X) (xs : List (Rose X))
    : IsSupported 𝔸 (Rose.mk x xs) ↔ IsSupported 𝔸 x ∧ IsSupported 𝔸 xs := by
  have : IsSupported 𝔸 (Rose.mk x xs) ↔ IsSupported 𝔸 (x, xs) := by
    simp only [isSupported_def, isSupportOf_mk, Prod.isSupportOf_mk]
  simp only [this, Prod.isSupported_mk]

instance [Nominal 𝔸 X] : Nominal 𝔸 (Rose X) where
  supported t := by
    induction t with | mk label children ih =>
    simp only [isSupported_mk, Nominal.supported, true_and]
    induction children with
    | nil => simp only [List.isSupported_nil]
    | cons head tail ih' =>
      simp only [List.isSupported_cons]
      grind

@[simp]
lemma supp_mk
    [DecidableEq 𝔸] [Nominal 𝔸 X]
    (x : X) (xs : List (Rose X))
    : supp 𝔸 (Rose.mk x xs) = supp 𝔸 x ∪ supp 𝔸 xs := by
  have : supp 𝔸 (Rose.mk x xs) = supp 𝔸 (x, xs) := by
    ext a
    simp only [mem_supp, Prod.isSupportOf_mk, isSupportOf_mk, and_imp]
  simp only [this, Prod.supp_mk]

@[simp, fun_prop]
lemma isSupportedF_mk : IsSupportedF 𝔸 (fun ((x, xs) : X × List (Rose X)) ↦ Rose.mk x xs) := by
  use ∅
  dsimp only
  simp only [perm_mk, Prod.perm_fst, Prod.perm_snd, implies_true]

lemma isSupportedF_mk'
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    {g : X → List (Rose Y)} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ Rose.mk (f x) (g x)) := by
  fun_prop

@[fun_prop]
lemma isSupportedF_fold
    {f : X → Y → List Z → Z} (hf : IsSupportedF 𝔸 fun (x, y, z) ↦ f x y z)
    {g : X → Rose Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ Rose.fold (f x) (g x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  intro π hπ x
  replace hA : perm π (f x) = f (perm π x) := by
    ext y z
    simp only [Prod.forall] at hA
    simp (disch := grind) only [Function.perm_def, hA, perm_mul, mul_inv_cancel, perm_one]
  simp (disch := grind) only [perm_fold, hA, hB]

@[simp, fun_prop]
lemma isSupportedF_label : IsSupportedF 𝔸 (Rose.label : Rose X → X) := by
  have : Rose.label = Rose.fold (fun (x : X) _ ↦ x) := by
    ext ⟨x, xs⟩
    simp only [Rose.fold.eq_1]
  rw [this]
  fun_prop

@[simp, fun_prop]
lemma isSupportedF_children : IsSupportedF 𝔸 (Rose.children : Rose X → List (Rose X)) := by
  have
      : Rose.children
      = Prod.snd ∘ Rose.fold (fun (x : X) xs ↦ (x, List.map (fun x ↦ .mk x.1 x.2) xs)) := by
    ext t : 1
    simp only [Function.comp_apply]
    induction t with | mk label children ih =>
    simp only [Rose.fold.eq_1, List.map_map]
    nth_rw 1 [(by simp only [List.map_id_fun, id_eq] : children = List.map id children)]
    simp only [List.map_inj_left, id_eq, Function.comp_apply]
    intro ⟨x, xs⟩ ht
    specialize ih _ ht
    simp only [Rose.fold.eq_1, List.map_map] at ih
    simp only [Rose.fold.eq_1, List.map_map, ← ih]
  rw [this]
  fun_prop

@[simp, fun_prop]
lemma isSupportedF_bind
    {f : X → Y → Rose Z} (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    {g : X → Rose Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ Rose.bind (f x) (g x)) := by
  simp only [← Rose.fold_eq_bind]
  fun_prop

@[simp, fun_prop]
lemma isSupportedF_map
    {f : X → Y → Rose Z} (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    {g : X → Rose Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ Rose.map (f x) (g x)) := by
  simp only [← Rose.bind_eq_map]
  fun_prop

end NominalSets.Rose
