import FinitelySupported.PermAction.Prod

namespace PermAction.List

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

@[simps]
instance : PermAction 𝔸 (List X) where
  perm π := List.map (perm π)
  perm_one := by simp only [perm_one', List.map_id_fun, id_eq, implies_true]
  perm_mul := by simp only [
    List.map_map, List.map_inj_left,
    Function.comp_apply, perm_mul, implies_true]

@[simp, fun_prop]
lemma isHom_nil : IsHom 𝔸 (fun _ : X ↦ ([] : List Y)) := by
  use ∅
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, perm_def, List.map_nil]

@[fun_prop]
lemma isHom_cons
    {f : X → Y} (hf : IsHom 𝔸 f)
    {g : X → List Y} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ f x :: g x) := by
  classical
  rcases hf with ⟨A, hA⟩
  rcases hg with ⟨B, hB⟩
  use A ∪ B
  simp only [Finset.mem_union, perm_def, List.map_cons, List.cons.injEq] at ⊢ hB
  intro π x hπ
  simp (disch := grind) only [hA, hB, true_and]

@[fun_prop]
lemma isHom_foldr
    {cons : X → Y → Z → Z} (hcons : IsHom 𝔸 fun (x, y, z) ↦ cons x y z)
    {nil : X → Z} (hnil : IsHom 𝔸 nil)
    {f : X → List Y} (hf : IsHom 𝔸 f)
    : IsHom 𝔸 (fun x ↦ List.foldr (cons x) (nil x) (f x)) := by
  classical
  rcases hcons with ⟨A, hA⟩
  rcases hnil with ⟨B, hB⟩
  rcases hf with ⟨C, hC⟩
  use A ∪ B ∪ C
  intro π x hπ
  simp (disch := grind) only [← hC, perm_def]
  simp only [Prod.forall] at hA hB
  induction f x with
  | nil =>
    simp (disch := grind) only [List.foldr_nil, List.map_nil, hB]
  | cons head tail ih =>
    simp (disch := grind) only [List.foldr_cons, hA, List.map_cons, ih]

lemma isSupp_iff (A : Finset 𝔸) (xs : List X) : IsSupp A xs ↔ (∀x ∈ xs, IsSupp A x) := by
  apply Iff.intro
  · rintro ⟨h⟩ x hx
    constructor
    simp only [perm_def] at h
    intro π hπ
    specialize h π hπ
    nth_rw 2 [←List.map_id xs] at h
    simp only [List.map_inj_left, id_eq] at h
    apply h _ hx
  · intro h
    constructor
    intro π hπ
    simp only [perm_def]
    nth_rw 2 [←List.map_id xs]
    simp only [List.map_inj_left, id_eq]
    intro x hx
    specialize h x hx
    apply h.eq π hπ

@[simp]
lemma isSupp_nil (A : Finset 𝔸) : IsSupp A ([] : List X) := by
  simp only [isSupp_iff, List.not_mem_nil, IsEmpty.forall_iff, implies_true]

@[simp]
lemma isSupp_cons
    (A : Finset 𝔸) (x : X) (xs : List X)
    : IsSupp A (x :: xs) ↔ IsSupp A x ∧ IsSupp A xs := by
  simp only [isSupp_iff, List.mem_cons, forall_eq_or_imp]

end PermAction.List
