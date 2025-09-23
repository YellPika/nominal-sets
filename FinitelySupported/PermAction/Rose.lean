import FinitelySupported.PermAction.List
import RoseTree

namespace PermAction.Rose

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

instance : PermAction 𝔸 (Rose X) where
  perm π := (perm π <$> ·)
  perm_one := by simp only [perm_one', Rose.map_eq, id_eq, implies_true, Rose.map_id]
  perm_mul := by simp only [Rose.map_eq, Rose.map_map, perm_mul, implies_true]

@[simp]
lemma perm_def (π : Perm 𝔸) : perm (X := Rose X) π = (perm π <$> ·) := rfl

@[fun_prop]
lemma isHom_mk
    {f : X → Y} (hf : IsHom 𝔸 f)
    {g : X → List (Rose Y)} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ Rose.mk (f x) (g x)) := by
  classical
  rcases hf with ⟨A, hA⟩
  rcases hg with ⟨B, hB⟩
  use A ∪ B
  simp only [
    List.perm_def, perm_def, Rose.map_eq,
    Finset.mem_union, Rose.map_mk, Rose.mk.injEq] at ⊢ hB
  intro π x hπ
  simp (disch := grind) only [hA, hB, true_and]

@[fun_prop]
lemma isHom_fold
    {mk : X → Y → List Z → Z} (hmk : IsHom 𝔸 fun (x, y, z) ↦ mk x y z)
    {f : X → Rose Y} (hf : IsHom 𝔸 f)
    : IsHom 𝔸 (fun x ↦ Rose.fold (mk x) (f x)) := by
  classical
  rcases hmk with ⟨A, hA⟩
  rcases hf with ⟨B, hB⟩
  use A ∪ B
  intro π x hπ
  simp (disch := grind) only [← hB, perm_def, Rose.map_eq, Rose.fold_map]
  simp only [List.perm_def, Prod.forall, perm_def, Rose.map_eq] at hA hB
  induction f x with | mk label children ih =>
  simp (disch := grind) only [Rose.fold.eq_1, hA, List.map_map]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply]
  exact ih

@[simp]
lemma isSupp_mk
    (A : Finset 𝔸) (x : X) (xs : List (Rose X))
    : IsSupp A (Rose.mk x xs) ↔ IsSupp A x ∧ IsSupp A xs := by
  apply Iff.intro
  · intro ⟨h⟩
    apply And.intro
    · constructor
      intro π hπ
      specialize h π hπ
      simp only [perm_def, Rose.map_eq, Rose.map_mk, Rose.mk.injEq] at h
      grind
    · constructor
      intro π hπ
      specialize h π hπ
      simp only [perm_def, Rose.map_eq, Rose.map_mk, Rose.mk.injEq, List.perm_def] at ⊢ h
      grind
  · intro ⟨⟨h₁⟩, ⟨h₂⟩⟩
    constructor
    intro π hπ
    specialize h₁ π hπ
    specialize h₂ π hπ
    simp_all only [List.perm_def, perm_def, Rose.map_eq, Rose.map_mk]

end PermAction.Rose
