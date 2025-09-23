import FinitelySupported.PermAction.Basic

namespace PermAction.Prod

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

@[simps]
instance : PermAction 𝔸 (X × Y) where
  perm π x := (perm π x.1, perm π x.2)
  perm_one := by simp only [perm_one, Prod.mk.eta, implies_true]
  perm_mul := by simp only [perm_mul, implies_true]

@[simp]
lemma isHom_fst : IsHom 𝔸 (Prod.fst : X × Y → X) := by
  use ∅
  intro π ⟨x, y⟩
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, perm_def]

@[fun_prop]
lemma isHom_fst' {f : X → Y × Z} (hf : IsHom 𝔸 f) : IsHom 𝔸 (fun x ↦ (f x).1) :=
  isHom_comp' isHom_fst hf

@[simp]
lemma isHom_snd : IsHom 𝔸 (Prod.snd : X × Y → Y) := by
  use ∅
  intro π ⟨x, y⟩
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, perm_def]

@[fun_prop]
lemma isHom_snd' {f : X → Y × Z} (hf : IsHom 𝔸 f) : IsHom 𝔸 (fun x ↦ (f x).2) :=
  isHom_comp' isHom_snd hf

@[fun_prop]
lemma isHom_mk
    {f : X → Y} (hf : IsHom 𝔸 f)
    {g : X → Z} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ (f x, g x)) := by
  classical
  rcases hf with ⟨A, hA⟩
  rcases hg with ⟨B, hB⟩
  use A ∪ B
  intros
  simp (disch := grind) only [perm_def, hA, hB]

@[simp]
lemma isHom_iff
    (f : X → Y × Z)
    : IsHom 𝔸 f ↔ IsHom 𝔸 (fun x ↦ (f x).1) ∧ IsHom 𝔸 (fun x ↦ (f x).2) := by
  apply Iff.intro
  · intro
    apply And.intro <;> fun_prop
  · rintro ⟨_, _⟩
    apply isHom_mk <;> fun_prop

@[simp]
lemma isSupp_iff (A : Finset 𝔸) (x : X × Y) : IsSupp A x ↔ IsSupp A x.1 ∧ IsSupp A x.2 := by
  apply Iff.intro
  · intro ⟨hπ⟩
    simp only [perm_def] at hπ
    apply And.intro <;>
    · constructor
      grind
  · intro ⟨⟨h₁⟩, ⟨h₂⟩⟩
    constructor
    cases x
    simp only [perm_def, Prod.mk.injEq] at ⊢ h₁ h₂
    grind

end PermAction.Prod
