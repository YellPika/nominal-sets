import RenamingSets.Finset
import Mathlib.Data.Part

namespace RenamingSets

variable {𝔸 X Y : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y]

/-- Morphisms in the category of nominal renaming sets. -/
structure Hom (𝔸 X Y : Type*) [RenameAction 𝔸 X] [RenameAction 𝔸 Y] where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The function has a nominal support. -/
  exists_support : ∃ A : Finset 𝔸,
    ∀ σ, (∀a ∈ A, σ a = a) →
    ∀ x, rename σ (toFun x) = toFun (rename σ x)

namespace Hom

instance : FunLike (Hom 𝔸 X Y) X Y where
  coe := toFun
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simp only [mk.injEq] at ⊢ h
    rw [h]

@[ext]
lemma ext {f g : Hom 𝔸 X Y} (h : ∀ x, f x = g x) : f = g := by
  rcases f
  rcases g
  simp only [DFunLike.coe, mk.injEq] at ⊢ h
  ext x
  apply h

private lemma exists_fresh_inj
    [Infinite 𝔸] (A : Finset 𝔸) (B : Finset 𝔸)
    : ∃f : 𝔸 → 𝔸, Set.InjOn f A ∧ (∀a ∈ A, f a ∉ B) ∧ (∀a ∉ A, f a = a) := by
  classical
  induction A using Finset.induction with
  | empty =>
    use fun a ↦ a
    simp only [
      Finset.coe_empty, Set.injOn_empty, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, not_false_eq_true, and_self]
  | insert a s ha ih =>
    obtain ⟨f, hf₁, hf₂, hf₃⟩ := ih
    obtain ⟨b, hb⟩ := (B ∪ s.image f).exists_notMem
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hb
    use fun c ↦ if c = a then b else f c
    refine ⟨?_, ?_, ?_⟩
    · intro c₁ hc₁ c₂ hc₂ hc
      simp only at hc
      wlog hc₁a : c₁ ≠ a
      · grind
      wlog hc₂a : c₂ ≠ a
      · grind
      apply hf₁ <;> grind
    · grind
    · grind

private noncomputable def fresh [Infinite 𝔸] (A B : Finset 𝔸) : Ren 𝔸 where
  toFun := (exists_fresh_inj A B).choose
  exists_support' := by
    use A
    have := Classical.choose_spec (exists_fresh_inj A B)
    exact this.2.2

private lemma fresh_inj [Infinite 𝔸] (A B : Finset 𝔸) : Set.InjOn (fresh A B) A := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  exact this.1

private lemma fresh_fresh [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ A, fresh A B a ∉ B := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  exact this.2.1

@[simp]
private lemma fresh_id [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∉ A, fresh A B a = a := by
  unfold fresh
  have := Classical.choose_spec (exists_fresh_inj A B)
  exact this.2.2

@[simps -isSimp]
private noncomputable def unfresh [Infinite 𝔸] (A B : Finset 𝔸) : Ren 𝔸 where
  toFun a :=
    open Classical in
    if h : ∃b ∈ A, fresh A B b = a then Classical.choose h else a
  exists_support' := by
    classical
    use A.image (fresh A B)
    grind

@[simp]
lemma unfresh_id [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ B, unfresh A B a = a := by
  simp only [unfresh_coe, dite_eq_right_iff, forall_exists_index, forall_and_index]
  intro a ha b hb rfl
  have := fresh_fresh A B
  grind

@[simp]
lemma unfresh_fresh₁ [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ A, unfresh A B (fresh A B a) = a := by
  intro a ha
  have : ∃ b ∈ A, (fresh A B) b = (fresh A B) a := by grind
  simp only [unfresh_coe, this, ↓reduceDIte]
  exact fresh_inj A B this.choose_spec.1 ha this.choose_spec.2

@[simp]
lemma unfresh_fresh₂ [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ B, unfresh A B (fresh A B a) = a := by
  intro a ha
  simp only [unfresh_coe]
  by_cases ha' : a ∈ A
  · have : ∃b ∈ A, fresh A B b = fresh A B a := by use a
    simp only [this, ↓reduceDIte]
    have := Classical.choose_spec this
    apply fresh_inj A B this.1 ha' this.2
  · simp only [
      ha', not_false_eq_true, fresh_id, dite_eq_right_iff,
      forall_exists_index, forall_and_index]
    intro b hb rfl
    have := fresh_fresh A B b hb
    contradiction

lemma ext_of_finset
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X]
    (f g : Hom 𝔸 X Y) (A : Finset 𝔸)
    (hA : ∀ x, supp 𝔸 x ∩ A = ∅ → f x = g x)
    : f = g := by
  classical
  rcases f with ⟨f, Cf, hCf⟩
  rcases g with ⟨g, Cg, hCg⟩
  simp only [DFunLike.coe, mk.injEq] at ⊢ hA
  ext x

  let τ := fresh (supp 𝔸 x ∩ A) (supp 𝔸 x ∪ A ∪ Cf ∪ Cg)
  let τ' := unfresh (supp 𝔸 x ∩ A) (supp 𝔸 x ∪ A ∪ Cf ∪ Cg)

  have : x = rename τ' (rename τ x) := by
    simp only [rename_mul]
    nth_rw 1 [←rename_one (𝔸 := 𝔸) x]
    apply rename_congr
    intro a ha
    simp (disch := grind) only [Ren.one_coe, Finset.union_assoc, Ren.mul_coe, unfresh_fresh₂, τ', τ]

  have : f (rename τ x) = g (rename τ x) := by
    apply hA
    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha₁ ha₂
    have := supp_rename_subset τ x ha₁
    simp only [Finset.mem_rename, rename_def, τ] at this
    rcases this with ⟨b, hb, rfl⟩
    by_cases hb' : b ∈ A
    · have := fresh_fresh (supp 𝔸 x ∩ A) (supp 𝔸 x ∪ A ∪ Cf ∪ Cg) b (by grind)
      grind
    · rw [fresh_id] at ha₁ ha₂ <;> grind

  have : f (rename τ' (rename τ x)) = rename τ' (f (rename τ x)) := by
    rw [←hCf]
    simp +contextual (disch := grind) [Finset.union_assoc, unfresh_id, implies_true, τ']

  have : g (rename τ' (rename τ x)) = rename τ' (g (rename τ x)) := by
    rw [←hCg]
    simp +contextual (disch := grind) [Finset.union_assoc, unfresh_id, implies_true, τ']

  grind

end Hom

end RenamingSets
