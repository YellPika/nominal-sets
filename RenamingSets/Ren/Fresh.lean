import RenamingSets.Ren.Basic

namespace RenamingSets.Ren

variable {𝔸 : Type*}

private def exists_fresh [Infinite 𝔸] (A B : Finset 𝔸)
    : ∃f : 𝔸 → 𝔸, Set.InjOn f A ∧ (∀a ∈ A, f a ∉ B) ∧ (∀a ∉ A, f a = a) := by
  classical
  induction A using Finset.induction generalizing B with
  | empty =>
    use id
    simp only [
      Finset.coe_empty, Set.injOn_empty, Finset.notMem_empty, id_eq,
      IsEmpty.forall_iff, implies_true, not_false_eq_true, and_self]
  | insert a s ha ih =>
    obtain ⟨b, hb⟩ := B.exists_notMem
    obtain ⟨f, hf₁, hf₂, hf₃⟩ := ih (B ∪ {b})
    use fun c ↦ if c = a then b else f c
    refine ⟨?_, ?_, ?_⟩
    · intro c hc d hd hcd
      wlog hca : c ≠ a
      · grind
      wlog hda : d ≠ a
      · grind
      apply hf₁ <;> grind
    · grind
    · grind

/--
`fresh A B` is a renaming which assigns a unique name for every `a ∈ A`, such
that `a ∉ B`. Names not in `A` are left alone (i.e. `a ∉ A → fresh A B a = a`).
-/
noncomputable def fresh [Infinite 𝔸] (A B : Finset 𝔸) : Ren 𝔸 where
  toFun := (exists_fresh A B).choose
  exists_support' := by
    use A
    exact (exists_fresh A B).choose_spec.2.2

@[simp, grind ←]
lemma fresh_injOn [Infinite 𝔸] (A B : Finset 𝔸) : Set.InjOn (fresh A B) A := by
  unfold fresh
  exact (exists_fresh A B).choose_spec.1

@[grind →]
lemma fresh_injOn'
    [Infinite 𝔸]
    {A B : Finset 𝔸} {a b} (ha : a ∈ A) (hb : b ∈ A)
    (h : fresh A B a = fresh A B b)
    : a = b := by
  apply fresh_injOn <;> assumption

lemma fresh_of_mem [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ A, fresh A B a ∉ B := by
  unfold fresh
  exact (exists_fresh A B).choose_spec.2.1

@[grind ←]
lemma fresh_of_mem' [Infinite 𝔸] (A B C : Finset 𝔸) : ∀a ∈ A, C ⊆ B → fresh A B a ∉ C := by
  have := fresh_of_mem A B
  grind

@[simp, grind =]
private lemma fresh_of_notMem [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∉ A, fresh A B a = a := by
  unfold fresh
  exact (exists_fresh A B).choose_spec.2.2

/-- The inverse renaming for `fresh`. -/
@[simps -isSimp]
noncomputable def unfresh [Infinite 𝔸] (A B : Finset 𝔸) : Ren 𝔸 where
  toFun a :=
    open Classical in
    if h : ∃b ∈ A, fresh A B b = a then h.choose else a
  exists_support' := by
    classical
    use A.image (fresh A B)
    grind

@[simp, grind =]
lemma unfresh_of_mem [Infinite 𝔸] (A B : Finset 𝔸) : ∀a ∈ B, unfresh A B a = a := by
  simp only [unfresh_coe, dite_eq_right_iff, forall_exists_index, forall_and_index]
  intro a ha b hb rfl
  have := fresh_of_mem A B
  grind

@[grind =]
lemma unfresh_of_not_fresh
    [Infinite 𝔸] (A B : Finset 𝔸)
    : ∀ a, (∀ b ∈ A, a ≠ fresh A B b) → unfresh A B a = a := by
  simp only [unfresh_coe]
  grind

@[simp, grind =]
lemma unfresh_fresh₁
    [Infinite 𝔸] (A B : Finset 𝔸)
    : ∀a ∈ A, unfresh A B (fresh A B a) = a := by
  intro a ha
  have : ∃ b ∈ A, (fresh A B) b = (fresh A B) a := by grind
  simp only [unfresh_coe, this, ↓reduceDIte]
  replace := this.choose_spec
  grind

@[simp, grind =]
lemma unfresh_fresh₂
    [Infinite 𝔸] (A B : Finset 𝔸)
    : ∀a ∈ B, unfresh A B (fresh A B a) = a := by
  intro a ha
  simp only [unfresh_coe]
  by_cases ha' : a ∈ A
  · have : ∃b ∈ A, fresh A B b = fresh A B a := by use a
    simp only [this, ↓reduceDIte]
    have := Classical.choose_spec this
    grind
  · grind

end RenamingSets.Ren
