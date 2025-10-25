import RenamingSets.Finset

namespace RenamingSets

/--
For any `RenameAction` type `X`, we can form a `RenamingSet` `Restrict 𝔸 X`
which is simply `X` restricted to those elements which have a finite support.
-/
@[ext]
structure Restrict (𝔸 X : Type*) [RenameAction 𝔸 X] where
  /-- The underlying element. -/
  val : X
  /-- The element has a finite support. -/
  isSupported_val : IsSupported 𝔸 val

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

namespace Restrict

attribute [coe] val
attribute [simp] isSupported_val

instance : CoeOut (Restrict 𝔸 X) X where
  coe := val

@[simps]
instance : RenameAction 𝔸 (Restrict 𝔸 X) where
  rename σ x := {
    val := rename σ x
    isSupported_val := by
      classical
      apply isSupported_rename
      exact x.isSupported_val
  }
  rename_one := by simp only [rename_one, implies_true]
  rename_mul := by simp only [rename_mul, implies_true]

@[simp]
lemma isSupportOf (A : Finset 𝔸) (x : Restrict 𝔸 X) : IsSupportOf A x ↔ IsSupportOf A x.val := by
  apply Iff.intro <;>
  · rintro ⟨h⟩
    constructor
    simp only [Restrict.ext_iff, rename_val] at ⊢ h
    exact h

instance : RenamingSet 𝔸 (Restrict 𝔸 X) where
  isSupported x := by
    obtain ⟨A, hA⟩ := x.isSupported_val
    use A
    simp only [isSupportOf, hA]

@[simp, fun_prop]
lemma isSupportedF_val : IsSupportedF 𝔸 (val : Restrict 𝔸 X → X) := by
  use ∅
  simp only [isSupportOfF_def, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, rename_val]

@[simp]
lemma isSupportedF_iff
    (f : X → Restrict 𝔸 Y)
    : IsSupportedF 𝔸 f ↔ IsSupportedF 𝔸 (fun x ↦ (f x).val) := by
  apply Iff.intro <;>
  · rintro ⟨A, hA⟩
    use A
    simp only [isSupportOfF_def, Restrict.ext_iff, rename_val] at ⊢ hA
    exact hA

@[fun_prop]
lemma isSupportedF_mk
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    (p : ∀ x, IsSupported 𝔸 (f x))
    : IsSupportedF 𝔸 fun x ↦ mk (f x) (p x) := by
  simp only [isSupportedF_iff, hf]

end Restrict

end RenamingSets
