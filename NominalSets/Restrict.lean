import NominalSets.Function

namespace NominalSets

/--
For any `PermAction` type `X`, we can form a `Supported` type `Restrict 𝔸 X`
which is simply `X` restricted to those elements which have a finite support.
-/
@[ext]
structure Restrict (𝔸 X : Type*) [PermAction 𝔸 X] where
  /-- The underlying element. -/
  val : X
  /-- The element has a finite support. -/
  isSupported_val : IsSupported 𝔸 val

variable {𝔸 X Y Z : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

namespace Restrict

attribute [simp] isSupported_val

instance : CoeOut (Restrict 𝔸 X) X where
  coe := val

instance : CoeFun (Restrict 𝔸 (X → Y)) (fun _ ↦ X → Y) where
  coe := val

instance [CoeFun X (fun _ ↦ Y)] : CoeFun (Restrict 𝔸 X) (fun _ ↦ Y) where
  coe x := x.val

@[simps]
instance : PermAction 𝔸 (Restrict 𝔸 X) where
  perm π x := {
    val := perm π x
    isSupported_val := by simp only [isSupported_perm, isSupported_val]
  }
  perm_one := by simp only [perm_one, implies_true]
  perm_mul := by simp only [perm_mul, implies_true]

@[simp]
lemma isSupportOf (A : Finset 𝔸) (x : Restrict 𝔸 X) : IsSupportOf A x ↔ IsSupportOf A x.val := by
  apply Iff.intro <;>
  · rintro ⟨h⟩
    constructor
    simp only [Restrict.ext_iff, perm_val] at ⊢ h
    exact h

instance : Nominal 𝔸 (Restrict 𝔸 X) where
  supported x := by
    obtain ⟨A, hA⟩ := x.isSupported_val
    use A
    simp only [isSupportOf, hA]

@[simp, fun_prop]
lemma isSupportedF_val : IsSupportedF 𝔸 (val : Restrict 𝔸 X → X) := by
  use ∅
  intro π hπ x
  simp only [perm_val]

@[simp, fun_prop]
lemma isSupportedF_val' (f : Restrict 𝔸 (X → Y)) : IsSupportedF 𝔸 f.val := by
  have := isSupported_val f
  simp only [isSupported_iff_isSupportedF] at this
  exact this

@[simp]
lemma isSupportedF_iff
    (f : X → Restrict 𝔸 Y)
    : IsSupportedF 𝔸 f ↔ IsSupportedF 𝔸 (fun x ↦ (f x).val) := by
  apply Iff.intro <;>
  · rintro ⟨A, hA⟩
    use A
    simp_all only [Restrict.ext_iff, perm_val, implies_true]

@[fun_prop]
lemma isSupportedF_mk
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    (p : ∀ x, IsSupported 𝔸 (f x))
    : IsSupportedF 𝔸 fun x ↦ mk (f x) (p x) := by
  simp only [isSupportedF_iff, hf]

@[fun_prop]
lemma isSupportedF_eval
    {f : X → Restrict 𝔸 (Y → Z)} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ f x (g x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  intro π hπ x
  specialize hA π (by grind)
  specialize hB π (by grind)
  simp only [Restrict.ext_iff, perm_val, funext_iff, Function.perm_def] at hA
  specialize hA x (perm π (g x))
  simp only [perm_mul, inv_mul_cancel, perm_one] at hA
  simp only [hA, hB]

end Restrict

end NominalSets
