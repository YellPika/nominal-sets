import FinitelySupported.Supported.Prod
import FinitelySupported.PermAction.Function

open PermAction

namespace Supported.Function

variable {𝔸 X Y Z} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z]

@[fun_prop, simp]
lemma isHom_val (f : FS 𝔸 (X → Y)) : IsHom 𝔸 f := by
  rcases f.property with ⟨A, ⟨hA⟩⟩
  use A
  intro π x hπ
  specialize hA π⁻¹
  simp only [Perm.inv_toFun, funext_iff, Function.perm_def, inv_inv] at hA
  rw [←hA]
  · simp only [perm_mul, mul_inv_cancel, perm_one]
  · intro a ha
    nth_rw 1 [← hπ a ha]
    simp only [Perm.left_inverse]

/-- Currying for finitely-supported functions. -/
@[simps]
def curry [Supported 𝔸 X] (f : FS 𝔸 (X × Y → Z)) : FS 𝔸 (X → FS 𝔸 (Y → Z)) where
  val x := {
    val y := f (x, y)
    property := by
      apply Function.exists_isSupp_of_isHom
      fun_prop
  }
  property := by
    apply Function.exists_isSupp_of_isHom
    fun_prop

@[local fun_prop, simp]
lemma isHom_eval₀ : IsHom 𝔸 (fun p : FS 𝔸 (X → Y) × X => p.1 p.2) := by
  use ∅
  intro π x hπ
  simp only [Prod.perm_def, FS.perm_val, Function.perm_def, perm_mul, inv_mul_cancel, perm_one]

@[fun_prop]
lemma isHom_eval
    {f : X → FS 𝔸 (Y → Z)} (hf : IsHom 𝔸 f)
    {g : X → Y} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ f x (g x)) := by
  fun_prop

/-- Uncurrying for finitely-supported functions. -/
@[simps]
def eval : FS 𝔸 (FS 𝔸 (X → Y) × X → Y) where
  val x := x.1 x.2
  property := by
    apply Function.exists_isSupp_of_isHom
    fun_prop

@[simp]
lemma supp_eval [Supported 𝔸 X] [Supported 𝔸 Y] : supp 𝔸 (eval (𝔸 := 𝔸) (X := X) (Y := Y)) = ∅ := by
  have : IsSupp (∅ : Finset 𝔸) (eval (𝔸 := 𝔸) (X := X) (Y := Y)) := by
    constructor
    intro π hπ
    ext ⟨f, x⟩
    simp only [
      FS.perm_val, Function.perm_def, Prod.perm_def, eval_val,
      inv_inv, perm_mul, mul_inv_cancel, perm_one]
  have := supp_min _ this
  simp_all only [Finset.subset_empty]

lemma isSupp_apply
    {A : Finset 𝔸} {f : FS 𝔸 (X → Y)} {x : X}
    (hf : IsSupp A f) (hx : IsSupp A x)
    : IsSupp A (f x) := by
  constructor
  intro π hπ
  simp only at hπ
  have hf := hf.eq π (by grind)
  simp only [FS.ext_iff, FS.perm_val] at hf
  replace hf := congr_fun hf (perm π x)
  simp only [Function.perm_def, perm_mul, inv_mul_cancel, perm_one] at hf
  rw [hf, hx.eq π (by grind)]

@[simp]
lemma isHom_iff (f : X → FS 𝔸 (Y → Z)) : IsHom 𝔸 f ↔ IsHom 𝔸 (fun x : X × Y ↦ f x.1 x.2) := by
  apply Iff.intro
  · intro hf
    fun_prop
  · intro hf
    apply FS.isHom_mk
    fun_prop

end Supported.Function
