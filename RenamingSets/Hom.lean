import RenamingSets.Function

namespace RenamingSets

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

/-- Morphisms in the category of nominal renaming sets. -/
structure Hom (𝔸 X Y : Type*) [RenameAction 𝔸 X] [RenameAction 𝔸 Y] where
  /-- The underlying function. -/
  toFun : X → Y
  /--
  The function has a finite support. Do not use this directly except when
  elements of the `Hom` type. Prefer `isSupportedF` instead.
  -/
  isSupportedF' : IsSupportedF 𝔸 toFun := by fun_prop

namespace Hom

instance : FunLike (Hom 𝔸 X Y) X Y where
  coe := toFun
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simp only [mk.injEq] at ⊢ h
    rw [h]

/-- A simps projection for function application. -/
def Simps.coe (f : Hom 𝔸 X Y) : X → Y := f

initialize_simps_projections Hom (toFun → coe)

@[simp, local fun_prop]
lemma isSupportedF (f : Hom 𝔸 X Y) : IsSupportedF 𝔸 f :=
  f.isSupportedF'

@[simp]
lemma coe_mk (f : X → Y) (hf : IsSupportedF 𝔸 f) : mk (𝔸 := 𝔸) f = f := rfl

@[simp]
lemma mk_coe (f : Hom 𝔸 X Y) : mk f = f := rfl

@[ext]
lemma ext {f g : Hom 𝔸 X Y} (h : (f : X → Y) = g) : f = g := by
  rcases f
  rcases g
  simpa only [mk.injEq, coe_mk] using h

lemma ext'
    [Infinite 𝔸] [DecidableEq 𝔸] [RenamingSet 𝔸 X]
    {f g : Hom 𝔸 X Y} (A : Finset 𝔸)
    (hA : ∀ x, supp 𝔸 x ∩ A = ∅ → f x = g x)
    : f = g := by
  obtain ⟨B, hB⟩ := f.isSupportedF
  obtain ⟨C, hC⟩ := g.isSupportedF
  ext : 1
  apply Function.ext' (A ∪ B ∪ C)
  · grind
  · grind
  · intro x hx
    apply hA
    simp only [
      Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
      Finset.notMem_empty, iff_false, not_and, not_or] at ⊢ hx
    grind

variable [Infinite 𝔸] [RenamingSet 𝔸 X] [RenamingSet 𝔸 Y] [RenamingSet 𝔸 Z]

@[simps -isSimp]
noncomputable instance : RenameAction 𝔸 (Hom 𝔸 X Y) where
  rename σ f := mk (rename σ (f : X → Y))
  rename_one f := by simp only [rename_one', id_eq, mk_coe]
  rename_mul σ₁ σ₂ f := by simp only [coe_mk, rename_mul]

lemma isSupportOf_iff_coe
    (A : Finset 𝔸) (f : Hom 𝔸 X Y)
    : IsSupportOf A f ↔ IsSupportOf A (f : X → Y) := by
  simp only [isSupportOf_def, Hom.ext_iff, rename_coe, funext_iff]

instance : RenamingSet 𝔸 (Hom 𝔸 X Y) where
  isSupported f := by
    obtain ⟨A, hA⟩ := f.isSupportedF
    use A
    simp only [isSupportOf_iff_coe]
    apply Function.isSupportOf_of_isSupportOfF
    exact hA

@[simp]
lemma rename_apply
    (σ : Ren 𝔸) (f : Hom 𝔸 X Y) (x : X)
    : rename σ f (rename σ x) = rename σ (f x) := by
  simp only [rename_coe, isSupportedF, Function.rename_apply]

@[simp]
lemma isSupportOfF_supp (f : Hom 𝔸 X Y) : IsSupportOfF (supp 𝔸 f) f := by
  constructor
  intro σ hσ x
  rw [← rename_apply, rename_congr']
  exact hσ

lemma supp_min {A : Finset 𝔸} {f : Hom 𝔸 X Y} (hf : IsSupportOfF A f) : supp 𝔸 f ⊆ A := by
  intro a ha
  simp only [mem_supp] at ha
  apply ha
  simp only [isSupportOf_iff_coe, hf, Function.isSupportOf_of_isSupportOfF]

@[simp]
lemma isSupportOf_iff_isSupportOfF
    (A : Finset 𝔸) (f : Hom 𝔸 X Y)
    : IsSupportOf A f ↔ IsSupportOfF A f := by
  apply Iff.intro
  · intro hf
    apply isSupportOfF_mono f
    · apply RenamingSets.supp_min hf
    · simp only [isSupportOfF_supp]
  · intro hf
    apply isSupportOf_mono f (supp_min hf)
    simp only [isSupportOf_supp]

lemma supp_subset [DecidableEq 𝔸]
    (f : Hom 𝔸 X Y) (x : X)
    : supp 𝔸 (f x) ⊆ supp 𝔸 f ∪ supp 𝔸 x := by
  apply supp_apply
  simp only [isSupportOfF_supp]

@[simp]
lemma equivariant_coe : Equivariant 𝔸 (fun ((f, x) : Hom 𝔸 X Y × X) ↦ f x) := by
  simp only [
    equivariant_def, isSupportOfF_def, Finset.notMem_empty, IsEmpty.forall_iff,
    implies_true, Prod.forall, Prod.rename_mk, rename_apply]

@[simp]
lemma isSupportedF_apply : IsSupportedF 𝔸 (fun ((f, x) : Hom 𝔸 X Y × X) ↦ f x) := by
  apply isSupportedF_of_equivariant
  simp only [equivariant_coe]

omit [RenamingSet 𝔸 X] in
@[fun_prop, simp]
lemma equivariant_coe'
    {f : X → Hom 𝔸 Y Z} (hf : Equivariant 𝔸 f)
    {g : X → Y} (hg : Equivariant 𝔸 g)
    : Equivariant 𝔸 (fun x ↦ f x (g x)) := by
  have := equivariant_comp' (𝔸 := 𝔸)
    (f := fun ((f, x) : Hom 𝔸 Y Z × Y) ↦ f x)
    (g := fun x ↦ (f x, g x))
  simp only [equivariant_coe, forall_const] at this
  apply this
  fun_prop

omit [RenamingSet 𝔸 X] in
@[fun_prop, simp]
lemma isSupportedF''
    {f : X → Hom 𝔸 Y Z} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ f x (g x)) := by
  have := isSupportedF_comp' (𝔸 := 𝔸)
    (f := fun ((f, x) : Hom 𝔸 Y Z × Y) ↦ f x)
    (g := fun x ↦ (f x, g x))
  simp only [isSupportedF_apply, forall_const] at this
  apply this
  fun_prop

@[fun_prop]
lemma isSupportedF_mk
    (f : X → Y → Z) (hf : IsSupportedF 𝔸 fun (x, y) ↦ f x y)
    : IsSupportedF 𝔸 (fun x ↦ mk (f x)) := by
  classical
  obtain ⟨A, hA⟩ := hf
  use A
  simp only [isSupportOfF_def, Prod.forall, Prod.rename_mk] at ⊢ hA
  intro σ hσ x
  apply ext' (supp 𝔸 x ∪ A ∪ σ.supp)
  intro y hy
  have : rename σ y = y := by
    apply rename_congr'
    simp only [Finset.union_assoc, Finset.ext_iff, Finset.mem_inter, Finset.mem_union,
      Ren.mem_supp, ne_eq, Finset.notMem_empty, iff_false, not_and, not_or,
      Decidable.not_not] at hy
    grind
  rw [←this, rename_apply]
  simp only [coe_mk]
  apply hA hσ

/-- Currying for morphisms. -/
@[simps]
def curry (f : Hom 𝔸 (X × Y) Z) : Hom 𝔸 X (Hom 𝔸 Y Z) where
  toFun x := { toFun y := f (x, y) }

/-- The evaluation morphism. -/
@[simps]
def eval : Hom 𝔸 (Hom 𝔸 X Y × X) Y where
  toFun x := x.1 x.2

end Hom

end RenamingSets
