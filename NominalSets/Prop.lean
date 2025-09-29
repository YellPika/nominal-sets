import NominalSets.Prod

namespace NominalSets.Prop

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

instance : PermAction 𝔸 Prop := default

@[simp, fun_prop]
lemma isSupportedF_ite
    {p : X → Prop} (hp : IsSupportedF 𝔸 p) [DecidablePred p]
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ if p x then f x else g x) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨C, hC⟩ := hp
  use A ∪ B ∪ C
  intro π hπ x
  by_cases h : p x
  · simp (disch := grind) only [h, ↓reduceIte, ← hC, perm_discrete, ← hA]
  · simp (disch := grind) only [h, ↓reduceIte, ← hC, perm_discrete, ← hB]

@[fun_prop]
lemma isSupportedF_eq [DiscretePermAction 𝔸 Y]
    {f : X → Y} (hf : IsSupportedF 𝔸 f)
    {g : X → Y} (hg : IsSupportedF 𝔸 g)
    : IsSupportedF 𝔸 (fun x ↦ f x = g x) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  intro π hπ x
  simp only [perm_discrete] at hA hB
  simp (disch := grind) only [perm_discrete, ← hA, ← hB]

end NominalSets.Prop
