import FinitelySupported.PermAction.Basic

namespace PermAction.Prop

variable {𝔸 X Y : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y]

instance : PermAction 𝔸 Prop := default

@[simp, fun_prop]
lemma isHom_ite
    {p : X → Prop} (hp : IsHom 𝔸 p) [DecidablePred p]
    {f : X → Y} (hf : IsHom 𝔸 f)
    {g : X → Y} (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ if p x then f x else g x) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨C, hC⟩ := hp
  use A ∪ B ∪ C
  intro π x hπ
  by_cases h : p x
  · simp (disch := grind) only [h, ↓reduceIte, ← hC, default_perm, ← hA]
  · simp (disch := grind) only [h, ↓reduceIte, ← hC, default_perm, ← hB]

end PermAction.Prop
