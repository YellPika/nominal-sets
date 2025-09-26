import FinitelySupported.PermAction.Prop

namespace PermAction.Bool

variable {𝔸 X : Type*} [PermAction 𝔸 X]

instance : PermAction 𝔸 Bool := default

@[fun_prop]
lemma isHom_eq
    {f g : X → Bool} (hf : IsHom 𝔸 f) (hg : IsHom 𝔸 g)
    : IsHom 𝔸 (fun x ↦ f x = g x) := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  use A ∪ B
  intro π x hπ
  specialize hA π x (by grind)
  specialize hB π x (by grind)
  simp only [default_perm] at hA hB
  simp only [default_perm, ← hA, ← hB]

end PermAction.Bool
