import NominalSets.Prod

/-!
# Natural Numbers

This file formalizes definitions and results about permutations and supports for natural numbers.
-/

namespace NominalSets.Nat

variable {𝔸 X Y Z W : Type*} [PermAction 𝔸 X] [PermAction 𝔸 Y] [PermAction 𝔸 Z] [PermAction 𝔸 W]

/-!
## Permutations
-/

instance : PermAction 𝔸 ℕ := default

@[simp]
lemma perm_rec
    (π : Perm 𝔸) (z : X) (s : ℕ → X → X) (n : ℕ)
    : perm π (Nat.rec z s n : X) = Nat.rec (perm π z) (perm π s) n := by
  induction n generalizing π z s with
  | zero => rfl
  | succ n ih =>
    simp only [
      Function.perm_def, perm_discrete, ih,
      perm_mul, inv_mul_cancel, perm_one]

/-!
## Supports
-/

@[fun_prop]
lemma isSupportedF_rec
    (z : X → Y) (hz : IsSupportedF 𝔸 z)
    (s : X → ℕ → Y → Y) (hs : IsSupportedF 𝔸 fun (x, y, z) ↦ s x y z)
    (f : X → ℕ) (hf : IsSupportedF 𝔸 f)
    : IsSupportedF 𝔸 (fun x ↦ Nat.rec (z x) (s x) (f x) : X → Y) := by
  classical
  obtain ⟨A, hA⟩ := hz
  obtain ⟨B, hB⟩ := hs
  obtain ⟨C, hC⟩ := hf
  use A ∪ B ∪ C
  intro π hπ x
  replace hB : perm π (s x) = s (perm π x) := by
    ext n y
    simp only [perm_discrete, Prod.forall] at hB
    simp (disch := grind) only [
      Function.perm_def, perm_discrete, hB,
      perm_mul, mul_inv_cancel, perm_one]
  simp (disch := grind) only [perm_rec, hA, hB, ← hC, perm_discrete]

/-!
## Equivariance
-/

@[fun_prop]
lemma equivariant_rec
    (z : X → Y) (hz : Equivariant 𝔸 z)
    (s : X → ℕ → Y → Y) (hs : Equivariant 𝔸 fun (x, y, z) ↦ s x y z)
    (f : X → ℕ) (hf : Equivariant 𝔸 f)
    : Equivariant 𝔸 (fun x ↦ Nat.rec (z x) (s x) (f x) : X → Y) := by
  obtain ⟨hA⟩ := hz
  obtain ⟨hB⟩ := hs
  obtain ⟨hC⟩ := hf
  constructor
  intro π x
  replace hB : perm π (s x) = s (perm π x) := by
    ext n y
    simp only [perm_discrete, Prod.forall] at hB
    simp (disch := grind) only [
      Function.perm_def, perm_discrete, hB,
      perm_mul, mul_inv_cancel, perm_one]
  simp (disch := grind) only [perm_rec, hA, hB, ← hC, perm_discrete]

end NominalSets.Nat
