import RenamingSets.Ren.Defs

namespace RenamingSets

/-- A type with a (nominal) _renaming action_ is equipped with -/
class RenameAction (𝔸 X : Type*) where
  /-- 1. A _renaming operation_, such that -/
  rename : Ren 𝔸 → X → X
  /-- 2. applying the _identity renaming_ is the identity, and -/
  rename_one (x) : rename 1 x = x
  /-- 3. composition of renamings is equal to renaming by the composition. -/
  rename_mul (f g : Ren 𝔸) (x : X) : rename f (rename g x) = rename (f * g) x

export RenameAction (rename rename_one rename_mul)

attribute [simp] rename_mul

variable {𝔸 X Y Z : Type*} [RenameAction 𝔸 X] [RenameAction 𝔸 Y] [RenameAction 𝔸 Z]

@[simps]
instance : Inhabited (RenameAction 𝔸 X) where
  default := {
    rename _ x := x
    rename_one := by simp only [implies_true]
    rename_mul := by simp only [implies_true]
  }

@[simps]
instance (priority := default) : RenameAction 𝔸 𝔸 where
  rename σ := σ
  rename_one := by simp only [Ren.one_coe, implies_true]
  rename_mul := by simp only [Ren.mul_coe, implies_true]

end RenamingSets
