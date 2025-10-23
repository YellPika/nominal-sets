import RenamingSets.RenameAction.Defs
import RenamingSets.Ren.Basic

namespace RenamingSets

variable {𝔸 X : Type*} [RenameAction 𝔸 X]

@[simp]
lemma rename_one' : rename (1 : Ren 𝔸) = (id : X → X) := by
  ext a
  simp only [rename_one, id_eq]

@[simp]
lemma rename_discrete' [DiscreteRenameAction 𝔸 X] (σ : Ren 𝔸) : rename σ = (id : X → X) := by
  ext
  apply rename_discrete

instance : DiscreteRenameAction[(default : RenameAction 𝔸 X)] := by
  let : RenameAction 𝔸 X := default
  constructor
  simp only [RenameAction.default_rename, implies_true]

end RenamingSets
