import RenamingSets.RenameAction.Defs
import RenamingSets.Ren.Basic

namespace RenamingSets

variable {𝔸 X : Type*} [RenameAction 𝔸 X]

@[simp]
lemma rename_one' : rename (1 : Ren 𝔸) = (id : X → X) := by
  ext a
  simp only [rename_one, id_eq]

end RenamingSets
