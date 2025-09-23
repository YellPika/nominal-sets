import FinitelySupported.PermAction.Basic

namespace PermAction.Unit

variable {𝔸 : Type*}

instance : PermAction 𝔸 Unit := default

end PermAction.Unit

namespace PermAction.PUnit

variable {𝔸 : Type*}

instance : PermAction 𝔸 PUnit := default

end PermAction.PUnit
