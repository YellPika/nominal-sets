import FinitelySupported.PermAction.Basic

namespace PermAction.Empty

variable {𝔸 : Type*}

instance : PermAction 𝔸 Empty := default

end PermAction.Empty

namespace PermAction.PEmpty

variable {𝔸 : Type*}

instance : PermAction 𝔸 PEmpty := default

end PermAction.PEmpty
