import Brent.Generated.TangentBlocks.Block7

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent56 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (224 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (224 + j.val)) = true) j

theorem tangent57 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (228 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (228 + j.val)) = true) j

theorem tangent58 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (232 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (232 + j.val)) = true) j

theorem tangent59 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (236 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (236 + j.val)) = true) j

theorem tangent60 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (240 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (240 + j.val)) = true) j

theorem tangent61 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (244 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (244 + j.val)) = true) j

theorem tangent62 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (248 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (248 + j.val)) = true) j

end Brent.TangentData
