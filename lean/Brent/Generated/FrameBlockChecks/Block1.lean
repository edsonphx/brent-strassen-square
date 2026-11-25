import Brent.Generated.FrameBlockChecks.Block0

/- Generated finite checks for the correspondence of frozen tangent blocks. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem blockMatch6 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (18 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (18 + j.val)) = true) j

theorem blockMatch7 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (21 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (21 + j.val)) = true) j

theorem blockMatch8 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (24 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (24 + j.val)) = true) j

theorem blockMatch9 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (27 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (27 + j.val)) = true) j

theorem blockMatch10 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (30 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (30 + j.val)) = true) j

theorem blockMatch11 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (33 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (33 + j.val)) = true) j

end Brent.TangentData
