import Brent.FrameBlocks

/- Generated finite checks for the correspondence of frozen tangent blocks. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem blockMatch0 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (0 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (0 + j.val)) = true) j

theorem blockMatch1 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (3 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (3 + j.val)) = true) j

theorem blockMatch2 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (6 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (6 + j.val)) = true) j

theorem blockMatch3 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (9 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (9 + j.val)) = true) j

theorem blockMatch4 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (12 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (12 + j.val)) = true) j

theorem blockMatch5 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (15 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (15 + j.val)) = true) j

end Brent.TangentData
