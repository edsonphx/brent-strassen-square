import Brent.Generated.FrameBlockChecks.Block1

/- Generated finite checks for the correspondence of frozen tangent blocks. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem blockMatch12 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (36 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (36 + j.val)) = true) j

theorem blockMatch13 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (39 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (39 + j.val)) = true) j

theorem blockMatch14 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (42 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (42 + j.val)) = true) j

theorem blockMatch15 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (45 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (45 + j.val)) = true) j

theorem blockMatch16 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (48 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (48 + j.val)) = true) j

theorem blockMatch17 (j : Fin 3) :
    checkBlock (Fin.ofNat 54 (51 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 3,
    checkBlock (Fin.ofNat 54 (51 + j.val)) = true) j

end Brent.TangentData
