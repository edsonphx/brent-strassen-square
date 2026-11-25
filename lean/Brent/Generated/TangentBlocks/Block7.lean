import Brent.Generated.TangentBlocks.Block6

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent49 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (196 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (196 + j.val)) = true) j

theorem tangent50 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (200 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (200 + j.val)) = true) j

theorem tangent51 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (204 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (204 + j.val)) = true) j

theorem tangent52 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (208 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (208 + j.val)) = true) j

theorem tangent53 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (212 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (212 + j.val)) = true) j

theorem tangent54 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (216 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (216 + j.val)) = true) j

theorem tangent55 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (220 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (220 + j.val)) = true) j

end Brent.TangentData
