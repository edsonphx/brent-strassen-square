import Brent.Generated.TangentBlocks.Block2

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent21 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (84 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (84 + j.val)) = true) j

theorem tangent22 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (88 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (88 + j.val)) = true) j

theorem tangent23 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (92 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (92 + j.val)) = true) j

theorem tangent24 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (96 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (96 + j.val)) = true) j

theorem tangent25 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (100 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (100 + j.val)) = true) j

theorem tangent26 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (104 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (104 + j.val)) = true) j

theorem tangent27 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (108 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (108 + j.val)) = true) j

end Brent.TangentData
