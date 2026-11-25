import Brent.Generated.TangentBlocks.Block1

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent14 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (56 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (56 + j.val)) = true) j

theorem tangent15 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (60 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (60 + j.val)) = true) j

theorem tangent16 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (64 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (64 + j.val)) = true) j

theorem tangent17 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (68 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (68 + j.val)) = true) j

theorem tangent18 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (72 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (72 + j.val)) = true) j

theorem tangent19 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (76 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (76 + j.val)) = true) j

theorem tangent20 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (80 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (80 + j.val)) = true) j

end Brent.TangentData
