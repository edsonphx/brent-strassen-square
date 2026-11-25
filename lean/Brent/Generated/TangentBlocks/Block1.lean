import Brent.Generated.TangentBlocks.Block0

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent7 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (28 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (28 + j.val)) = true) j

theorem tangent8 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (32 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (32 + j.val)) = true) j

theorem tangent9 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (36 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (36 + j.val)) = true) j

theorem tangent10 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (40 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (40 + j.val)) = true) j

theorem tangent11 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (44 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (44 + j.val)) = true) j

theorem tangent12 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (48 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (48 + j.val)) = true) j

theorem tangent13 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (52 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (52 + j.val)) = true) j

end Brent.TangentData
