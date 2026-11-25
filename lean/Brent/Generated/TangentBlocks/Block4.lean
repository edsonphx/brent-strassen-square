import Brent.Generated.TangentBlocks.Block3

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent28 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (112 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (112 + j.val)) = true) j

theorem tangent29 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (116 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (116 + j.val)) = true) j

theorem tangent30 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (120 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (120 + j.val)) = true) j

theorem tangent31 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (124 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (124 + j.val)) = true) j

theorem tangent32 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (128 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (128 + j.val)) = true) j

theorem tangent33 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (132 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (132 + j.val)) = true) j

theorem tangent34 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (136 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (136 + j.val)) = true) j

end Brent.TangentData
