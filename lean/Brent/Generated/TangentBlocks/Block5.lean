import Brent.Generated.TangentBlocks.Block4

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent35 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (140 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (140 + j.val)) = true) j

theorem tangent36 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (144 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (144 + j.val)) = true) j

theorem tangent37 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (148 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (148 + j.val)) = true) j

theorem tangent38 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (152 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (152 + j.val)) = true) j

theorem tangent39 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (156 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (156 + j.val)) = true) j

theorem tangent40 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (160 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (160 + j.val)) = true) j

theorem tangent41 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (164 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (164 + j.val)) = true) j

end Brent.TangentData
