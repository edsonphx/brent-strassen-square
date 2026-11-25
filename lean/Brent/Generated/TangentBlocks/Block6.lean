import Brent.Generated.TangentBlocks.Block5

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent42 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (168 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (168 + j.val)) = true) j

theorem tangent43 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (172 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (172 + j.val)) = true) j

theorem tangent44 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (176 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (176 + j.val)) = true) j

theorem tangent45 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (180 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (180 + j.val)) = true) j

theorem tangent46 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (184 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (184 + j.val)) = true) j

theorem tangent47 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (188 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (188 + j.val)) = true) j

theorem tangent48 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (192 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (192 + j.val)) = true) j

end Brent.TangentData
