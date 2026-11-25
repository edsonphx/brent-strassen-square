import Brent.TangentCertificate

/- Generated finite checks for the archived tangent frame. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem tangent0 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (0 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (0 + j.val)) = true) j

theorem tangent1 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (4 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (4 + j.val)) = true) j

theorem tangent2 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (8 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (8 + j.val)) = true) j

theorem tangent3 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (12 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (12 + j.val)) = true) j

theorem tangent4 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (16 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (16 + j.val)) = true) j

theorem tangent5 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (20 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (20 + j.val)) = true) j

theorem tangent6 (j : Fin 4) :
    checkFrame (Fin.ofNat 251 (24 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 4,
    checkFrame (Fin.ofNat 251 (24 + j.val)) = true) j

end Brent.TangentData
