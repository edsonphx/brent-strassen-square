import Brent.FamilyOrigin

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch0 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (0 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (0 + r.val)) = true) r

theorem originBatch1 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (2 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (2 + r.val)) = true) r

theorem originBatch2 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (4 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (4 + r.val)) = true) r

theorem originBatch3 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (6 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (6 + r.val)) = true) r

theorem originBatch4 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (8 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (8 + r.val)) = true) r

theorem originBatch5 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (10 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (10 + r.val)) = true) r

theorem originBatch6 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (12 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (12 + r.val)) = true) r

theorem originBatch7 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (14 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (14 + r.val)) = true) r

end Brent.TangentData
