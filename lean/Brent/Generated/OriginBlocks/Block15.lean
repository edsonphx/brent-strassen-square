import Brent.Generated.OriginBlocks.Block14

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch120 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (240 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (240 + r.val)) = true) r

theorem originBatch121 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (242 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (242 + r.val)) = true) r

theorem originBatch122 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (244 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (244 + r.val)) = true) r

theorem originBatch123 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (246 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (246 + r.val)) = true) r

theorem originBatch124 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (248 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (248 + r.val)) = true) r

theorem originBatch125 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (250 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (250 + r.val)) = true) r

end Brent.TangentData
