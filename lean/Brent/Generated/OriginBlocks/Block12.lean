import Brent.Generated.OriginBlocks.Block11

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch96 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (192 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (192 + r.val)) = true) r

theorem originBatch97 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (194 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (194 + r.val)) = true) r

theorem originBatch98 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (196 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (196 + r.val)) = true) r

theorem originBatch99 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (198 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (198 + r.val)) = true) r

theorem originBatch100 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (200 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (200 + r.val)) = true) r

theorem originBatch101 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (202 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (202 + r.val)) = true) r

theorem originBatch102 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (204 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (204 + r.val)) = true) r

theorem originBatch103 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (206 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (206 + r.val)) = true) r

end Brent.TangentData
