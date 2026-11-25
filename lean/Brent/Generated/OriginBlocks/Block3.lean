import Brent.Generated.OriginBlocks.Block2

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch24 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (48 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (48 + r.val)) = true) r

theorem originBatch25 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (50 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (50 + r.val)) = true) r

theorem originBatch26 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (52 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (52 + r.val)) = true) r

theorem originBatch27 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (54 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (54 + r.val)) = true) r

theorem originBatch28 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (56 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (56 + r.val)) = true) r

theorem originBatch29 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (58 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (58 + r.val)) = true) r

theorem originBatch30 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (60 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (60 + r.val)) = true) r

theorem originBatch31 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (62 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (62 + r.val)) = true) r

end Brent.TangentData
