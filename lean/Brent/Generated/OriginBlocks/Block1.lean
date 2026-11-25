import Brent.Generated.OriginBlocks.Block0

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch8 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (16 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (16 + r.val)) = true) r

theorem originBatch9 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (18 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (18 + r.val)) = true) r

theorem originBatch10 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (20 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (20 + r.val)) = true) r

theorem originBatch11 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (22 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (22 + r.val)) = true) r

theorem originBatch12 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (24 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (24 + r.val)) = true) r

theorem originBatch13 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (26 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (26 + r.val)) = true) r

theorem originBatch14 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (28 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (28 + r.val)) = true) r

theorem originBatch15 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (30 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (30 + r.val)) = true) r

end Brent.TangentData
