import Brent.Generated.OriginBlocks.Block1

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch16 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (32 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (32 + r.val)) = true) r

theorem originBatch17 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (34 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (34 + r.val)) = true) r

theorem originBatch18 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (36 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (36 + r.val)) = true) r

theorem originBatch19 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (38 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (38 + r.val)) = true) r

theorem originBatch20 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (40 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (40 + r.val)) = true) r

theorem originBatch21 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (42 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (42 + r.val)) = true) r

theorem originBatch22 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (44 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (44 + r.val)) = true) r

theorem originBatch23 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (46 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (46 + r.val)) = true) r

end Brent.TangentData
