import Brent.Generated.OriginBlocks.Block3

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch32 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (64 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (64 + r.val)) = true) r

theorem originBatch33 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (66 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (66 + r.val)) = true) r

theorem originBatch34 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (68 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (68 + r.val)) = true) r

theorem originBatch35 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (70 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (70 + r.val)) = true) r

theorem originBatch36 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (72 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (72 + r.val)) = true) r

theorem originBatch37 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (74 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (74 + r.val)) = true) r

theorem originBatch38 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (76 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (76 + r.val)) = true) r

theorem originBatch39 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (78 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (78 + r.val)) = true) r

end Brent.TangentData
