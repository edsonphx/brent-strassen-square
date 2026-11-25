import Brent.Generated.OriginBlocks.Block7

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch64 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (128 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (128 + r.val)) = true) r

theorem originBatch65 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (130 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (130 + r.val)) = true) r

theorem originBatch66 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (132 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (132 + r.val)) = true) r

theorem originBatch67 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (134 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (134 + r.val)) = true) r

theorem originBatch68 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (136 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (136 + r.val)) = true) r

theorem originBatch69 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (138 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (138 + r.val)) = true) r

theorem originBatch70 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (140 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (140 + r.val)) = true) r

theorem originBatch71 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (142 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (142 + r.val)) = true) r

end Brent.TangentData
