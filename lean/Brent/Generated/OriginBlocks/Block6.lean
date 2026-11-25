import Brent.Generated.OriginBlocks.Block5

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch48 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (96 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (96 + r.val)) = true) r

theorem originBatch49 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (98 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (98 + r.val)) = true) r

theorem originBatch50 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (100 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (100 + r.val)) = true) r

theorem originBatch51 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (102 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (102 + r.val)) = true) r

theorem originBatch52 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (104 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (104 + r.val)) = true) r

theorem originBatch53 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (106 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (106 + r.val)) = true) r

theorem originBatch54 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (108 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (108 + r.val)) = true) r

theorem originBatch55 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (110 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (110 + r.val)) = true) r

end Brent.TangentData
