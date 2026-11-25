import Brent.Generated.OriginBlocks.Block9

/- Generated kernel replay of chart derivative certificates. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem originBatch80 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (160 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (160 + r.val)) = true) r

theorem originBatch81 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (162 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (162 + r.val)) = true) r

theorem originBatch82 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (164 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (164 + r.val)) = true) r

theorem originBatch83 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (166 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (166 + r.val)) = true) r

theorem originBatch84 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (168 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (168 + r.val)) = true) r

theorem originBatch85 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (170 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (170 + r.val)) = true) r

theorem originBatch86 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (172 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (172 + r.val)) = true) r

theorem originBatch87 (r : Fin 2) : checkOrigin (Fin.ofNat 251 (174 + r.val)) = true :=
  (by decide +kernel : ∀ r : Fin 2, checkOrigin (Fin.ofNat 251 (174 + r.val)) = true) r

end Brent.TangentData
