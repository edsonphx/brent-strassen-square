import Brent.Generated.AugmentedBlocks.Block19

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augCover160 (j : Fin 32) :
    checkCoverAt (Fin.ofNat 5268 (5120 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkCoverAt (Fin.ofNat 5268 (5120 + j.val)) = true) j

theorem augCover161 (j : Fin 32) :
    checkCoverAt (Fin.ofNat 5268 (5152 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkCoverAt (Fin.ofNat 5268 (5152 + j.val)) = true) j

theorem augCover162 (j : Fin 32) :
    checkCoverAt (Fin.ofNat 5268 (5184 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkCoverAt (Fin.ofNat 5268 (5184 + j.val)) = true) j

theorem augCover163 (j : Fin 32) :
    checkCoverAt (Fin.ofNat 5268 (5216 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkCoverAt (Fin.ofNat 5268 (5216 + j.val)) = true) j

theorem augCover164 (j : Fin 32) :
    checkCoverAt (Fin.ofNat 5268 (5248 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkCoverAt (Fin.ofNat 5268 (5248 + j.val)) = true) j

end Brent.AugmentedTrace
