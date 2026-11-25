import Brent.Generated.AugmentedBlocks.Block4

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps40 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1280 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1280 + j.val)) = true) j

theorem augSteps41 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1312 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1312 + j.val)) = true) j

theorem augSteps42 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1344 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1344 + j.val)) = true) j

theorem augSteps43 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1376 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1376 + j.val)) = true) j

theorem augSteps44 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1408 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1408 + j.val)) = true) j

theorem augSteps45 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1440 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1440 + j.val)) = true) j

theorem augSteps46 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1472 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1472 + j.val)) = true) j

theorem augSteps47 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1504 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1504 + j.val)) = true) j

end Brent.AugmentedTrace
