import Brent.Generated.AugmentedBlocks.Block2

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps24 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (768 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (768 + j.val)) = true) j

theorem augSteps25 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (800 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (800 + j.val)) = true) j

theorem augSteps26 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (832 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (832 + j.val)) = true) j

theorem augSteps27 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (864 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (864 + j.val)) = true) j

theorem augSteps28 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (896 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (896 + j.val)) = true) j

theorem augSteps29 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (928 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (928 + j.val)) = true) j

theorem augSteps30 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (960 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (960 + j.val)) = true) j

theorem augSteps31 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (992 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (992 + j.val)) = true) j

end Brent.AugmentedTrace
