import Brent.Generated.AugmentedBlocks.Block0

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps8 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (256 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (256 + j.val)) = true) j

theorem augSteps9 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (288 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (288 + j.val)) = true) j

theorem augSteps10 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (320 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (320 + j.val)) = true) j

theorem augSteps11 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (352 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (352 + j.val)) = true) j

theorem augSteps12 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (384 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (384 + j.val)) = true) j

theorem augSteps13 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (416 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (416 + j.val)) = true) j

theorem augSteps14 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (448 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (448 + j.val)) = true) j

theorem augSteps15 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (480 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (480 + j.val)) = true) j

end Brent.AugmentedTrace
