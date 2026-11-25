import Brent.Generated.AugmentedBlocks.Block1

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps16 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (512 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (512 + j.val)) = true) j

theorem augSteps17 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (544 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (544 + j.val)) = true) j

theorem augSteps18 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (576 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (576 + j.val)) = true) j

theorem augSteps19 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (608 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (608 + j.val)) = true) j

theorem augSteps20 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (640 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (640 + j.val)) = true) j

theorem augSteps21 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (672 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (672 + j.val)) = true) j

theorem augSteps22 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (704 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (704 + j.val)) = true) j

theorem augSteps23 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (736 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (736 + j.val)) = true) j

end Brent.AugmentedTrace
