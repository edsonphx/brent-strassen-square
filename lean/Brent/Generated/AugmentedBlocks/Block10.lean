import Brent.Generated.AugmentedBlocks.Block9

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps80 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2560 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2560 + j.val)) = true) j

theorem augSteps81 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2592 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2592 + j.val)) = true) j

theorem augSteps82 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2624 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2624 + j.val)) = true) j

theorem augSteps83 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2656 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2656 + j.val)) = true) j

theorem augSteps84 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2688 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2688 + j.val)) = true) j

theorem augSteps85 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2720 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2720 + j.val)) = true) j

theorem augSteps86 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2752 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2752 + j.val)) = true) j

theorem augSteps87 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2784 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2784 + j.val)) = true) j

end Brent.AugmentedTrace
