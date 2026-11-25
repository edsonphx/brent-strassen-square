import Brent.Generated.AugmentedBlocks.Block8

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps72 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2304 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2304 + j.val)) = true) j

theorem augSteps73 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2336 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2336 + j.val)) = true) j

theorem augSteps74 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2368 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2368 + j.val)) = true) j

theorem augSteps75 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2400 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2400 + j.val)) = true) j

theorem augSteps76 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2432 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2432 + j.val)) = true) j

theorem augSteps77 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2464 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2464 + j.val)) = true) j

theorem augSteps78 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2496 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2496 + j.val)) = true) j

theorem augSteps79 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2528 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2528 + j.val)) = true) j

end Brent.AugmentedTrace
