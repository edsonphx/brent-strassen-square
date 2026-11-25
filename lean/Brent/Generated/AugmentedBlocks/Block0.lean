import Brent.AugmentedTrace

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps0 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (0 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (0 + j.val)) = true) j

theorem augSteps1 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (32 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (32 + j.val)) = true) j

theorem augSteps2 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (64 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (64 + j.val)) = true) j

theorem augSteps3 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (96 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (96 + j.val)) = true) j

theorem augSteps4 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (128 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (128 + j.val)) = true) j

theorem augSteps5 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (160 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (160 + j.val)) = true) j

theorem augSteps6 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (192 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (192 + j.val)) = true) j

theorem augSteps7 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (224 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (224 + j.val)) = true) j

end Brent.AugmentedTrace
