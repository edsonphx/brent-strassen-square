import Brent.Generated.AugmentedBlocks.Block10

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps88 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2816 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2816 + j.val)) = true) j

theorem augSteps89 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2848 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2848 + j.val)) = true) j

theorem augSteps90 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2880 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2880 + j.val)) = true) j

theorem augSteps91 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2912 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2912 + j.val)) = true) j

end Brent.AugmentedTrace
