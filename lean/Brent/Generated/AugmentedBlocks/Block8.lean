import Brent.Generated.AugmentedBlocks.Block7

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps64 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2048 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2048 + j.val)) = true) j

theorem augSteps65 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2080 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2080 + j.val)) = true) j

theorem augSteps66 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2112 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2112 + j.val)) = true) j

theorem augSteps67 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2144 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2144 + j.val)) = true) j

theorem augSteps68 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2176 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2176 + j.val)) = true) j

theorem augSteps69 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2208 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2208 + j.val)) = true) j

theorem augSteps70 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2240 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2240 + j.val)) = true) j

theorem augSteps71 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (2272 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (2272 + j.val)) = true) j

end Brent.AugmentedTrace
