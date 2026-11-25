import Brent.Generated.AugmentedBlocks.Block5

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps48 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1536 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1536 + j.val)) = true) j

theorem augSteps49 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1568 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1568 + j.val)) = true) j

theorem augSteps50 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1600 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1600 + j.val)) = true) j

theorem augSteps51 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1632 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1632 + j.val)) = true) j

theorem augSteps52 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1664 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1664 + j.val)) = true) j

theorem augSteps53 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1696 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1696 + j.val)) = true) j

theorem augSteps54 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1728 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1728 + j.val)) = true) j

theorem augSteps55 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1760 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1760 + j.val)) = true) j

end Brent.AugmentedTrace
