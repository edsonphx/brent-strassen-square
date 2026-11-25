import Brent.Generated.AugmentedBlocks.Block3

/- Generated bounded-size batches for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem augSteps32 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1024 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1024 + j.val)) = true) j

theorem augSteps33 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1056 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1056 + j.val)) = true) j

theorem augSteps34 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1088 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1088 + j.val)) = true) j

theorem augSteps35 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1120 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1120 + j.val)) = true) j

theorem augSteps36 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1152 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1152 + j.val)) = true) j

theorem augSteps37 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1184 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1184 + j.val)) = true) j

theorem augSteps38 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1216 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1216 + j.val)) = true) j

theorem augSteps39 (j : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (1248 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 32,
    checkMixedStep (Fin.ofNat 2916 (1248 + j.val)) = true) j

end Brent.AugmentedTrace
