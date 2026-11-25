import Brent.JacobianTrace
import Brent.RadixReplay

/- Generated bounded-size batches for the signed Jacobian trace. -/
namespace Brent.JacobianTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem steps0 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (0 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (0 + j.val)) = true) j

theorem steps1 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (8 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (8 + j.val)) = true) j

theorem steps2 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (16 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (16 + j.val)) = true) j

theorem steps3 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (24 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (24 + j.val)) = true) j

theorem steps4 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (32 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (32 + j.val)) = true) j

theorem steps5 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (40 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (40 + j.val)) = true) j

theorem steps6 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (48 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (48 + j.val)) = true) j

theorem steps7 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (56 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (56 + j.val)) = true) j

theorem steps8 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (64 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (64 + j.val)) = true) j

theorem steps9 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (72 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (72 + j.val)) = true) j

theorem steps10 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (80 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (80 + j.val)) = true) j

theorem steps11 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (88 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (88 + j.val)) = true) j

theorem steps12 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (96 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (96 + j.val)) = true) j

theorem steps13 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (104 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (104 + j.val)) = true) j

theorem steps14 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (112 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (112 + j.val)) = true) j

theorem steps15 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (120 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (120 + j.val)) = true) j

theorem steps16 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (128 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (128 + j.val)) = true) j

theorem steps17 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (136 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (136 + j.val)) = true) j

theorem steps18 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (144 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (144 + j.val)) = true) j

theorem steps19 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (152 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (152 + j.val)) = true) j

theorem steps20 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (160 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (160 + j.val)) = true) j

theorem steps21 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (168 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (168 + j.val)) = true) j

theorem steps22 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (176 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (176 + j.val)) = true) j

theorem steps23 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (184 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (184 + j.val)) = true) j

theorem steps24 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (192 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (192 + j.val)) = true) j

theorem steps25 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (200 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (200 + j.val)) = true) j

theorem steps26 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (208 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (208 + j.val)) = true) j

theorem steps27 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (216 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (216 + j.val)) = true) j

theorem steps28 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (224 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (224 + j.val)) = true) j

theorem steps29 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (232 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (232 + j.val)) = true) j

theorem steps30 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (240 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (240 + j.val)) = true) j

theorem steps31 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (248 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (248 + j.val)) = true) j

theorem steps32 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (256 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (256 + j.val)) = true) j

theorem steps33 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (264 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (264 + j.val)) = true) j

theorem steps34 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (272 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (272 + j.val)) = true) j

theorem steps35 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (280 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (280 + j.val)) = true) j

theorem steps36 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (288 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (288 + j.val)) = true) j

theorem steps37 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (296 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (296 + j.val)) = true) j

theorem steps38 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (304 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (304 + j.val)) = true) j

theorem steps39 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (312 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (312 + j.val)) = true) j

theorem steps40 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (320 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (320 + j.val)) = true) j

theorem steps41 (j : Fin 8) :
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (328 + j.val)) = true :=
  (by decide +kernel : ∀ j : Fin 8,
    SparseRow.checkRadixStep 4096 12 original reduced operations (Fin.ofNat 2352 (328 + j.val)) = true) j

end Brent.JacobianTrace
