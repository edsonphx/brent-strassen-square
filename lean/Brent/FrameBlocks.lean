import Brent.TangentCertificate
import Brent.QuadraticMixed

open scoped BigOperators

namespace Brent.TangentData

private def modeEquiv : Mode ≃ Fin 3 where
  toFun
    | .u => 0
    | .v => 1
    | .w => 2
  invFun a := ![Mode.u, Mode.v, Mode.w] a
  left_inv m := by cases m <;> rfl
  right_inv := by decide

private abbrev Slot := Fin 7 × Mode × SparseTensor.Coordinate

private def slotNumber : Slot ≃ Fin 336 :=
  (Equiv.prodCongr (Equiv.refl (Fin 7))
    (((Equiv.prodCongr modeEquiv SparseTensor.coordinateNumber).trans finProdFinEquiv))).trans
      finProdFinEquiv

private def xWalk (i : Fin 54) (n : Fin 336) : Variable SquareVertex SquareSummand :=
  let a := slotNumber.symm n
  ((QuadraticData.xBlock i, a.1), a.2)

private def yWalk (i : Fin 54) (n : Fin 336) : Variable SquareVertex SquareSummand :=
  let a := slotNumber.symm n
  ((a.1, QuadraticData.yBlock i), a.2)

private def supportRow (d : Decomposition Int SquareVertex SquareSummand)
    (walk : Fin 336 → Variable SquareVertex SquareSummand) : SparseRow.Row :=
  SparseRow.ofIndexed fun n => ((squareVariableNumber (walk n)).val, d.coordinates (walk n))

private theorem supportRow_correct (d : Decomposition Int SquareVertex SquareSummand)
    (walk : Fin 336 → Variable SquareVertex SquareSummand) (inj : Function.Injective walk)
    (covered : ∀ x ∉ Set.range walk, d.coordinates x = 0) (x : Variable SquareVertex SquareSummand) :
    SparseRow.coefficient (squareVariableNumber x).val (supportRow d walk) = d.coordinates x := by
  rw [supportRow, SparseRow.coefficient_ofIndexed]
  simp only [Fin.val_inj, Equiv.apply_eq_iff_eq]
  by_cases h : x ∈ Set.range walk
  · obtain ⟨j, rfl⟩ := h
    simp [inj.eq_iff]
  · have none (j : Fin 336) : walk j ≠ x := fun eq => h ⟨j, eq⟩
    simp [none, covered x h]

private theorem xWalk_inj (i : Fin 54) : Function.Injective (xWalk i) := by
  intro a b h
  apply slotNumber.symm.injective
  exact Prod.ext (congrArg (fun x : Variable SquareVertex SquareSummand => x.1.2) h)
    (congrArg (fun x : Variable SquareVertex SquareSummand => x.2) h)

private theorem yWalk_inj (i : Fin 54) : Function.Injective (yWalk i) := by
  intro a b h
  apply slotNumber.symm.injective
  exact Prod.ext (congrArg (fun x : Variable SquareVertex SquareSummand => x.1.1) h)
    (congrArg (fun x : Variable SquareVertex SquareSummand => x.2) h)

private theorem xWalk_covers (i : Fin 54) :
    ∀ x ∉ Set.range (xWalk i), (QuadraticData.xDirection i).coordinates x = 0 := by
  rintro ⟨⟨a, b⟩, m, c⟩ hx
  have h : a ≠ QuadraticData.xBlock i := by
    rintro rfl
    exact hx ⟨slotNumber (b, m, c), by simp [xWalk]⟩
  cases m <;> (change (if a = QuadraticData.xBlock i then _ else 0) = 0; rw [if_neg h])

private theorem yWalk_covers (i : Fin 54) :
    ∀ x ∉ Set.range (yWalk i), (QuadraticData.yDirection i).coordinates x = 0 := by
  rintro ⟨⟨a, b⟩, m, c⟩ hx
  have h : b ≠ QuadraticData.yBlock i := by
    rintro rfl
    exact hx ⟨slotNumber (a, m, c), by simp [yWalk]⟩
  cases m <;> (change (if b = QuadraticData.yBlock i then _ else 0) = 0; rw [if_neg h])

def xFrameIndex (i : Fin 54) : Fin 251 := ⟨143 + i.val, by have := i.isLt; omega⟩
def yFrameIndex (i : Fin 54) : Fin 251 := ⟨197 + i.val, by have := i.isLt; omega⟩

def checkBlock (i : Fin 54) : Bool :=
  decide (supportRow (QuadraticData.xDirection i) (xWalk i) = frame (xFrameIndex i)) &&
  decide (supportRow (QuadraticData.yDirection i) (yWalk i) = frame (yFrameIndex i))

/-- The left directions used in the mixed certificate are literally part of the verified frame. -/
theorem xFrame_coordinates_of_check (i : Fin 54) (h : checkBlock i = true) (x : Variable SquareVertex SquareSummand) :
    SparseRow.coefficient (squareVariableNumber x).val (frame (xFrameIndex i)) =
      (QuadraticData.xDirection i).coordinates x := by
  simp only [checkBlock, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← h.1]
  exact supportRow_correct _ _ (xWalk_inj i) (xWalk_covers i) x

/-- The right directions used in the mixed certificate are literally part of the verified frame. -/
theorem yFrame_coordinates_of_check (i : Fin 54) (h : checkBlock i = true) (x : Variable SquareVertex SquareSummand) :
    SparseRow.coefficient (squareVariableNumber x).val (frame (yFrameIndex i)) =
      (QuadraticData.yDirection i).coordinates x := by
  simp only [checkBlock, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← h.2]
  exact supportRow_correct _ _ (yWalk_inj i) (yWalk_covers i) x

end Brent.TangentData
