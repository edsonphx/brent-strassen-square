import Brent.Differential
import Brent.SparseRow
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators

namespace Brent

private abbrev MatrixCoordinate := SquareVertex × SquareVertex

private def coordinateNumber : MatrixCoordinate ≃ Fin 16 :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

private def modeNumber : Mode ≃ Fin 3 where
  toFun m := match m with
    | .u => 0
    | .v => 1
    | .w => 2
  invFun i := ![Mode.u, Mode.v, Mode.w] i
  left_inv m := by cases m <;> rfl
  right_inv := by decide

/-- Appendix A.1's numbering, `48s + 16m + a`. -/
def squareVariableNumber : Variable SquareVertex SquareSummand ≃ Fin 2352 :=
  (Equiv.prodCongr finProdFinEquiv
    ((Equiv.prodCongr modeNumber coordinateNumber).trans finProdFinEquiv)).trans finProdFinEquiv

/-- Appendix A.1's numbering, `256a + 16b + c`. -/
def squareEquationNumber : EquationIndex SquareVertex ≃ Fin 4096 :=
  (Equiv.prodCongr coordinateNumber
    ((Equiv.prodCongr coordinateNumber coordinateNumber).trans finProdFinEquiv)).trans
      finProdFinEquiv

private def twoCoordinates : MatrixCoordinate × MatrixCoordinate ≃ Fin 256 :=
  (Equiv.prodCongr coordinateNumber coordinateNumber).trans finProdFinEquiv

private def sparseColumnBlock (place : MatrixCoordinate × MatrixCoordinate → EquationIndex SquareVertex)
    (value : MatrixCoordinate × MatrixCoordinate → ℤ) : SparseRow.Row :=
  SparseRow.ofIndexed fun i =>
    let x := twoCoordinates.symm i
    ((squareEquationNumber (place x)).val, value x)

private theorem coefficient_block
    (place : MatrixCoordinate × MatrixCoordinate → EquationIndex SquareVertex)
    (value : MatrixCoordinate × MatrixCoordinate → ℤ) (e : EquationIndex SquareVertex) :
    SparseRow.coefficient (squareEquationNumber e).val (sparseColumnBlock place value) =
      ∑ x, if place x = e then value x else 0 := by
  rw [sparseColumnBlock, SparseRow.coefficient_ofIndexed]
  simp only [Fin.val_inj, Equiv.apply_eq_iff_eq]
  exact twoCoordinates.symm.sum_comp (fun x => if place x = e then value x else 0)

/-- Sparse reconstruction of Jacobian columns directly from the signed recursive point. -/
def squareJacobianColumn (x : Variable SquareVertex SquareSummand) : SparseRow.Row :=
  let p := strassenSquareInt
  let (s, m, a) := x
  match m with
  | .u => sparseColumnBlock (fun (b, c) => (a, b, c)) (fun (b, c) => p.v s b * p.w s c)
  | .v => sparseColumnBlock (fun (b, c) => (b, a, c)) (fun (b, c) => p.u s b * p.w s c)
  | .w => sparseColumnBlock (fun (b, c) => (b, c, a)) (fun (b, c) => p.u s b * p.v s c)

theorem squareJacobianColumn_correct (x : Variable SquareVertex SquareSummand)
    (e : EquationIndex SquareVertex) :
    SparseRow.coefficient (squareEquationNumber e).val (squareJacobianColumn x) =
      strassenSquareInt.jacobianColumn x e.1 e.2.1 e.2.2 := by
  obtain ⟨s, m, x⟩ := x
  obtain ⟨a, b, c⟩ := e
  rw [Decomposition.jacobianColumn_eq]
  cases m <;>
    simp [squareJacobianColumn, coefficient_block, Fintype.sum_prod_type, Prod.mk.injEq,
      ite_and, and_left_comm]

/-- The actual Brent differential, in the ambient factor coordinates. -/
noncomputable def squareDifferential (k : Type*) [Field k] :
    (Variable SquareVertex SquareSummand → k) →ₗ[k] (EquationIndex SquareVertex → k) :=
  Matrix.mulVecLin (fun e x => (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2)

theorem square_nullity_of_rank (k : Type*) [Field k] (r : Nat)
    (rank : Module.finrank k (Submodule.span k (Set.range
      (fun x : Variable SquareVertex SquareSummand => fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) = r) :
    Module.finrank k (LinearMap.ker (squareDifferential k)) = 2352 - r := by
  have h := (squareDifferential k).finrank_range_add_finrank_ker
  unfold squareDifferential at h
  rw [Matrix.range_mulVecLin, Module.finrank_pi, square_variable_count] at h
  change Module.finrank k (Submodule.span k (Set.range
      (fun x : Variable SquareVertex SquareSummand => fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) +
    Module.finrank k (LinearMap.ker (squareDifferential k)) = 2352 at h
  omega

end Brent
