import Brent.LWH.Trace
import Brent.SparseTensor
import Mathlib.Tactic.FinCases

/- Generated: the 4096 integer Brent identities at the Li–Wang–Hu point, by the kernel. -/
namespace Brent.LWH

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Row-major numbering of matrix coordinates. -/
abbrev cn (n : Fin 16) : SquareVertex × SquareVertex := SparseTensor.coordinateNumber.symm n

theorem solvesRow0 : ∀ b c : Fin 16,
    pointDec.entry (cn 0) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 0) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow1 : ∀ b c : Fin 16,
    pointDec.entry (cn 1) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 1) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow2 : ∀ b c : Fin 16,
    pointDec.entry (cn 2) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 2) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow3 : ∀ b c : Fin 16,
    pointDec.entry (cn 3) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 3) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow4 : ∀ b c : Fin 16,
    pointDec.entry (cn 4) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 4) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow5 : ∀ b c : Fin 16,
    pointDec.entry (cn 5) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 5) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow6 : ∀ b c : Fin 16,
    pointDec.entry (cn 6) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 6) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow7 : ∀ b c : Fin 16,
    pointDec.entry (cn 7) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 7) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow8 : ∀ b c : Fin 16,
    pointDec.entry (cn 8) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 8) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow9 : ∀ b c : Fin 16,
    pointDec.entry (cn 9) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 9) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow10 : ∀ b c : Fin 16,
    pointDec.entry (cn 10) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 10) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow11 : ∀ b c : Fin 16,
    pointDec.entry (cn 11) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 11) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow12 : ∀ b c : Fin 16,
    pointDec.entry (cn 12) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 12) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow13 : ∀ b c : Fin 16,
    pointDec.entry (cn 13) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 13) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow14 : ∀ b c : Fin 16,
    pointDec.entry (cn 14) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 14) (cn b) (cn c) := by
  decide +kernel

theorem solvesRow15 : ∀ b c : Fin 16,
    pointDec.entry (cn 15) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn 15) (cn b) (cn c) := by
  decide +kernel

theorem solves_fin : ∀ a b c : Fin 16,
    pointDec.entry (cn a) (cn b) (cn c) = matrixMultiplicationEntry ℤ (cn a) (cn b) (cn c) := by
  intro a
  fin_cases a
  exacts [solvesRow0, solvesRow1, solvesRow2, solvesRow3, solvesRow4, solvesRow5, solvesRow6, solvesRow7, solvesRow8, solvesRow9, solvesRow10, solvesRow11, solvesRow12, solvesRow13, solvesRow14, solvesRow15]

/-- **The integer Brent identity holds at the Li–Wang–Hu point.** -/
theorem pointDec_solves : pointDec.Solves := by
  intro a b c
  have h := solves_fin (SparseTensor.coordinateNumber a) (SparseTensor.coordinateNumber b)
    (SparseTensor.coordinateNumber c)
  simpa only [cn, Equiv.symm_apply_apply] using h

end Brent.LWH
