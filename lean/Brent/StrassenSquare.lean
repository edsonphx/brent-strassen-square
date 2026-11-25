import Brent.Tensor
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic

namespace Brent

private def strassenU : Fin 7 → Fin 4 → ℤ :=
  ![![1, 0, 0, 1], ![0, 0, 1, 1], ![1, 0, 0, 0], ![0, 0, 0, 1],
    ![1, 1, 0, 0], ![-1, 0, 1, 0], ![0, 1, 0, -1]]

private def strassenV : Fin 7 → Fin 4 → ℤ :=
  ![![1, 0, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, -1], ![-1, 0, 1, 0],
    ![0, 0, 0, 1], ![1, 1, 0, 0], ![0, 0, 1, 1]]

private def strassenW : Fin 7 → Fin 4 → ℤ :=
  ![![1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, 1], ![1, 0, 1, 0],
    ![-1, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0]]

/-- The signed Strassen table in §2, including output-factor order. -/
def strassen : Decomposition ℤ (Fin 2) (Fin 7) where
  u s a := strassenU s (finProdFinEquiv a)
  v s a := strassenV s (finProdFinEquiv a)
  w s a := strassenW s (finProdFinEquiv a)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- All 64 scalar Strassen identities over the integers, evaluated by the kernel. -/
theorem strassen_solves : strassen.Solves := by
  change ∀ a b c : Fin 2 × Fin 2, strassen.entry a b c = matrixMultiplicationEntry ℤ a b c
  decide

abbrev SquareVertex := Fin 2 × Fin 2
abbrev SquareSummand := Fin 7 × Fin 7

/-- The integral recursive point. The product indices flatten lexicographically to
four vertices and 49 summands by `finProdFinEquiv`. -/
def strassenSquareInt : Decomposition ℤ SquareVertex SquareSummand :=
  strassen.recursiveLeft (fun _ => strassen)

theorem strassenSquareInt_solves : strassenSquareInt.Solves :=
  Decomposition.solves_recursiveLeft strassen_solves (fun _ => strassen_solves)

def strassenSquare (R : Type*) [CommRing R] :
    Decomposition R SquareVertex SquareSummand :=
  strassenSquareInt.map (Int.castRingHom R)

/-- The exact signed 4096-equation identity, in every coefficient ring. -/
theorem strassenSquare_solves (R : Type*) [CommRing R] :
    (strassenSquare R).Solves :=
  Decomposition.solves_map (Int.castRingHom R) strassenSquareInt_solves

end Brent
