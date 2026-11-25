import Brent.SmoothL
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# The 2155 × 2155 Jacobian minor at `q_L`

The radix certificate of `Brent.SmoothL` proves, over every field of characteristic three, that
the selected rows `original i` span a space of dimension 2155. In characteristic three these rows
are the selected Jacobian columns restricted to the selected equations, so the integer minor has
nonzero determinant modulo three, hence over `ℤ`, hence over every field of characteristic zero.
-/

namespace Brent.SmoothL
open SparseRow

def eqn (j : Fin 2155) : EquationIndex SquareVertex := squareEquationNumber.symm (coord j)

/-- The integer minor. -/
def minorInt : Matrix (Fin 2155) (Fin 2155) ℤ :=
  Matrix.of fun i j => pointDec.jacobianColumn (col i) (eqn j).1 (eqn j).2.1 (eqn j).2.2

theorem decode_original (K : Type*) [Field K] [CharP K 3] (i j : Fin 2155) :
    decode (K := K) (fun j => (coord j).val) (original i) j = (minorInt i j : K) := by
  have hc : (coord j).val = (squareEquationNumber (eqn j)).val := by simp [eqn]
  simp only [decode, original, coefficient_subScaled, hc, column_correct, minorInt, Matrix.of_apply,
    Int.cast_sub, Int.cast_mul]
  have : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  simp [this]

theorem det_minor_charThree (h : ∀ i, checkAt i = true) (K : Type*) [Field K] [CharP K 3] :
    (minorInt.map (Int.castRingHom K)).det ≠ 0 := by
  have hr := rank_of_checks h K
  have hli : LinearIndependent K (fun i => decode (K := K) (fun j => (coord j).val) (original i)) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hr, Fintype.card_fin]
  have heq : (fun i => decode (K := K) (fun j => (coord j).val) (original i)) =
      (minorInt.map (Int.castRingHom K)).row := by
    funext i j; simp [decode_original, Matrix.row]
  rw [heq, Matrix.linearIndependent_rows_iff_isUnit] at hli
  exact (Matrix.isUnit_iff_isUnit_det _).mp hli |>.ne_zero

theorem det_minorInt_ne_zero (h : ∀ i, checkAt i = true) : minorInt.det ≠ 0 := by
  intro h0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply det_minor_charThree h (ZMod 3)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem det_minor_ne_zero (h : ∀ i, checkAt i = true) (K : Type*) [Field K]
    (hK : CharP K 3 ∨ CharZero K) : (minorInt.map (Int.castRingHom K)).det ≠ 0 := by
  rcases hK with hK | hK
  · exact det_minor_charThree h K
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [eq_intCast]
    exact Int.cast_ne_zero.mpr (det_minorInt_ne_zero h)

end Brent.SmoothL
