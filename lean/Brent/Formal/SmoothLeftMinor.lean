import Brent.Formal.SmoothLeftMinorData
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The 197-parameter tangent minor at `q_L`

`params` selects 197 group parameters and `freeNum` the 197 variables outside the pivot columns
`SmoothL.col` of the rank certificate. The tangents of the selected parameters, restricted to the
free variables, form an integer matrix that is lower triangular with diagonal `±1`
(kernel-checked), so it is invertible over every commutative ring.
-/

namespace Brent.Formal.SmoothLeftMinor

open Brent Brent.Formal Brent.SmoothL

instance : DecidableEq GrpIdx := instDecidableEqSum

/-- The free variables. -/
def freeVar (i : Fin 197) : Var := squareVariableNumber.symm (freeNum i)

/-- The tangent minor on the free variables. -/
def minor : Matrix (Fin 197) (Fin 197) ℤ := Matrix.of fun i j => tanLeft (params i) (freeVar j)

set_option maxRecDepth 100000 in
theorem minor_lower : ∀ i j : Fin 197, i < j → minor i j = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem minor_diag : ∀ i : Fin 197, minor i i = 1 ∨ minor i i = -1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem params_injective : Function.Injective params := by
  have h : ∀ i j : Fin 197, params i = params j → i = j := by decide +kernel
  exact fun i j => h i j

set_option maxRecDepth 100000 in
theorem freeNum_injective : Function.Injective freeNum := by
  have h : ∀ i j : Fin 197, freeNum i = freeNum j → i = j := by decide +kernel
  exact fun i j => h i j

theorem freeVar_injective : Function.Injective freeVar :=
  fun i j h => freeNum_injective (squareVariableNumber.symm.injective h)

theorem isUnit_det_minor : IsUnit minor.det := by
  have hlow : minor.BlockTriangular OrderDual.toDual := fun i j hij => minor_lower i j hij
  rw [Matrix.det_of_lowerTriangular minor hlow]
  refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ => ?_
  rcases minor_diag i with h | h <;> rw [h]
  · exact isUnit_one
  · exact isUnit_one.neg

/-- **The minor is invertible over every commutative ring.** -/
theorem isUnit_minor_map (K : Type*) [CommRing K] : IsUnit (minor.map (Int.castRingHom K)) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isUnit_det_minor.map _

/-! ### The free variables are not pivot columns -/

/-- Pivot column numbers, extended strictly monotonically past the end. -/
def colNumN (i : ℕ) : ℕ := if h : i < 2155 then (squareVariableNumber (col ⟨i, h⟩)).val else 2352 + i

set_option maxRecDepth 100000 in
theorem colNumN_succ_check : ∀ i : Fin 2155, colNumN i.val < colNumN (i.val + 1) := by
  decide +kernel

theorem colNumN_strictMono : StrictMono colNumN := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  by_cases h : i < 2155
  · exact colNumN_succ_check ⟨i, h⟩
  · have h' : ¬ i + 1 < 2155 := by omega
    simp only [colNumN, dif_neg h, dif_neg h']
    omega

set_option maxRecDepth 100000 in
theorem pos_check : ∀ f : Fin 197,
    (pos f = 0 ∨ colNumN (pos f - 1) < (freeNum f).val) ∧ (freeNum f).val < colNumN (pos f) := by
  decide +kernel

theorem freeVar_not_col (f : Fin 197) : freeVar f ∉ Set.range col := by
  rintro ⟨i, hi⟩
  have hnum : colNumN i.val = (freeNum f).val := by
    simp only [colNumN, dif_pos i.isLt, hi, freeVar, Equiv.apply_symm_apply]
  obtain ⟨hlo, hhi⟩ := pos_check f
  by_cases hp : pos f ≤ i.val
  · have := colNumN_strictMono.monotone hp
    omega
  · have hp' : i.val ≤ pos f - 1 := by omega
    have := colNumN_strictMono.monotone hp'
    rcases hlo with h0 | hlo
    · omega
    · omega

theorem col_injective : Function.Injective col := by
  intro i j h
  apply Fin.ext
  apply colNumN_strictMono.injective
  simp only [colNumN, dif_pos i.isLt, dif_pos j.isLt, h]

end Brent.Formal.SmoothLeftMinor
