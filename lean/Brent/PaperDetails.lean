import Brent.KernelCheck.QuadraticCertificates
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Explicit numerical and modular-reduction statements from Appendix A.2 and §7.
The determinant lemma uses the strict bound as hypothesis, not a claim that the
external Python program or Hadamard's inequality has been formally verified. -/
open scoped BigOperators

namespace Brent.PaperDetails

open QuadraticData

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- The actual integer mixed coefficient in the worked example. -/
theorem appendix_mixed_entry : mixedEntry 0 19 (squareEquationNumber.symm 2225) = -1 := by
  rw [← coefficient_mixedColumn]
  simp only [Equiv.apply_symm_apply]
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- The actual archived covector entry, in the paper's numbering. -/
theorem appendix_covector_entry : functionalEntry 0 2225 = 2 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- On the support of the first covector, there is exactly one nonzero integer
mixed entry, at index 2225. Checking the sparse contraction avoids trusting the CSV. -/
theorem appendix_unique_support : ∀ e : Fin 4096,
    functionalEntry 0 e ≠ 0 ∧
      SparseRow.coefficient e.val (mixedColumn 0 19) ≠ 0 ↔ e = 2225 := by
  decide +kernel

/-- The earlier nineteen mixed coefficients vanish. -/
theorem appendix_earlier_zero (j : Fin 54) (hj : j.val < 19) :
    ∑ e : EquationIndex SquareVertex,
      (mixedEntry 0 j e : ZMod 3) * functionalEntry 0 (squareEquationNumber e) = 0 := by
  apply archived_mixed_zero_before 0 0 j
  simpa [quadraticMatching] using hj

/-- The mixed coefficient is one in characteristic three. -/
theorem appendix_projected_coefficient : projectedMixed 0 0 19 = 1 := by
  simpa [quadraticMatching] using archived_mixed_pivots 0

/-- Strict size control makes reduction modulo `p` faithful on an integer. -/
theorem int_vanishing_iff_mod (p : ℕ) (z : ℤ) (h : z.natAbs < p) :
    (z : ZMod p) = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using h)
  · rintro rfl
    simp

/-- Consequently a square integer minor of determinant magnitude strictly below
`p` vanishes exactly when its reduction modulo `p` vanishes. -/
theorem minor_vanishing_iff_mod_prime {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (M : Matrix n n ℤ) (h : M.det.natAbs < p) :
    (M.map (Int.cast : ℤ → ZMod p)).det = 0 ↔ M.det = 0 := by
  rw [← RingHom.map_det (Int.castRingHom (ZMod p)) M]
  exact int_vanishing_iff_mod p M.det h

end Brent.PaperDetails
