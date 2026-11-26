import Brent.KernelCheck.QuadraticCertificates
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

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

/-! ### Concrete modulus used by the catalogue

The Leibniz bound below is weaker than the paper's Hadamard inequality,
but suffices independently for every minor used by the census, including
stacked-matrix minors. -/

/-- Elementary determinant bound for an integer square matrix. -/
theorem det_abs_le_factorial {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (B : ℤ) (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) :
    |M.det| ≤ (Nat.factorial (Fintype.card n) : ℤ) * B ^ Fintype.card n := by
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul] using
    (Matrix.det_le (A := M) (abv := AbsoluteValue.abs) (x := B) hM)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem censusPrime_isPrime : Nat.Prime 65521 := by decide +kernel

/-- The squared Hadamard expression appearing in the Python program is smaller
than the squared selected prime for every allowed minor size. -/
theorem censusPrime_hadamard_expression (m : Fin 5) :
    (m.val * 4^2)^m.val < 65521^2 := by
  revert m
  decide +kernel

/-- A separate elementary estimate, sufficient even without Hadamard. -/
theorem censusPrime_leibniz_expression (m : Fin 5) :
    Nat.factorial m.val * 4^m.val < 65521 := by
  revert m
  decide +kernel

/-- Faithful reduction for all matrices of order at most four with entry bound four. -/
theorem censusMinor_vanishing_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (hn : Fintype.card n ≤ 4) (hM : ∀ i j, |M i j| ≤ 4) :
    (M.map (Int.cast : ℤ → ZMod 65521)).det = 0 ↔ M.det = 0 := by
  apply minor_vanishing_iff_mod_prime
  have h := det_abs_le_factorial M 4 (by norm_num) hM
  have h' := censusPrime_leibniz_expression ⟨Fintype.card n, by omega⟩
  have h'' : (M.det.natAbs : ℤ) ≤ (Nat.factorial (Fintype.card n) : ℤ) * 4 ^ Fintype.card n := by
    simpa only [Int.natCast_natAbs] using h
  have h₃ : (Nat.factorial (Fintype.card n) : ℤ) * 4 ^ Fintype.card n < 65521 := by
    exact_mod_cast h'
  exact_mod_cast h''.trans_lt h₃

end Brent.PaperDetails
