import Brent.KernelCheck.HilbertInitial
import Brent.KernelCheck.MixedRank
import Brent.Generated.AugmentedChecks


/-!
# The initial Hilbert function `(1, 251, 30978)`

`H(0) = 1` and `H(1) = 251` hold over every field. `H(2) = 31626 - dim Rel`, and
`dim Rel = 2749 - 2101 = 648` whenever `2 ≠ 0`, using the kernel-checked augmented rank.
In particular the values hold in characteristic three and in characteristic zero.
-/

namespace Brent.HilbertValues

open UpperBound

variable (k : Type) [Field k]

/-- `H(2) = 30978` over every field in which `2 ≠ 0`. -/
theorem hilbertValue_two (h2 : (2 : k) ≠ 0) : hilbertValue k (A k) 2 = 30978 :=
  MixedRank.hilbertValue_two_of_rank k h2 (AugmentedTrace.augmented_rank k)

/-- **Initial Hilbert values** `(1, 251, 30978)` over every field of characteristic `≠ 2`. -/
theorem hilbert_initial (h2 : (2 : k) ≠ 0) :
    hilbertValue k (A k) 0 = 1 ∧ hilbertValue k (A k) 1 = 251 ∧
      hilbertValue k (A k) 2 = 30978 :=
  ⟨HilbertInitial.hilbertValue_zero k, HilbertInitial.hilbertValue_one k, hilbertValue_two k h2⟩

theorem two_ne_zero_of_charP_three [CharP k 3] : (2 : k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k 3] at h'
  omega

/-- The initial Hilbert values in characteristic three. -/
theorem hilbert_initial_charP_three [CharP k 3] :
    hilbertValue k (A k) 0 = 1 ∧ hilbertValue k (A k) 1 = 251 ∧
      hilbertValue k (A k) 2 = 30978 :=
  hilbert_initial k (two_ne_zero_of_charP_three k)

/-- The initial Hilbert values in characteristic zero. -/
theorem hilbert_initial_charZero [CharZero k] :
    hilbertValue k (A k) 0 = 1 ∧ hilbertValue k (A k) 1 = 251 ∧
      hilbertValue k (A k) 2 = 30978 :=
  hilbert_initial k two_ne_zero

end Brent.HilbertValues
