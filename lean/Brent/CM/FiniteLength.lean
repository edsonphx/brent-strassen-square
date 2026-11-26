import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Length

/-!
# `A ⧸ mⁿ` has finite length (discharges `hfin` of `Brent.CM.Dimension`)

DRAFT, NOT YET COMPILED.

In a Noetherian local ring `(A, m)`, the maximal ideal is the only minimal prime of `mⁿ`
(`n ≥ 1`), so `A ⧸ mⁿ` is an Artinian ring, hence an `A`-module of finite length.

Imports Mathlib only.
-/

namespace Brent.CM

open IsLocalRing

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem maximalIdeal_mem_minimalPrimes_pow {n : ℕ} (hn : n ≠ 0) :
    maximalIdeal A ∈ (maximalIdeal A ^ n).minimalPrimes := by
  refine ⟨⟨(maximalIdeal.isMaximal A).isPrime, Ideal.pow_le_self hn⟩, ?_⟩
  rintro p ⟨hp, hle⟩ -
  exact Ideal.IsPrime.le_of_pow_le hle

/-- **`length_A (A ⧸ mⁿ)` is finite.** -/
theorem length_quot_pow_ne_top (n : ℕ) : Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (A ⧸ maximalIdeal A ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero_iff.mpr inferInstance]
    exact ENat.zero_ne_top
  · rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
    haveI : IsArtinianRing (A ⧸ maximalIdeal A ^ n) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
        (maximalIdeal_mem_minimalPrimes_pow hn.ne')
    exact ⟨isNoetherian_quotient _,
      isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := maximalIdeal A ^ n))⟩

end Brent.CM
