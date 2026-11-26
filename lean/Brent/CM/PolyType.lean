import Brent.CM.HilbertSerre
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Polynomial.Basic

/-!
# Functions of polynomial type are polynomials (roadmap step B, first part)

DRAFT, NOT YET COMPILED.

`OrderLE f a` (the `a`-th difference of `f` eventually vanishes) holds exactly when `f` agrees
on a tail with a real polynomial of degree `< a`, and a polynomial bounded by `C (n + 1)ᵇ` has
degree `≤ b`. These are the comparisons that the Hilbert–Samuel degree `d(A)` needs:

* `exists_poly_of_orderLE`, `orderLE_of_poly`;
* `degree_le_of_bound`: a polynomial bounded by `C (n + 1)ᵇ` on the naturals has degree `≤ b`;
* `orderLE_of_bound`: `OrderLE f a` and `|f n| ≤ C (n + 1)ᵇ` give `OrderLE f (b + 1)`;
* `bound_of_orderLE`: `OrderLE f (b + 1)` gives `|f n| ≤ C (n + 1)ᵇ` on a tail.

Imports Mathlib and `Brent.CM.HilbertSerre` only.
-/

namespace Brent.CM

open Finset Polynomial Filter fwdDiff

theorem diffPow_eq_iterate (e : ℕ) (f : ℕ → ℤ) : diffPow e f = (fwdDiff 1)^[e] f := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [diffPow_succ, ih, Function.iterate_succ_apply']
    rfl

/-- **Newton's forward formula** for `diffPow`. -/
theorem shift_eq_sum_diffPow (f : ℕ → ℤ) (n₀ k : ℕ) :
    f (n₀ + k) = ∑ i ∈ range (k + 1), (k.choose i : ℤ) * diffPow i f n₀ := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) f k n₀
  rw [smul_eq_mul, mul_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, diffPow_eq_iterate]

theorem diffPow_eq_zero_of_le {f : ℕ → ℤ} {a n₀ : ℕ} (h : ∀ n ≥ n₀, diffPow a f n = 0)
    {i : ℕ} (hi : a ≤ i) : ∀ n ≥ n₀, diffPow i f n = 0 := by
  intro n hn
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [add_comm, diffPow_add]
  have hz : ∀ m ≥ n₀, diffPow a f m = (fun _ => (0 : ℤ)) m := h
  rw [diffPow_congr c hz n hn, diffPow_const_zero]

/-- On the tail, a function of order `≤ a` is a combination of `C(k, i)` with `i < a`. -/
theorem eq_sum_of_orderLE {f : ℕ → ℤ} {a n₀ : ℕ} (h : ∀ n ≥ n₀, diffPow a f n = 0) (k : ℕ) :
    f (n₀ + k) = ∑ i ∈ range a, (k.choose i : ℤ) * diffPow i f n₀ := by
  rw [shift_eq_sum_diffPow]
  have e1 : ∑ i ∈ range (k + 1), (k.choose i : ℤ) * diffPow i f n₀ =
      ∑ i ∈ range (max (k + 1) a), (k.choose i : ℤ) * diffPow i f n₀ :=
    Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _)) fun i _ hi => by
      rw [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have e2 : ∑ i ∈ range a, (k.choose i : ℤ) * diffPow i f n₀ =
      ∑ i ∈ range (max (k + 1) a), (k.choose i : ℤ) * diffPow i f n₀ :=
    Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) fun i _ hi => by
      rw [Finset.mem_range, not_lt] at hi
      rw [diffPow_eq_zero_of_le h hi n₀ le_rfl, mul_zero]
  rw [e1, e2]

/-- The binomial coefficient `C(x − n₀, i)` as a real polynomial in `x`. -/
noncomputable def binomPoly (n₀ i : ℕ) : ℝ[X] :=
  C ((i.factorial : ℝ)⁻¹) * (descPochhammer ℝ i).comp (X - C (n₀ : ℝ))

theorem eval_binomPoly (n₀ i k : ℕ) :
    (binomPoly n₀ i).eval ((n₀ + k : ℕ) : ℝ) = (k.choose i : ℝ) := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C,
    show ((n₀ + k : ℕ) : ℝ) - n₀ = (k : ℝ) by push_cast; ring,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  push_cast
  field_simp

theorem degree_binomPoly_le (n₀ i : ℕ) : (binomPoly n₀ i).degree ≤ i := by
  rw [binomPoly]
  refine (degree_mul_le _ _).trans ?_
  refine (add_le_add (degree_C_le) (degree_le_of_natDegree_le ?_)).trans (by simp)
  rw [natDegree_comp, descPochhammer_natDegree, natDegree_sub_C, natDegree_X, mul_one]

/-- **A function of order `≤ a` agrees on a tail with a real polynomial of degree `< a`.** -/
theorem exists_poly_of_orderLE {f : ℕ → ℤ} {a : ℕ} (h : OrderLE f a) :
    ∃ P : ℝ[X], P.degree < a ∧ ∃ n₀, ∀ n ≥ n₀, (f n : ℝ) = P.eval (n : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨∑ i ∈ range a, C ((diffPow i f n₀ : ℤ) : ℝ) * binomPoly n₀ i, ?_, n₀, fun n hn => ?_⟩
  · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_natCast a)]
    intro i hi
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add degree_C_le (degree_binomPoly_le n₀ i)) ?_
    rw [zero_add]
    exact_mod_cast Finset.mem_range.mp hi
  · obtain ⟨k, rfl⟩ : ∃ k, n = n₀ + k := ⟨n - n₀, by omega⟩
    rw [eq_sum_of_orderLE hn₀ k, eval_finset_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_mul, eval_C, eval_binomPoly]
    push_cast
    ring

/-- Differences of `n ↦ P (n)` are the polynomial differences. -/
theorem cast_diffPow_poly {f : ℕ → ℤ} {P : ℝ[X]} {n₀ : ℕ}
    (hf : ∀ n ≥ n₀, (f n : ℝ) = P.eval (n : ℝ)) (e : ℕ) :
    ∀ n ≥ n₀, (diffPow e f n : ℝ) = ((fwdDiff (1 : ℝ))^[e] P.eval) (n : ℝ) := by
  induction e with
  | zero => exact hf
  | succ e ih =>
    intro n hn
    rw [diffPow_succ, Function.iterate_succ_apply']
    simp only [diff]
    rw [Int.cast_sub, ih n hn, ih (n + 1) (by omega)]
    simp [fwdDiff]

/-- **Agreeing on a tail with a polynomial of degree `< a` gives order `≤ a`.** -/
theorem orderLE_of_poly {f : ℕ → ℤ} {P : ℝ[X]} {a n₀ : ℕ}
    (hf : ∀ n ≥ n₀, (f n : ℝ) = P.eval (n : ℝ)) (hP : P.degree < a) : OrderLE f a := by
  have hlt : 0 < a → P.natDegree < a := fun ha => by
    by_cases h0 : P = 0
    · simpa [h0] using ha
    · rwa [degree_eq_natDegree h0, Nat.cast_lt] at hP
  refine ⟨n₀, fun n hn => ?_⟩
  have h := cast_diffPow_poly hf a n hn
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hP0 : P = 0 := by
      by_contra h0
      rw [degree_eq_natDegree h0, Nat.cast_lt] at hP
      exact Nat.not_lt_zero _ hP
    simpa [hP0] using h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (hlt ha)] at h
    simpa using h

/-- **A polynomial bounded by `C (n + 1)ᵇ` on the naturals has degree `≤ b`.** -/
theorem degree_le_of_bound {P : ℝ[X]} {b n₀ : ℕ} {Cb : ℝ}
    (hP : ∀ n ≥ n₀, |P.eval (n : ℝ)| ≤ Cb * ((n : ℝ) + 1) ^ b) : P.degree ≤ b := by
  by_contra hlt
  push_neg at hlt
  set Q : ℝ[X] := (X + C 1) ^ b with hQ
  have hQ0 : Q ≠ 0 := pow_ne_zero _ (X_add_C_ne_zero 1)
  have hQdeg : Q.degree = b := by
    rw [hQ, degree_pow, degree_X_add_C, nsmul_one]
  have hlim := (abs_div_tendsto_atTop_atTop_of_degree_gt P Q (by rw [hQdeg]; exact hlt) hQ0).comp
    tendsto_natCast_atTop_atTop
  have hev := (hlim.eventually_gt_atTop Cb).and (eventually_ge_atTop n₀)
  obtain ⟨n, hgt, hn⟩ := hev.exists
  simp only [Function.comp_apply] at hgt
  have hQpos : 0 < Q.eval (n : ℝ) := by
    rw [hQ, eval_pow, eval_add, eval_X, eval_C]
    positivity
  rw [abs_div, abs_of_pos hQpos, lt_div_iff₀ hQpos] at hgt
  have hQe : Q.eval (n : ℝ) = ((n : ℝ) + 1) ^ b := by
    rw [hQ, eval_pow, eval_add, eval_X, eval_C]
  rw [hQe] at hgt
  linarith [hP n hn]

/-- **Comparison.** A function of polynomial type bounded by `C (n + 1)ᵇ` has order `≤ b + 1`. -/
theorem orderLE_of_bound {f : ℕ → ℤ} {a b n₁ : ℕ} {Cb : ℝ} (hf : OrderLE f a)
    (hb : ∀ n ≥ n₁, |(f n : ℝ)| ≤ Cb * ((n : ℝ) + 1) ^ b) : OrderLE f (b + 1) := by
  obtain ⟨P, -, n₀, hP⟩ := exists_poly_of_orderLE hf
  have hPb : ∀ n ≥ max n₀ n₁, |P.eval (n : ℝ)| ≤ Cb * ((n : ℝ) + 1) ^ b := by
    intro n hn
    rw [← hP n (by omega)]
    exact hb n (by omega)
  have hdeg := degree_le_of_bound hPb
  refine orderLE_of_poly (n₀ := n₀) hP (lt_of_le_of_lt hdeg ?_)
  exact_mod_cast Nat.lt_succ_self b

/-- **Growth.** A function of order `≤ b + 1` is bounded by `C (n + 1)ᵇ` on a tail. -/
theorem bound_of_orderLE {f : ℕ → ℤ} {b : ℕ} (hf : OrderLE f (b + 1)) :
    ∃ Cb : ℝ, ∃ n₁, ∀ n ≥ n₁, |(f n : ℝ)| ≤ Cb * ((n : ℝ) + 1) ^ b := by
  obtain ⟨P, hPdeg, n₀, hP⟩ := exists_poly_of_orderLE hf
  set Q : ℝ[X] := (X + C 1) ^ b with hQ
  have hQdeg : Q.degree = b := by
    rw [hQ, degree_pow, degree_X_add_C, nsmul_one]
  have hle : P.degree ≤ Q.degree := by
    rw [hQdeg]
    by_cases h0 : P = 0
    · simp [h0]
    · rw [degree_eq_natDegree h0] at hPdeg ⊢
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hPdeg)
  obtain ⟨c, hc⟩ := (Polynomial.isBigO_atTop_of_degree_le P Q hle).bound
  have hev := (tendsto_natCast_atTop_atTop.eventually hc).and (eventually_ge_atTop n₀)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hev
  refine ⟨c, n₁, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₁ n hn
  rw [hP n h2]
  have hQe : Q.eval (n : ℝ) = ((n : ℝ) + 1) ^ b := by
    rw [hQ, eval_pow, eval_add, eval_X, eval_C]
  simp only [Real.norm_eq_abs] at h1
  rw [hQe, abs_of_pos (by positivity)] at h1
  exact h1

end Brent.CM
