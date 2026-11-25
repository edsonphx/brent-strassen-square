import Brent.LocalDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Initial values of the local Hilbert function

For a local `k`-algebra `R`, the Hilbert function is `d ↦ dim_k 𝔪^d / 𝔪^(d+1)`. We realize
`𝔪^d / 𝔪^(d+1)` as the image of `𝔪^d` in the `k`-vector space `R ⧸ 𝔪^(d+1)`. This file
proves the generic facts used for the initial values: `H(0) = 1` given a residue map,
upper bounds from spanning families, and lower bounds from linear functionals.
-/

open IsLocalRing
open scoped BigOperators

namespace Brent

variable (k : Type*) {R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- `𝔪^d` as a `k`-subspace. -/
abbrev powK (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R] (d : ℕ) : Submodule k R :=
  (maximalIdeal R ^ d).restrictScalars k

/-- The projection `R → R ⧸ 𝔪^(d+1)` as a `k`-linear map. -/
abbrev proj (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R] (d : ℕ) :
    R →ₗ[k] R ⧸ powK k R (d + 1) :=
  (powK k R (d + 1)).mkQ

/-- The graded piece `𝔪^d / 𝔪^(d+1)`, inside `R ⧸ 𝔪^(d+1)`. -/
abbrev gradedPiece (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R] (d : ℕ) :
    Submodule k (R ⧸ powK k R (d + 1)) :=
  (powK k R d).map (proj k R d)

/-- The local Hilbert function `d ↦ dim_k 𝔪^d / 𝔪^(d+1)`. -/
noncomputable def hilbertValue (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R]
    (d : ℕ) : ℕ :=
  Module.finrank k (gradedPiece k R d)

variable {k}

theorem residue_sub_mem (ev : R →ₐ[k] k) (a : R) :
    a - algebraMap k R (ev a) ∈ maximalIdeal R := by
  by_contra h
  have hu : IsUnit (a - algebraMap k R (ev a)) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using h
  have h0 := hu.map ev
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self] at h0
  exact not_isUnit_zero h0

theorem one_not_mem_maximalIdeal : (1 : R) ∉ maximalIdeal R :=
  (maximalIdeal.isMaximal R).ne_top ∘ (Ideal.eq_top_iff_one _).mpr

theorem proj_eq_iff (d : ℕ) (a b : R) :
    proj k R d a = proj k R d b ↔ a - b ∈ maximalIdeal R ^ (d + 1) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  rfl

theorem proj_mem (d : ℕ) {a : R} (ha : a ∈ maximalIdeal R ^ d) :
    proj k R d a ∈ gradedPiece k R d :=
  Submodule.mem_map_of_mem ha

/-- `H(0) = 1`. -/
theorem hilbertValue_zero (ev : R →ₐ[k] k) : hilbertValue k R 0 = 1 := by
  have hne : proj k R 0 (1 : R) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (1 : R) ∉ maximalIdeal R ^ (0 + 1)
    rw [zero_add, pow_one]
    exact one_not_mem_maximalIdeal
  have heq : gradedPiece k R 0 = Submodule.span k {proj k R 0 (1 : R)} := by
    apply le_antisymm
    · rintro _ ⟨a, -, rfl⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨ev a, ?_⟩
      rw [← map_smul, proj_eq_iff, Algebra.smul_def, mul_one, zero_add, pow_one, ← neg_sub,
        Ideal.neg_mem_iff]
      exact residue_sub_mem ev a
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact proj_mem 0 (by rw [pow_zero, Ideal.one_eq_top]; trivial)
  rw [hilbertValue, heq, finrank_span_singleton hne]

/-- Generators of `𝔪` modulo `𝔪²` span `𝔪/𝔪²`. -/
theorem gradedPiece_one_le_span (ev : R →ₐ[k] k) {n : ℕ} (z : Fin n → R)
    (hz : ∀ i, z i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ maximalIdeal R ^ 2) :
    gradedPiece k R 1 ≤ Submodule.span k (Set.range fun i => proj k R 1 (z i)) := by
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a ∈ maximalIdeal R := by
    have h1 : a ∈ maximalIdeal R ^ 1 := ha
    rwa [pow_one] at h1
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp (hgen ha')
  obtain ⟨f, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hs
  have e : proj k R 1 (∑ i, f i * z i + r) = ∑ i, ev (f i) • proj k R 1 (z i) := by
    simp only [← map_smul, ← map_sum]
    rw [proj_eq_iff]
    have : ∑ i, f i * z i + r - ∑ i, ev (f i) • z i =
        ∑ i, (f i - algebraMap k R (ev (f i))) * z i + r := by
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]; ring
    rw [this]
    refine Ideal.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) hr
    rw [pow_two]
    exact Ideal.mul_mem_mul (residue_sub_mem ev (f i)) (hz i)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Generators of `𝔪^d` modulo `𝔪^(d+1)` span `𝔪^d/𝔪^(d+1)`. -/
theorem gradedPiece_le_span (ev : R →ₐ[k] k) (d : ℕ) {ι : Type*} [Fintype ι] (w : ι → R)
    (hw : ∀ i, w i ∈ maximalIdeal R ^ d)
    (hgen : maximalIdeal R ^ d ≤ Ideal.span (Set.range w) ⊔ maximalIdeal R ^ (d + 1)) :
    gradedPiece k R d ≤ Submodule.span k (Set.range fun i => proj k R d (w i)) := by
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a ∈ maximalIdeal R ^ d := ha
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp (hgen ha')
  obtain ⟨f, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hs
  have e : proj k R d (∑ i, f i * w i + r) = ∑ i, ev (f i) • proj k R d (w i) := by
    simp only [← map_smul, ← map_sum]
    rw [proj_eq_iff]
    have : ∑ i, f i * w i + r - ∑ i, ev (f i) • w i =
        ∑ i, (f i - algebraMap k R (ev (f i))) * w i + r := by
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]; ring
    rw [this]
    refine Ideal.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) hr
    rw [pow_succ']
    exact Ideal.mul_mem_mul (residue_sub_mem ev (f i)) (hw i)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Products of generators of `𝔪` span `𝔪²/𝔪³`. -/
theorem gradedPiece_two_le_span (ev : R →ₐ[k] k) {n : ℕ} (z : Fin n → R)
    (hz : ∀ i, z i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ maximalIdeal R ^ 2) :
    gradedPiece k R 2 ≤
      Submodule.span k (Set.range fun p : Fin n × Fin n => proj k R 2 (z p.1 * z p.2)) := by
  let w : Fin n × Fin n → R := fun p => z p.1 * z p.2
  have hw : ∀ p, w p ∈ maximalIdeal R ^ 2 := fun p => by
    rw [pow_two]; exact Ideal.mul_mem_mul (hz p.1) (hz p.2)
  have hzm : Ideal.span (Set.range z) ≤ maximalIdeal R := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hz i
  have hzz : Ideal.span (Set.range z) * Ideal.span (Set.range z) ≤ Ideal.span (Set.range w) := by
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨(i, j), rfl⟩
  have h3 : maximalIdeal R ^ 2 * maximalIdeal R = maximalIdeal R ^ (2 + 1) := (pow_succ _ _).symm
  have hle : maximalIdeal R ^ 2 ≤ Ideal.span (Set.range w) ⊔ maximalIdeal R ^ (2 + 1) := by
    calc maximalIdeal R ^ 2 = maximalIdeal R * maximalIdeal R := pow_two _
      _ ≤ (Ideal.span (Set.range z) ⊔ maximalIdeal R ^ 2) *
          (Ideal.span (Set.range z) ⊔ maximalIdeal R ^ 2) := Ideal.mul_mono hgen hgen
      _ ≤ Ideal.span (Set.range w) ⊔ maximalIdeal R ^ (2 + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        refine sup_le (sup_le (le_sup_of_le_left hzz) ?_) (sup_le ?_ ?_)
        · refine le_sup_of_le_right ?_
          rw [← h3, mul_comm]
          exact Ideal.mul_mono_right hzm
        · refine le_sup_of_le_right ?_
          rw [← h3]
          exact Ideal.mul_mono_right hzm
        · refine le_sup_of_le_right ?_
          rw [← h3]
          exact Ideal.mul_mono_right (Ideal.pow_le_self (by norm_num))
  exact gradedPiece_le_span ev 2 w hw hle

/-- A spanning family bounds the Hilbert value and makes the piece finite-dimensional. -/
theorem hilbertValue_le_of_le_span {d n : ℕ} (v : Fin n → R ⧸ powK k R (d + 1))
    (hv : gradedPiece k R d ≤ Submodule.span k (Set.range v)) :
    FiniteDimensional k (gradedPiece k R d) ∧ hilbertValue k R d ≤ n := by
  haveI : FiniteDimensional k (Submodule.span k (Set.range v)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range v)
  refine ⟨Submodule.finiteDimensional_of_le hv, ?_⟩
  exact (Submodule.finrank_mono hv).trans ((finrank_range_le_card v).trans (by simp))

/-- A linear map on `R` that kills `𝔪^(d+1)` and is onto `k^n` from `𝔪^d` bounds `H(d)`
from below. -/
theorem le_hilbertValue {d n : ℕ} [FiniteDimensional k (gradedPiece k R d)]
    (Λ : R →ₗ[k] (Fin n → k)) (hΛ : ∀ a ∈ maximalIdeal R ^ (d + 1), Λ a = 0)
    {ι : Type*} (y : ι → R) (hy : ∀ i, y i ∈ maximalIdeal R ^ d)
    (hspan : Submodule.span k (Set.range fun i => Λ (y i)) = ⊤) :
    n ≤ hilbertValue k R d := by
  let L : (R ⧸ powK k R (d + 1)) →ₗ[k] (Fin n → k) :=
    (powK k R (d + 1)).liftQ Λ fun a ha => hΛ a ha
  have hL : (gradedPiece k R d).map L = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨proj k R d (y i), proj_mem d (hy i), rfl⟩
  have h := Submodule.finrank_map_le L (gradedPiece k R d)
  rw [hL, finrank_top, Module.finrank_fin_fun] at h
  exact h

end Brent
