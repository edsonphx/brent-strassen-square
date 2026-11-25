import Brent.LocalHomDimension
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The germ of affine space at the origin

`AffineGerm k n` is the polynomial ring in `n` variables localized at the origin.
We prove that its dimension is at least `n`, construct its first-order
specializations along the coordinate axes, and show that an element of the maximal
ideal with vanishing first derivatives lies in the square of the maximal ideal.
-/

open MvPolynomial

namespace Brent

variable (k : Type*) [Field k] (n : ℕ)

theorem coeff_zero_eq' (g : MvPolynomial (Fin n) k) : coeff 0 g = constantCoeff g := by
  rw [constantCoeff_eq]

theorem mem_idealOfVars_iff (g : MvPolynomial (Fin n) k) :
    g ∈ idealOfVars (Fin n) k ↔ constantCoeff g = 0 := by
  rw [← pow_one (idealOfVars (Fin n) k), mem_pow_idealOfVars_iff']
  constructor
  · intro h
    rw [← coeff_zero_eq']
    exact h 0 (by simp)
  · intro h x hx
    have : x = 0 := by
      have : x.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff x).mp this
    rw [this, coeff_zero_eq', h]

theorem idealOfVars_eq_ker :
    idealOfVars (Fin n) k = RingHom.ker (constantCoeff : MvPolynomial (Fin n) k →+* k) := by
  ext g
  rw [mem_idealOfVars_iff, RingHom.mem_ker]

instance idealOfVars_isMaximal : (idealOfVars (Fin n) k).IsMaximal := by
  rw [idealOfVars_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ a⟩

/-- Polynomial functions near the origin of `kⁿ`. -/
abbrev AffineGerm := Localization.AtPrime (idealOfVars (Fin n) k)

section Chain

/-- Set the first `j` coordinates to zero. -/
noncomputable def killFirst (j : ℕ) : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) k :=
  eval₂Hom C fun i => if i.val < j then 0 else X i

theorem killFirst_comp (j : ℕ) : (killFirst k n (j + 1)).comp (killFirst k n j) = killFirst k n (j + 1) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [killFirst]
  · intro i
    simp only [RingHom.comp_apply, killFirst, eval₂Hom_X']
    by_cases h : i.val < j
    · simp [h, show i.val < j + 1 by omega]
    · by_cases h' : i.val < j + 1
      · simp [h, h']; omega
      · simp [h, h']; intro; omega

theorem killFirst_all : killFirst k n n = C.comp constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [killFirst]
  · intro i; simp [killFirst, i.isLt]

instance killFirst_ker_isPrime (j : ℕ) : (RingHom.ker (killFirst k n j)).IsPrime :=
  RingHom.ker_isPrime _

theorem killFirst_ker_lt (j : Fin n) :
    RingHom.ker (killFirst k n j.val) < RingHom.ker (killFirst k n (j.val + 1)) := by
  refine lt_of_le_of_ne (fun g hg => ?_) fun h => ?_
  · rw [RingHom.mem_ker] at hg ⊢
    rw [← killFirst_comp, RingHom.comp_apply, hg, map_zero]
  · have hmem : X j ∈ RingHom.ker (killFirst k n (j.val + 1)) := by
      simp [RingHom.mem_ker, killFirst]
    rw [← h, RingHom.mem_ker] at hmem
    simp [killFirst] at hmem

theorem killFirst_ker_last : RingHom.ker (killFirst k n n) ≤ idealOfVars (Fin n) k := by
  intro g hg
  rw [RingHom.mem_ker, killFirst_all, RingHom.comp_apply, C_eq_zero] at hg
  exact (mem_idealOfVars_iff k n g).mpr hg

theorem le_idealOfVars_height : (n : ℕ∞) ≤ (idealOfVars (Fin n) k).height := by
  let P : Fin (n + 1) → PrimeSpectrum (MvPolynomial (Fin n) k) :=
    fun j => ⟨RingHom.ker (killFirst k n j.val), inferInstance⟩
  let series : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) k)) :=
    ⟨n, P, fun j => by
      change RingHom.ker (killFirst k n j.val) < RingHom.ker (killFirst k n (j.val + 1))
      exact killFirst_ker_lt k n j⟩
  have hlen : (n : ℕ∞) ≤ Order.height series.last := Order.length_le_height_last (p := series)
  rw [Ideal.height_eq_primeHeight]
  calc (n : ℕ∞) ≤ Order.height series.last := hlen
    _ = (RingHom.ker (killFirst k n n)).primeHeight := rfl
    _ ≤ (idealOfVars (Fin n) k).primeHeight := Ideal.primeHeight_mono (killFirst_ker_last k n)

theorem le_ringKrullDim_affineGerm : (n : WithBot ℕ∞) ≤ ringKrullDim (AffineGerm k n) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (idealOfVars (Fin n) k) (AffineGerm k n)]
  exact_mod_cast le_idealOfVars_height k n

end Chain

section Specialization

/-- First-order evaluation along the `i`-th axis. -/
noncomputable def axisJet (i : Fin n) : MvPolynomial (Fin n) k →+* DualNumber k :=
  eval₂Hom (algebraMap k (DualNumber k)) fun j => if j = i then DualNumber.eps else 0

theorem fst_axisJet (i : Fin n) (g : MvPolynomial (Fin n) k) :
    (axisJet k n i g).fst = constantCoeff g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [axisJet, TrivSqZeroExt.algebraMap_eq_inl]
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
    rw [map_mul, TrivSqZeroExt.fst_mul, hf, map_mul, constantCoeff_X]
    by_cases h : j = i <;> simp [axisJet, h]

theorem snd_axisJet (i : Fin n) (g : MvPolynomial (Fin n) k) :
    (axisJet k n i g).snd = coeff (Finsupp.single i 1) g := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp only [axisJet, eval₂Hom_C, coeff_C]
    rw [if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
    rfl
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
    rw [map_mul, coeff_mul_X', TrivSqZeroExt.snd_mul, hf, fst_axisJet]
    by_cases h : j = i
    · subst h
      simp [axisJet, coeff_zero_eq']
    · have hj : j ∉ (Finsupp.single i 1 : Fin n →₀ ℕ).support := by
        simp [Finsupp.support_single_ne_zero, h]
      simp [axisJet, h, hj]

theorem axisJet_unit (i : Fin n) (g : (idealOfVars (Fin n) k).primeCompl) :
    IsUnit (axisJet k n i g) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_axisJet, isUnit_iff_ne_zero]
  intro h
  exact g.2 ((mem_idealOfVars_iff k n g).mpr h)

/-- First-order specialization of the germ along the `i`-th axis. -/
noncomputable def germJet (i : Fin n) : AffineGerm k n →+* DualNumber k :=
  IsLocalization.lift (M := (idealOfVars (Fin n) k).primeCompl) (axisJet_unit k n i)

theorem germJet_algebraMap (i : Fin n) (g : MvPolynomial (Fin n) k) :
    germJet k n i (algebraMap _ (AffineGerm k n) g) = axisJet k n i g :=
  IsLocalization.lift_eq _ _

theorem constantCoeff_eq_zero_of_mk'_mem (g : MvPolynomial (Fin n) k)
    (h : (idealOfVars (Fin n) k).primeCompl)
    (hb : IsLocalization.mk' (AffineGerm k n) g h ∈ IsLocalRing.maximalIdeal (AffineGerm k n)) :
    constantCoeff g = 0 := by
  have : algebraMap _ (AffineGerm k n) g ∈ IsLocalRing.maximalIdeal (AffineGerm k n) := by
    rw [← IsLocalization.mk'_spec (AffineGerm k n) g h]
    exact Ideal.mul_mem_right _ _ hb
  exact (mem_idealOfVars_iff k n g).mp
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff (AffineGerm k n) (idealOfVars (Fin n) k) g).mp this)

theorem fst_germJet_of_mem (i : Fin n) {b : AffineGerm k n}
    (hb : b ∈ IsLocalRing.maximalIdeal (AffineGerm k n)) : (germJet k n i b).fst = 0 := by
  obtain ⟨⟨g, h⟩, rfl⟩ := IsLocalization.mk'_surjective (idealOfVars (Fin n) k).primeCompl b
  dsimp only at hb ⊢
  have hg := constantCoeff_eq_zero_of_mk'_mem k n g h hb
  have hspec := congrArg (germJet k n i) (IsLocalization.mk'_spec (AffineGerm k n) g h)
  rw [map_mul, germJet_algebraMap, germJet_algebraMap] at hspec
  have hfst := congrArg TrivSqZeroExt.fst hspec
  rw [TrivSqZeroExt.fst_mul, fst_axisJet, fst_axisJet, hg] at hfst
  have hh : constantCoeff (h : MvPolynomial (Fin n) k) ≠ 0 :=
    fun h0 => h.2 ((mem_idealOfVars_iff k n _).mpr h0)
  exact (mul_eq_zero.mp hfst).resolve_right hh

/-- First-order Taylor expansion at the origin. -/
theorem sub_linear_mem_sq (g : MvPolynomial (Fin n) k) :
    g - C (constantCoeff g) - ∑ i, C (coeff (Finsupp.single i 1) g) * X i ∈
      idealOfVars (Fin n) k ^ 2 := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a =>
    have h0 : ∀ i : Fin n, coeff (Finsupp.single i 1) (C a : MvPolynomial (Fin n) k) = 0 := by
      intro i
      rw [coeff_C, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
    simp [h0]
  | add f g hf hg =>
    have e : f + g - C (constantCoeff (f + g)) -
        ∑ i, C (coeff (Finsupp.single i 1) (f + g)) * X i =
        (f - C (constantCoeff f) - ∑ i, C (coeff (Finsupp.single i 1) f) * X i) +
        (g - C (constantCoeff g) - ∑ i, C (coeff (Finsupp.single i 1) g) * X i) := by
      simp only [map_add, coeff_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [e]
    exact add_mem hf hg
  | mul_X f j hf =>
    have hc : ∀ i : Fin n, coeff (Finsupp.single i 1) (f * X j) =
        if i = j then constantCoeff f else 0 := by
      intro i
      rw [coeff_mul_X']
      by_cases h : i = j
      · subst h
        simp [coeff_zero_eq']
      · have hj : j ∉ (Finsupp.single i 1 : Fin n →₀ ℕ).support := by
          simp [Finsupp.support_single_ne_zero, Ne.symm h]
        simp [hj, h]
    have e : f * X j - C (constantCoeff (f * X j)) -
        ∑ i, C (coeff (Finsupp.single i 1) (f * X j)) * X i =
        (f - C (constantCoeff f) - ∑ i, C (coeff (Finsupp.single i 1) f) * X i) * X j +
        (∑ i, C (coeff (Finsupp.single i 1) f) * X i) * X j := by
      simp only [hc, map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
      simp only [apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      ring
    have hX : ∀ i : Fin n, X i ∈ idealOfVars (Fin n) k := fun i => Ideal.subset_span ⟨i, rfl⟩
    rw [e, pow_two]
    refine add_mem (Ideal.mul_mem_right _ _ (by rw [← pow_two]; exact hf)) ?_
    exact Ideal.mul_mem_mul
      (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hX i)) (hX j)

/-- An element of the maximal ideal whose derivatives along all axes vanish lies in
the square of the maximal ideal. -/
theorem mem_sq_of_germJet (b : AffineGerm k n)
    (hb : b ∈ IsLocalRing.maximalIdeal (AffineGerm k n))
    (hd : ∀ i, (germJet k n i b).snd = 0) :
    b ∈ IsLocalRing.maximalIdeal (AffineGerm k n) ^ 2 := by
  obtain ⟨⟨g, h⟩, rfl⟩ := IsLocalization.mk'_surjective (idealOfVars (Fin n) k).primeCompl b
  dsimp only at hb ⊢
  have hspec := IsLocalization.mk'_spec (AffineGerm k n) g h
  have hcc := constantCoeff_eq_zero_of_mk'_mem k n g h hb
  have hlin : ∀ i, coeff (Finsupp.single i 1) g = 0 := by
    intro i
    have e := congrArg (germJet k n i) hspec
    rw [map_mul, germJet_algebraMap, germJet_algebraMap] at e
    have hb0 : germJet k n i (IsLocalization.mk' (AffineGerm k n) g h) = 0 :=
      TrivSqZeroExt.ext (fst_germJet_of_mem k n i hb) (hd i)
    rw [hb0, zero_mul] at e
    rw [← snd_axisJet k n i, ← e]
    rfl
  have hg : g ∈ idealOfVars (Fin n) k ^ 2 := by
    have := sub_linear_mem_sq k n g
    simpa [hcc, hlin] using this
  have hmap : algebraMap _ (AffineGerm k n) g ∈ IsLocalRing.maximalIdeal (AffineGerm k n) ^ 2 := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hg
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ hmap

end Specialization

end Brent
