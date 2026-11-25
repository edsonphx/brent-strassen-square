import Brent.AffineGerm
import Brent.EmbeddingDimension
import Brent.LocalHomDimension

/-!
# Lower bounds for the local dimension at an arbitrary solution

`Brent.LowerBound` proves `dim ≥ 197` at the recursive point from one exact 197-parameter family
over the germ `k[t₁,…,tₙ]_(t)`. This file states the same argument for any solution `q` and any
`n`: an exact family over the germ whose value at the origin is `q` and whose `n` first-order
derivatives are linearly independent gives `n ≤ dim 𝒪_q`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.GermLower

variable (k : Type) [Field k] (n : ℕ)

/-- The germ of the `n`-dimensional parameter space. -/
abbrev Germ := AffineGerm k n

noncomputable def param (i : Fin n) : Germ k n :=
  algebraMap (MvPolynomial (Fin n) k) (Germ k n) (X i)

/-- Evaluation at the origin of the parameter space. -/
noncomputable def residue : Germ k n →+* k :=
  IsLocalization.lift (M := (idealOfVars (Fin n) k).primeCompl) (g := constantCoeff) fun g =>
    isUnit_iff_ne_zero.mpr fun h => g.2 ((mem_idealOfVars_iff k n g).mpr h)

theorem residue_algebraMap (g : MvPolynomial (Fin n) k) :
    residue k n (algebraMap _ (Germ k n) g) = constantCoeff g :=
  IsLocalization.lift_eq _ _

theorem algebraMap_germ (c : k) :
    algebraMap k (Germ k n) c = algebraMap (MvPolynomial (Fin n) k) (Germ k n) (C c) := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (Germ k n), algebraMap_eq]

@[simp] theorem residue_param (i : Fin n) : residue k n (param k n i) = 0 := by
  simp [param, residue_algebraMap]

@[simp] theorem residue_algebraMap_k (c : k) : residue k n (algebraMap k (Germ k n) c) = c := by
  rw [algebraMap_germ, residue_algebraMap, constantCoeff_C]

theorem residue_eq_zero_of_mem {b : Germ k n} (hb : b ∈ maximalIdeal (Germ k n)) :
    residue k n b = 0 := by
  have hle : maximalIdeal (Germ k n) ≤ RingHom.ker (residue k n) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, residue_algebraMap]
    exact (mem_idealOfVars_iff k n g).mp hg
  exact hle hb

theorem isUnit_of_residue_ne_zero {b : Germ k n} (h : residue k n b ≠ 0) : IsUnit b := by
  by_contra hu
  exact h (residue_eq_zero_of_mem k n ((mem_maximalIdeal _).mpr hu))

theorem germJet_param (i j : Fin n) :
    germJet k n j (param k n i) = if i = j then DualNumber.eps else 0 := by
  simp [param, germJet_algebraMap, axisJet]

theorem germJet_algebraMap_k (j : Fin n) (c : k) :
    germJet k n j (algebraMap k (Germ k n) c) = algebraMap k (DualNumber k) c := by
  rw [algebraMap_germ, germJet_algebraMap]
  simp [axisJet]

section GermMatrix

variable {α : Type} [Fintype α] [DecidableEq α]

/-- `1 + Σᵢ tᵢ Eᵢ` over the parameter germ. -/
noncomputable def germMatrix (E : Fin n → Matrix α α k) : Matrix α α (Germ k n) :=
  1 + ∑ i, param k n i • (E i).map (algebraMap k (Germ k n))

theorem germMatrix_apply (E : Fin n → Matrix α α k) (a b : α) :
    germMatrix k n E a b = (1 : Matrix α α (Germ k n)) a b +
      ∑ i, param k n i * algebraMap k (Germ k n) (E i a b) := by
  simp [germMatrix, Matrix.sum_apply]

theorem map_residue_germMatrix (E : Fin n → Matrix α α k) :
    (germMatrix k n E).map (residue k n) = 1 := by
  ext a b
  rw [Matrix.map_apply, germMatrix_apply, map_add, map_sum]
  simp [Matrix.one_apply, apply_ite (residue k n)]

theorem isUnit_germMatrix (E : Fin n → Matrix α α k) : IsUnit (germMatrix k n E) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_residue_ne_zero
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_residue_germMatrix, Matrix.det_one]
  exact one_ne_zero

theorem germJet_germMatrix (E : Fin n → Matrix α α k) (j : Fin n) (a b : α) :
    germJet k n j (germMatrix k n E a b) = ⟨(1 : Matrix α α k) a b, E j a b⟩ := by
  rw [germMatrix_apply, map_add, map_sum]
  simp only [map_mul, germJet_param, germJet_algebraMap_k, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply TrivSqZeroExt.ext
  · by_cases h : a = b <;> simp [Matrix.one_apply, h, TrivSqZeroExt.algebraMap_eq_inl]
  · by_cases h : a = b <;> simp [Matrix.one_apply, h, TrivSqZeroExt.algebraMap_eq_inl]

/-- `1 + Σᵢ tᵢ eᵢ` over the parameter germ. -/
noncomputable def germScalar (e : Fin n → k) : Germ k n :=
  1 + ∑ i, param k n i * algebraMap k (Germ k n) (e i)

theorem residue_germScalar (e : Fin n → k) : residue k n (germScalar k n e) = 1 := by
  simp [germScalar, map_sum]

theorem isUnit_germScalar (e : Fin n → k) : IsUnit (germScalar k n e) :=
  isUnit_of_residue_ne_zero k n (by rw [residue_germScalar]; exact one_ne_zero)

theorem germJet_germScalar (e : Fin n → k) (j : Fin n) :
    germJet k n j (germScalar k n e) = ⟨1, e j⟩ := by
  rw [germScalar, map_add, map_sum]
  simp only [map_mul, germJet_param, germJet_algebraMap_k, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one]
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end GermMatrix

section Pull

variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  (q : Decomposition k α ι) (hq : q.Solves)
  (fam : Decomposition (Germ k n) α ι) (hfam : fam.Solves)
  (hres : ∀ x, residue k n (fam.coordinates x) = q.coordinates x)

/-- Polynomial functions pulled back along the family. -/
noncomputable def pullPoly : MvPolynomial (Variable α ι) k →+* Germ k n :=
  eval₂Hom (algebraMap k (Germ k n)) fam.coordinates

include hfam in
theorem pullPoly_equation (a b c : α × α) :
    pullPoly k n fam (equation k α ι a b c) = 0 := by
  have hs := hfam a b c
  simp only [pullPoly, equation, map_sub, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C]
  rw [sub_eq_zero]
  simp only [Decomposition.entry] at hs
  convert hs using 1
  simp [matrixMultiplicationEntry, apply_ite (algebraMap k (Germ k n))]

include hfam in
theorem brentIdeal_le_ker : brentIdeal k α ι ≤ RingHom.ker (pullPoly k n fam) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  exact pullPoly_equation k n fam hfam a b c

noncomputable def pullQuot : CoordinateRing k α ι →+* Germ k n :=
  Ideal.Quotient.lift _ (pullPoly k n fam) fun _ hp => brentIdeal_le_ker k n fam hfam hp

include hres in
theorem residue_pullQuot :
    (residue k n).comp (pullQuot k n fam hfam) = pointEvaluation q hq := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [pullQuot, pullPoly, pointEvaluation]
  · intro x
    simp only [RingHom.comp_apply, pullQuot, Ideal.Quotient.lift_mk, pullPoly, eval₂Hom_X']
    rw [hres]
    simp [pointEvaluation]

include hres in
theorem pullQuot_unit (z : (pointIdeal q hq).primeCompl) :
    IsUnit (pullQuot k n fam hfam z) := by
  apply isUnit_of_residue_ne_zero
  rw [← RingHom.comp_apply, residue_pullQuot k n q hq fam hfam hres]
  exact fun h => z.2 h

/-- The local homomorphism from the Brent local ring at `q` to the parameter germ. -/
noncomputable def pull : PointLocalRing q hq →+* Germ k n :=
  IsLocalization.lift (M := (pointIdeal q hq).primeCompl)
    (pullQuot_unit k n q hq fam hfam hres)

theorem pull_algebraMap (z : CoordinateRing k α ι) :
    pull k n q hq fam hfam hres (algebraMap _ (PointLocalRing q hq) z) =
      pullQuot k n fam hfam z :=
  IsLocalization.lift_eq _ _

theorem pull_mem {a : PointLocalRing q hq} (ha : a ∈ maximalIdeal (PointLocalRing q hq)) :
    pull k n q hq fam hfam hres a ∈ maximalIdeal (Germ k n) := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (pointIdeal q hq).primeCompl a
  dsimp only at ha ⊢
  have hz : z ∈ pointIdeal q hq := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (PointLocalRing q hq) (pointIdeal q hq),
      ← IsLocalization.mk'_spec (PointLocalRing q hq) z s]
    exact Ideal.mul_mem_right _ _ ha
  have hspec := congrArg (pull k n q hq fam hfam hres)
    (IsLocalization.mk'_spec (PointLocalRing q hq) z s)
  rw [map_mul, pull_algebraMap, pull_algebraMap] at hspec
  have hres' := congrArg (residue k n) hspec
  rw [map_mul, ← RingHom.comp_apply (residue k n) (pullQuot k n fam hfam),
    ← RingHom.comp_apply (residue k n) (pullQuot k n fam hfam),
    residue_pullQuot k n q hq fam hfam hres] at hres'
  have hz0 : pointEvaluation q hq z = 0 := hz
  have hs0 : pointEvaluation q hq s ≠ 0 := fun h => s.2 h
  rw [hz0] at hres'
  have : residue k n (pull k n q hq fam hfam hres
      (IsLocalization.mk' (PointLocalRing q hq) z s)) = 0 :=
    (mul_eq_zero.mp hres').resolve_right hs0
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := (hu.map (residue k n)).ne_zero
  contradiction

instance pull_isLocalHom : IsLocalHom (pull k n q hq fam hfam hres) where
  map_nonunit a ha := by
    by_contra hna
    exact (mem_maximalIdeal _).mp (pull_mem k n q hq fam hfam hres ((mem_maximalIdeal _).mpr hna)) ha

/-- The translated coordinate functions in the local ring at `q`. -/
noncomputable def coord (x : Variable α ι) : PointLocalRing q hq :=
  algebraMap _ (PointLocalRing q hq)
    (Ideal.Quotient.mk (brentIdeal k α ι) (X x - C (q.coordinates x)))

theorem coord_mem (x : Variable α ι) : coord k q hq x ∈ maximalIdeal (PointLocalRing q hq) := by
  rw [coord, IsLocalization.AtPrime.to_map_mem_maximal_iff (PointLocalRing q hq) (pointIdeal q hq)]
  change pointEvaluation q hq _ = 0
  simp [pointEvaluation]

theorem germJet_pull_coord (j : Fin n) (x : Variable α ι) :
    (germJet k n j (pull k n q hq fam hfam hres (coord k q hq x))).snd =
      (germJet k n j (fam.coordinates x)).snd := by
  rw [coord, pull_algebraMap]
  simp only [pullQuot, Ideal.Quotient.lift_mk, pullPoly, map_sub, eval₂Hom_X', eval₂Hom_C]
  rw [TrivSqZeroExt.snd_sub, germJet_algebraMap_k]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

include hfam hres in
set_option maxHeartbeats 1000000 in
/-- **Lower bound at an arbitrary solution.** An exact family over the `n`-parameter germ
through `q` with `n` linearly independent derivatives gives `n ≤ dim 𝒪_q`. -/
theorem le_pointLocalDimension (D : Matrix (Fin n) (Variable α ι) k)
    (hD : LinearIndependent k D.row)
    (hjet : ∀ j x, (germJet k n j (fam.coordinates x)).snd = D j x) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (PointLocalRing q hq) := by
  suffices key : ringKrullDim (Germ k n) ≤ ringKrullDim (PointLocalRing q hq) by
    exact (le_ringKrullDim_affineGerm k n).trans key
  refine ringKrullDim_le_of_maximalIdeal_le (A := PointLocalRing q hq) (B := Germ k n)
    (pull k n q hq fam hfam hres) ?_
  have hsurj : Function.Surjective D.mulVecLin := by
    have hrank : D.rank = n := by
      rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hD, Fintype.card_fin]
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  have hmB : maximalIdeal (Germ k n) = Ideal.span (Set.range (param k n)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  refine hmB.le.trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨a, ha⟩ := hsurj (Pi.single j 1)
  let y : Variable α ι → PointLocalRing q hq := fun l => coord k q hq l
  let comb : Germ k n := ∑ l, algebraMap k (Germ k n) (a l) * pull k n q hq fam hfam hres (y l)
  have hcomb : comb ∈ (maximalIdeal (PointLocalRing q hq)).map (pull k n q hq fam hfam hres) := by
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    exact coord_mem k q hq _
  have hdiff : param k n j - comb ∈ maximalIdeal (Germ k n) ^ 2 := by
    apply mem_sq_of_germJet
    · refine Ideal.sub_mem _ (hmB ▸ Ideal.subset_span ⟨j, rfl⟩) ?_
      exact Ideal.sum_mem _ fun l _ =>
        Ideal.mul_mem_left _ _ (pull_mem k n q hq fam hfam hres (coord_mem k q hq _))
    · intro i
      have hai : ∑ l, D i l * a l = (Pi.single j (1 : k) : Fin n → k) i := by
        have h := congrFun ha i
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h
        exact h
      have hterm : ∀ l, (germJet k n i (algebraMap k (Germ k n) (a l) *
          pull k n q hq fam hfam hres (y l))).snd = D i l * a l := by
        intro l
        rw [map_mul, germJet_algebraMap_k, TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_mul,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero, germJet_pull_coord,
          hjet, mul_comm]
      rw [map_sub, TrivSqZeroExt.snd_sub, germJet_param, map_sum, TrivSqZeroExt.snd_sum]
      simp only [hterm]
      rw [hai]
      by_cases h : j = i
      · subst h; simp
      · simp [h, Ne.symm h]
  have hsum : param k n j = comb + (param k n j - comb) := by ring
  rw [SetLike.mem_coe, hsum]
  exact Submodule.add_mem_sup hcomb hdiff

end Pull

end Brent.GermLower
