import Brent.AffineGerm
import Brent.KernelCheck.FamilyQuadratics
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The lower bound `dim ≥ 197`

The 197 independent exact chart directions of `chart_independent_derivatives` are
combined into one exact 197-parameter family over the germ `B = k[t₁,…,t₁₉₇]_(t)`.
This gives a local homomorphism `ψ` from the Brent local ring to `B`. The kernel-checked
independence of the 197 derivatives shows that `ψ` is surjective on cotangent spaces,
so `ringKrullDim_le_of_maximalIdeal_le` gives `197 ≤ dim B ≤ dim A`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.LowerBound

open TangentData

variable (k : Type) [Field k]

/-- The germ of the 197-dimensional parameter space. -/
abbrev Germ := AffineGerm k 197

noncomputable def param (i : Fin 197) : Germ k :=
  algebraMap (MvPolynomial (Fin 197) k) (Germ k) (X i)

/-- Evaluation at the origin of the parameter space. -/
noncomputable def residue : Germ k →+* k :=
  IsLocalization.lift (M := (idealOfVars (Fin 197) k).primeCompl) (g := constantCoeff) fun g =>
    isUnit_iff_ne_zero.mpr fun h => g.2 ((mem_idealOfVars_iff k 197 g).mpr h)

theorem residue_algebraMap (g : MvPolynomial (Fin 197) k) :
    residue k (algebraMap _ (Germ k) g) = constantCoeff g :=
  IsLocalization.lift_eq _ _

theorem algebraMap_germ (c : k) :
    algebraMap k (Germ k) c = algebraMap (MvPolynomial (Fin 197) k) (Germ k) (C c) := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 197) k) (Germ k), algebraMap_eq]

@[simp] theorem residue_param (i : Fin 197) : residue k (param k i) = 0 := by
  simp [param, residue_algebraMap]

@[simp] theorem residue_algebraMap_k (c : k) : residue k (algebraMap k (Germ k) c) = c := by
  rw [algebraMap_germ, residue_algebraMap, constantCoeff_C]

theorem residue_eq_zero_of_mem {b : Germ k} (hb : b ∈ maximalIdeal (Germ k)) :
    residue k b = 0 := by
  have hle : maximalIdeal (Germ k) ≤ RingHom.ker (residue k) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, residue_algebraMap]
    exact (mem_idealOfVars_iff k 197 g).mp hg
  exact hle hb

theorem isUnit_of_residue_ne_zero {b : Germ k} (h : residue k b ≠ 0) : IsUnit b := by
  by_contra hu
  exact h (residue_eq_zero_of_mem k ((mem_maximalIdeal _).mpr hu))

theorem param_mem (i : Fin 197) : param k i ∈ maximalIdeal (Germ k) := by
  rw [param, IsLocalization.AtPrime.to_map_mem_maximal_iff (Germ k) (idealOfVars (Fin 197) k)]
  exact Ideal.subset_span ⟨i, rfl⟩

theorem germJet_param (i j : Fin 197) :
    germJet k 197 j (param k i) = if i = j then DualNumber.eps else 0 := by
  simp [param, germJet_algebraMap, axisJet]

theorem germJet_algebraMap_k (j : Fin 197) (c : k) :
    germJet k 197 j (algebraMap k (Germ k) c) = algebraMap k (DualNumber k) c := by
  rw [algebraMap_germ, germJet_algebraMap]
  simp [axisJet]

section GermMatrix

variable {α : Type} [Fintype α] [DecidableEq α]

/-- `1 + Σᵢ tᵢ Eᵢ` over the parameter germ. -/
noncomputable def germMatrix (E : Fin 197 → Matrix α α k) : Matrix α α (Germ k) :=
  1 + ∑ i, param k i • (E i).map (algebraMap k (Germ k))

theorem germMatrix_apply (E : Fin 197 → Matrix α α k) (a b : α) :
    germMatrix k E a b = (1 : Matrix α α (Germ k)) a b +
      ∑ i, param k i * algebraMap k (Germ k) (E i a b) := by
  simp [germMatrix, Matrix.sum_apply]

theorem map_residue_germMatrix (E : Fin 197 → Matrix α α k) :
    (germMatrix k E).map (residue k) = 1 := by
  ext a b
  rw [Matrix.map_apply, germMatrix_apply, map_add, map_sum]
  simp [Matrix.one_apply, apply_ite (residue k)]

theorem isUnit_germMatrix (E : Fin 197 → Matrix α α k) : IsUnit (germMatrix k E) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_residue_ne_zero
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_residue_germMatrix, Matrix.det_one]
  exact one_ne_zero

theorem germJet_germMatrix (E : Fin 197 → Matrix α α k) (j : Fin 197) (a b : α) :
    germJet k 197 j (germMatrix k E a b) = ⟨(1 : Matrix α α k) a b, E j a b⟩ := by
  rw [germMatrix_apply, map_add, map_sum]
  simp only [map_mul, germJet_param, germJet_algebraMap_k, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply TrivSqZeroExt.ext
  · by_cases h : a = b <;> simp [Matrix.one_apply, h, TrivSqZeroExt.algebraMap_eq_inl]
  · by_cases h : a = b <;> simp [Matrix.one_apply, h, TrivSqZeroExt.algebraMap_eq_inl]

/-- `1 + Σᵢ tᵢ eᵢ` over the parameter germ. -/
noncomputable def germScalar (e : Fin 197 → k) : Germ k :=
  1 + ∑ i, param k i * algebraMap k (Germ k) (e i)

theorem residue_germScalar (e : Fin 197 → k) : residue k (germScalar k e) = 1 := by
  simp [germScalar, map_sum]

theorem isUnit_germScalar (e : Fin 197 → k) : IsUnit (germScalar k e) :=
  isUnit_of_residue_ne_zero k (by rw [residue_germScalar]; exact one_ne_zero)

theorem germJet_germScalar (e : Fin 197 → k) (j : Fin 197) :
    germJet k 197 j (germScalar k e) = ⟨1, e j⟩ := by
  rw [germScalar, map_add, map_sum]
  simp only [map_mul, germJet_param, germJet_algebraMap_k, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one]
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end GermMatrix

/-- The left-chart frame directions used in `chart_independent_derivatives`. -/
def dir (i : Fin 197) : Fin 251 := ⟨i.val, by omega⟩

theorem castOrigin_base' (i : Fin 251) :
    (castOrigin k i).map (Jets.forget k) = FamilyParameters.one k := by
  have comp : (Jets.forget k).comp (Jets.map Int (Int.castRingHom k)) =
      (Int.castRingHom k).comp (Jets.forget Int) := rfl
  rw [castOrigin, FamilyParameters.map_comp, comp, ← FamilyParameters.map_comp,
    frameOrigin_base, FamilyParameters.map_one]

noncomputable def tangentGlobal (g : Fin 3) (i : Fin 197) : Matrix SquareVertex SquareVertex k :=
  fun a b => (((castOrigin k (dir i)).global g).val a b).snd

noncomputable def tangentBlock (s : Fin 7) (g : Fin 3) (i : Fin 197) : Matrix (Fin 2) (Fin 2) k :=
  fun a b => (((castOrigin k (dir i)).block s g).val a b).snd

noncomputable def tangentScale (s : SquareSummand) (c : Fin 2) (i : Fin 197) : k :=
  (((castOrigin k (dir i)).scale s c).val).snd

/-- The exact 197-parameter family over the parameter germ. -/
noncomputable def multi : FamilyParameters (Germ k) :=
  ⟨fun g => (isUnit_germMatrix k (tangentGlobal k g)).unit,
   fun s g => (isUnit_germMatrix k (tangentBlock k s g)).unit,
   fun s c => (isUnit_germScalar k (tangentScale k s c)).unit⟩

theorem multi_residue : (multi k).map (residue k) = FamilyParameters.one k := by
  simp only [multi, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext
    exact map_residue_germMatrix k _
  · funext s g; apply Units.ext
    exact map_residue_germMatrix k _
  · funext s c; apply Units.ext
    exact residue_germScalar k _

theorem multi_germJet (j : Fin 197) :
    (multi k).map (germJet k 197 j) = castOrigin k (dir j) := by
  have hb := castOrigin_base' k (dir j)
  simp only [FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq] at hb
  change _ = FamilyParameters.mk (castOrigin k (dir j)).global (castOrigin k (dir j)).block
    (castOrigin k (dir j)).scale
  simp only [multi, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((castOrigin k (dir j)).global g).val a b).fst =
        (1 : Matrix SquareVertex SquareVertex k) a b :=
      congrArg (fun u : (Matrix SquareVertex SquareVertex k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun hb.1 g)
    change germJet k 197 j (germMatrix k (tangentGlobal k g) a b) = _
    rw [germJet_germMatrix]
    exact TrivSqZeroExt.ext h1.symm rfl
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((castOrigin k (dir j)).block s g).val a b).fst =
        (1 : Matrix (Fin 2) (Fin 2) k) a b :=
      congrArg (fun u : (Matrix (Fin 2) (Fin 2) k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun (congrFun hb.2.1 s) g)
    change germJet k 197 j (germMatrix k (tangentBlock k s g) a b) = _
    rw [germJet_germMatrix]
    exact TrivSqZeroExt.ext h1.symm rfl
  · funext s c; apply Units.ext
    have h1 : (((castOrigin k (dir j)).scale s c).val).fst = 1 :=
      congrArg (fun u : kˣ => (u : k)) (congrFun (congrFun hb.2.2 s) c)
    change germJet k 197 j (germScalar k (tangentScale k s c)) = _
    rw [germJet_germScalar]
    exact TrivSqZeroExt.ext h1.symm rfl

/-- The exact solution over the parameter germ. -/
noncomputable def family : Decomposition (Germ k) SquareVertex SquareSummand :=
  (multi k).value true

theorem coordinates_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (d : Decomposition R SquareVertex SquareSummand) (x : Variable SquareVertex SquareSummand) :
    (d.map f).coordinates x = f (d.coordinates x) := by
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

theorem family_residue (x : Variable SquareVertex SquareSummand) :
    residue k ((family k).coordinates x) = (strassenSquare k).coordinates x := by
  rw [← coordinates_map, family, FamilyParameters.value_map, multi_residue,
    FamilyParameters.value_one]

theorem family_germJet (j : Fin 197) (x : Variable SquareVertex SquareSummand) :
    (germJet k 197 j ((family k).coordinates x)).snd =
      ((castOrigin k (dir j)).value true).tangentPart.coordinates x := by
  rw [← coordinates_map, family, FamilyParameters.value_map, multi_germJet]
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

/-- Polynomial functions pulled back along the family. -/
noncomputable def pullPoly : MvPolynomial (Variable SquareVertex SquareSummand) k →+* Germ k :=
  eval₂Hom (algebraMap k (Germ k)) (family k).coordinates

theorem pullPoly_equation (a b c : SquareVertex × SquareVertex) :
    pullPoly k (equation k SquareVertex SquareSummand a b c) = 0 := by
  have hs := FamilyParameters.value_solves true (multi k) a b c
  simp only [pullPoly, equation, map_sub, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C]
  rw [sub_eq_zero]
  change (family k).entry a b c = _ at hs
  simp only [Decomposition.entry] at hs
  convert hs using 1
  simp [matrixMultiplicationEntry, apply_ite (algebraMap k (Germ k))]

noncomputable def pullQuot : SquareCoordinateRing k →+* Germ k :=
  Ideal.Quotient.lift _ (pullPoly k) <| by
    intro p hp
    have hle : brentIdeal k SquareVertex SquareSummand ≤ RingHom.ker (pullPoly k) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨a, b, c⟩, rfl⟩
      exact pullPoly_equation k a b c
    exact hle hp

theorem residue_pullQuot : (residue k).comp (pullQuot k) = squareEvaluation k := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [pullQuot, pullPoly, squareEvaluation, pointEvaluation]
  · intro x
    simp only [RingHom.comp_apply, pullQuot, Ideal.Quotient.lift_mk, pullPoly, eval₂Hom_X']
    rw [family_residue]
    simp [squareEvaluation, pointEvaluation]

theorem pullQuot_unit (z : (squareMaximalIdeal k).primeCompl) : IsUnit (pullQuot k z) := by
  apply isUnit_of_residue_ne_zero
  rw [← RingHom.comp_apply, residue_pullQuot]
  exact z.2

/-- The local homomorphism from the Brent local ring to the parameter germ. -/
noncomputable def pull : SquareLocalRing k →+* Germ k :=
  IsLocalization.lift (M := (squareMaximalIdeal k).primeCompl) (pullQuot_unit k)

theorem pull_algebraMap (z : SquareCoordinateRing k) :
    pull k (algebraMap _ (SquareLocalRing k) z) = pullQuot k z :=
  IsLocalization.lift_eq _ _

theorem pull_mem {a : SquareLocalRing k} (ha : a ∈ maximalIdeal (SquareLocalRing k)) :
    pull k a ∈ maximalIdeal (Germ k) := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (squareMaximalIdeal k).primeCompl a
  dsimp only at ha ⊢
  have hz : z ∈ squareMaximalIdeal k := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (SquareLocalRing k) (squareMaximalIdeal k),
      ← IsLocalization.mk'_spec (SquareLocalRing k) z s]
    exact Ideal.mul_mem_right _ _ ha
  have hspec := congrArg (pull k) (IsLocalization.mk'_spec (SquareLocalRing k) z s)
  rw [map_mul, pull_algebraMap, pull_algebraMap] at hspec
  have hres := congrArg (residue k) hspec
  rw [map_mul, ← RingHom.comp_apply (residue k) (pullQuot k), ← RingHom.comp_apply (residue k)
    (pullQuot k), residue_pullQuot] at hres
  have hz0 : squareEvaluation k z = 0 := hz
  have hs0 : squareEvaluation k s ≠ 0 := s.2
  rw [hz0] at hres
  have : residue k (pull k (IsLocalization.mk' (SquareLocalRing k) z s)) = 0 :=
    (mul_eq_zero.mp hres).resolve_right hs0
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := (hu.map (residue k)).ne_zero
  contradiction

instance pull_isLocalHom : IsLocalHom (pull k) where
  map_nonunit a ha := by
    by_contra hna
    exact (mem_maximalIdeal _).mp (pull_mem k ((mem_maximalIdeal _).mpr hna)) ha

/-- The translated coordinate functions in the Brent local ring. -/
noncomputable def coord (x : Variable SquareVertex SquareSummand) : SquareLocalRing k :=
  algebraMap _ (SquareLocalRing k)
    (Ideal.Quotient.mk (brentIdeal k SquareVertex SquareSummand)
      (X x - C ((strassenSquare k).coordinates x)))

theorem coord_mem (x : Variable SquareVertex SquareSummand) :
    coord k x ∈ maximalIdeal (SquareLocalRing k) := by
  rw [coord, IsLocalization.AtPrime.to_map_mem_maximal_iff (SquareLocalRing k) (squareMaximalIdeal k)]
  change squareEvaluation k _ = 0
  simp [squareEvaluation, pointEvaluation]

theorem germJet_pull_coord (j : Fin 197) (x : Variable SquareVertex SquareSummand) :
    (germJet k 197 j (pull k (coord k x))).snd =
      ((castOrigin k (dir j)).value true).tangentPart.coordinates x := by
  rw [coord, pull_algebraMap]
  simp only [pullQuot, Ideal.Quotient.lift_mk, pullPoly, map_sub, eval₂Hom_X', eval₂Hom_C]
  rw [TrivSqZeroExt.snd_sub, family_germJet, germJet_algebraMap_k]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- The 197 chart derivatives as a matrix. -/
noncomputable def derivative : Matrix (Fin 197) (Fin 2352) k := fun i j =>
  ((castOrigin k (dir i)).value true).tangentPart.coordinates (squareVariableNumber.symm j)

theorem derivative_surjective : Function.Surjective (derivative k).mulVecLin := by
  have hli : LinearIndependent k (derivative k).row := chart_independent_derivatives k true
  have hrank : (derivative k).rank = 197 := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  exact hrank

set_option maxHeartbeats 1000000 in
/-- **Lower bound.** The local dimension at the Strassen-square point is at least 197. -/
theorem le_squareLocalDimension : (197 : WithBot ℕ∞) ≤ squareLocalDimension k := by
  suffices key : ringKrullDim (Germ k) ≤ ringKrullDim (SquareLocalRing k) by
    exact (le_ringKrullDim_affineGerm k 197).trans key
  refine ringKrullDim_le_of_maximalIdeal_le (A := SquareLocalRing k) (B := Germ k) (pull k) ?_
  -- The maximal ideal of the germ is generated by the parameters.
  have hmB : maximalIdeal (Germ k) = Ideal.span (Set.range (param k)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  refine hmB.le.trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨a, ha⟩ := derivative_surjective k (Pi.single j 1)
  let y : Fin 2352 → SquareLocalRing k := fun l => coord k (squareVariableNumber.symm l)
  let comb : Germ k := ∑ l, algebraMap k (Germ k) (a l) * pull k (y l)
  have hcomb : comb ∈ (maximalIdeal (SquareLocalRing k)).map (pull k) := by
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    exact coord_mem k _
  have hdiff : param k j - comb ∈ maximalIdeal (Germ k) ^ 2 := by
    apply mem_sq_of_germJet
    · refine Ideal.sub_mem _ (hmB ▸ Ideal.subset_span ⟨j, rfl⟩) ?_
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (pull_mem k (coord_mem k _))
    · intro i
      have hai : ∑ l, derivative k i l * a l = (Pi.single j (1 : k) : Fin 197 → k) i := by
        have h := congrFun ha i
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h
        exact h
      have hterm : ∀ l, (germJet k 197 i (algebraMap k (Germ k) (a l) * pull k (y l))).snd =
          derivative k i l * a l := by
        intro l
        rw [map_mul, germJet_algebraMap_k, TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_mul,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero, germJet_pull_coord,
          mul_comm]
        rfl
      rw [map_sub, TrivSqZeroExt.snd_sub, germJet_param, map_sum, TrivSqZeroExt.snd_sum]
      simp only [hterm]
      rw [hai]
      by_cases h : j = i
      · subst h; simp
      · simp [h, Ne.symm h]
  have hsum : param k j = comb + (param k j - comb) := by ring
  rw [SetLike.mem_coe, hsum]
  exact Submodule.add_mem_sup hcomb hdiff

end Brent.LowerBound
