import Brent.Formal.OrbitDimension
import Brent.Formal.Component
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing

/-! Algebraic orbit closure, not just the image of its differential.
The actual orbit comorphism is obtained by turning off all block parameters
in the generic family. The proof of density below uses the same localization
and specialization as the family-closure proof. -/

open scoped BigOperators nonZeroDivisors
open MvPolynomial

namespace Brent.Formal.OrbitClosure

open Brent Brent.Formal Brent.Formal.FamilyClosure

variable (k : Type) [Field k]

def trivialBlocks {S : Type} [CommRing S] (p : FamilyParameters S) : FamilyParameters S :=
  ⟨p.global, fun _ _ => 1, p.scale⟩

theorem trivialBlocks_trivial {S : Type} [CommRing S] (p : FamilyParameters S) :
    BlockTrivial (trivialBlocks p) := fun _ _ => rfl

theorem trivialBlocks_map {S T : Type} [CommRing S] [CommRing T]
    (h : S →+* T) (p : FamilyParameters S) :
    (trivialBlocks p).map h = trivialBlocks (p.map h) := by
  cases p
  simp [trivialBlocks, FamilyParameters.map]

theorem orbitValue_map {S T : Type} [CommRing S] [CommRing T]
    (h : S →+* T) (p : FamilyParameters S) :
    (orbitValue p).map h = orbitValue (p.map h) := by
  calc
    (orbitValue p).map h = ((trivialBlocks p).value false).map h := by
      rw [value_of_blockTrivial false (trivialBlocks_trivial p)] <;> rfl
    _ = ((trivialBlocks p).map h).value false := FamilyParameters.value_map _ _ _
    _ = orbitValue (p.map h) := by
      rw [trivialBlocks_map, value_of_blockTrivial false (trivialBlocks_trivial _)] <;> rfl

/-- The actual group orbit: arbitrary invertible global factors and term scalings. -/
def image : Set (Affine k) := Set.range fun p : FamilyParameters k => (orbitValue p).coordinates

def orbitClosure : Set (Affine k) := closure (image k)

/-- The generic orbit comorphism, in the same domain as the generic family. -/
noncomputable def orbitPsi : MvPolynomial Var k →ₐ[k] R k :=
  aeval (orbitValue (generic k)).coordinates

theorem evS_orbitPsi {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (f : MvPolynomial Var k) :
    Component.evS k p (orbitPsi k f) = aeval (orbitValue p).coordinates f := by
  have hc : (orbitValue p).coordinates = fun x =>
      Component.evS k p ((orbitValue (generic k)).coordinates x) := by
    funext x
    rw [← LowerBound.coordinates_map (Component.evS k p) (orbitValue (generic k)) x,
      orbitValue_map, Component.generic_map_evS]
  rw [hc, orbitPsi]
  induction f using MvPolynomial.induction_on with
  | C c => rw [aeval_C, aeval_C, Component.evS_algebraMap_k]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf => simp only [map_mul, hf, aeval_X]

theorem evAt_orbitPsi (a : GrpIdx → k) (ha : eval a (D k) ≠ 0)
    (f : MvPolynomial Var k) :
    evAt k a ha (orbitPsi k f) =
      eval (orbitValue ((generic k).map (evAt k a ha))).coordinates f := by
  have hc : (orbitValue ((generic k).map (evAt k a ha))).coordinates =
      fun x => evAt k a ha ((orbitValue (generic k)).coordinates x) := by
    funext x
    rw [← LowerBound.coordinates_map, orbitValue_map]
  rw [hc, orbitPsi]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, eval_C]
    rw [IsScalarTower.algebraMap_apply k (P k) (R k), evAt_algebraMap,
      MvPolynomial.algebraMap_eq, eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf => simp only [map_mul, hf, aeval_X, eval_X]

/-- Polynomial relations on the actual algebraic orbit equal the generic kernel. -/
theorem orbit_vanishes_iff [Infinite k] (f : MvPolynomial Var k) :
    (∀ v ∈ image k, eval v f = 0) ↔ orbitPsi k f = 0 := by
  constructor
  · intro h
    obtain ⟨⟨g, ⟨_, n, rfl⟩⟩, hg⟩ := IsLocalization.surj (Submonoid.powers (D k)) (orbitPsi k f)
    simp only at hg
    have hzero : ∀ a : GrpIdx → k, eval a (D k) ≠ 0 → eval a g = 0 := by
      intro a ha
      have h1 := congrArg (evAt k a ha) hg
      rw [map_mul, evAt_orbitPsi, evAt_algebraMap, evAt_algebraMap,
        h _ ⟨_, rfl⟩, zero_mul] at h1
      exact h1.symm
    have hg0 := Brent.Equidim.eq_zero_of_eval_eq_zero_of_eval_ne_zero (D_ne_zero k) g hzero
    rw [hg0, map_zero] at hg
    have hu : IsUnit (algebraMap (P k) (R k) (D k ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (D k)).pow n
    exact (hu.mul_left_eq_zero).mp hg
  · rintro h _ ⟨p, rfl⟩
    have := evAt_orbitPsi k (entries k p) (eval_D_entries k p) f
    rw [h, map_zero, generic_map_entries] at this
    exact this.symm

noncomputable abbrev orbitIdeal : Ideal (MvPolynomial Var k) := RingHom.ker (orbitPsi k)

instance orbitIdeal_prime : (orbitIdeal k).IsPrime := RingHom.ker_isPrime _

/-- The ideal is exactly the vanishing ideal of the Zariski closure, not a
polynomial ideal defined only by a tangent calculation. -/
theorem orbitClosure_vanishingIdeal [Infinite k] :
    Component.vanishingIdeal k (orbitClosure k) = orbitIdeal k := by
  ext f
  rw [Component.mem_vanishingIdeal, RingHom.mem_ker, ← orbit_vanishes_iff]
  constructor
  · intro h v hv
    exact h v (subset_closure hv)
  · intro h v hv
    have hclosed : IsClosed (zeroLocus k ({f} : Set (MvPolynomial Var k))) := isClosed_zeroLocus k _
    have hsub : image k ⊆ zeroLocus k ({f} : Set (MvPolynomial Var k)) := by
      intro w hw g hg
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact h w hw
    exact closure_minimal hsub hclosed hv f (Set.mem_singleton f)

/-- A scalar matrix multiple, with its inverse given explicitly. -/
def scaledMatrix {S : Type} [CommRing S] (c : Sˣ)
    (A : (Matrix SquareVertex SquareVertex S)ˣ) : (Matrix SquareVertex SquareVertex S)ˣ where
  val := (c : S) • A.val
  inv := ((c⁻¹ : Sˣ) : S) • A.inv
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, A.val_inv]
    simp
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, A.inv_val]
    simp

/-- Central rescaling of the three global factors, compensated by the two
term scalings. This is an exact identity over any commutative ring. -/
def centralNormalize {S : Type} [CommRing S] (p : FamilyParameters S)
    (c : Fin 3 → Sˣ) : FamilyParameters S :=
  ⟨fun g => scaledMatrix (c g)⁻¹ (p.global g), fun _ _ => 1,
    fun s i => if i = 0 then p.scale s i * c 0 * (c 1)⁻¹
      else p.scale s i * c 1 * (c 2)⁻¹⟩

/-- Matrix products after scaling the left and right factors. -/
theorem scaled_product {S : Type} [CommRing S] (a b : S)
    (L M N : Matrix SquareVertex SquareVertex S) :
    (a • L) * M * (b • N) = (a*b) • (L*M*N) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  <;> congr 1 <;> ac_rfl

/-- Exact central gauge invariance, including the compensating term scales. -/
theorem centralNormalize_value {S : Type} [Field S] (p : FamilyParameters S)
    (c : Fin 3 → Sˣ) : orbitValue (centralNormalize p c) = orbitValue p := by
  let q := centralNormalize p c
  let d := strassenSquare S
  have hu (s : SquareSummand) (a b : SquareVertex) :
      (orbitValue q).u s (a,b) = (orbitValue p).u s (a,b) := by
    change (q.scale s 0).val *
      ((q.global 0).val.transpose * (fun i j => d.u s (i,j)) *
        (q.global 1).inv.transpose) a b =
      (p.scale s 0).val *
      ((p.global 0).val.transpose * (fun i j => d.u s (i,j)) *
        (p.global 1).inv.transpose) a b
    simp only [q, centralNormalize, scaledMatrix, if_pos rfl, inv_inv,
      Matrix.transpose_smul, scaled_product, Matrix.smul_apply, smul_eq_mul,
      Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero] <;> ring
  have hv (s : SquareSummand) (a b : SquareVertex) :
      (orbitValue q).v s (a,b) = (orbitValue p).v s (a,b) := by
    change (q.scale s 1).val *
      ((q.global 1).val.transpose * (fun i j => d.v s (i,j)) *
        (q.global 2).inv.transpose) a b =
      (p.scale s 1).val *
      ((p.global 1).val.transpose * (fun i j => d.v s (i,j)) *
        (p.global 2).inv.transpose) a b
    simp only [q, centralNormalize, scaledMatrix, show (1 : Fin 2) ≠ 0 by decide,
      if_false, inv_inv, Matrix.transpose_smul, scaled_product, Matrix.smul_apply,
      smul_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero] <;> ring
  have hw (s : SquareSummand) (a b : SquareVertex) :
      (orbitValue q).w s (a,b) = (orbitValue p).w s (a,b) := by
    change ↑((q.scale s 0)⁻¹) * ↑((q.scale s 1)⁻¹) *
      ((q.global 0).inv * (fun i j => d.w s (i,j)) * (q.global 2).val) a b =
      ↑((p.scale s 0)⁻¹) * ↑((p.scale s 1)⁻¹) *
      ((p.global 0).inv * (fun i j => d.w s (i,j)) * (p.global 2).val) a b
    simp only [q, centralNormalize, scaledMatrix, if_pos rfl,
      show (1 : Fin 2) ≠ 0 by decide, if_false, inv_inv, scaled_product,
      Matrix.smul_apply, smul_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero] <;> ring
  change orbitValue q = orbitValue p
  cases hq : orbitValue q with
  | mk u v w =>
    cases hp : orbitValue p with
    | mk u' v' w' =>
      rw [Decomposition.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> funext s x <;> obtain ⟨a,b⟩ := x
      · simpa only [hq, hp] using hu s a b
      · simpa only [hq, hp] using hv s a b
      · simpa only [hq, hp] using hw s a b

/-- Every unremoved parameter is among the 143 certified rows. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rowsA_cover : ∀ w : GIdx,
    (∀ g : Fin 3, w ≠ .inl (g, (1,1), (1,1))) → ∃ i : Fin 143, rowsA i = w := by
  decide +kernel

/-- Normalize each of the three chosen diagonal entries to one. -/
theorem centralNormalize_diagonal {S : Type} [Field S] (p : FamilyParameters S)
    (h : ∀ g, (p.global g).val (1,1) (1,1) ≠ 0) (g : Fin 3) :
    ((centralNormalize p (fun g => Units.mk0 _ (h g))).global g).val (1,1) (1,1) = 1 := by
  simp [centralNormalize, scaledMatrix, Matrix.smul_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val, h]

section Dimension

open Cardinal

abbrev OrbitRing := MvPolynomial Var k ⧸ orbitIdeal k

/-- The 143 centered coordinate functions are algebraically independent on
 the orbit, by the actual formal inverse theorem for the certified minor. -/
theorem orbit_trdeg_lower : (143 : Cardinal) ≤ Algebra.trdeg k (OrbitRing k) := by
  classical
  let q := orbParams (tS k) (centered_tS k)
  let b : Fin 143 → MvPowerSeries (Fin 143) k := fun i =>
    orbArg (tS k) (centered_tS k) (colsA i)
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (b i) = 0 :=
    fun i => constantCoeff_orbArg _ _
  have hM : (Matrix.of fun x v => MvPowerSeries.coeff
      (Finsupp.single ((Equiv.refl (Fin 143)).symm v) 1) (b x)) =
      (minor k).transpose := by
    ext x v
    simp only [Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply, b,
      coeff_orbArg_tS, Matrix.transpose_apply, minor]
  have hbij := subst_bijective_equiv (Equiv.refl (Fin 143)) hb0 (by
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, isUnit_iff_ne_zero]
    exact det_minor_ne_zero k)
  let hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  let F := MvPowerSeries.substAlgHom hsub
  let inc : MvPolynomial (Fin 143) k →ₐ[k] MvPowerSeries (Fin 143) k :=
    MvPolynomial.coeToMvPowerSeries.algHom k
  have hi : Function.Injective inc := by
    intro x y h
    apply MvPolynomial.coe_injective (Fin 143) k
    simpa [inc, MvPolynomial.coeToMvPowerSeries.algHom_apply] using h
  have he : aeval b = F.comp inc := by
    ext i
    simp [F, inc, MvPowerSeries.substAlgHom_X]
  have hind : AlgebraicIndependent k b := by
    rw [algebraicIndependent_iff_injective_aeval, he]
    exact hbij.1.comp hi
  let e : OrbitRing k →ₐ[k] MvPowerSeries (Fin 143) k :=
    Ideal.Quotient.liftₐ (orbitIdeal k) (aeval (orbitValue q).coordinates) fun f hf => by
      rw [← evS_orbitPsi, RingHom.mem_ker.mp hf, map_zero]
  let x : Fin 143 → OrbitRing k := fun i =>
    Ideal.Quotient.mk _ (X (colsA i) - C (pt k (colsA i)))
  have hx : e ∘ x = b := by
    funext i
    change e (Ideal.Quotient.mk _ (X (colsA i) - C (pt k (colsA i)))) = b i
    simp only [e, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, map_sub,
      aeval_X, aeval_C, b, orbArg, MvPowerSeries.algebraMap_apply]
    rw [value_of_blockTrivial false (fun _ _ => rfl)]
  have hxi : AlgebraicIndependent k x := AlgebraicIndependent.of_comp e (hx.symm ▸ hind)
  simpa using hxi.cardinalMk_le_trdeg

/-- A finite type domain has a Noether-normalizing dimension equal to its
 transcendence degree.  The Krull-dimension comparison is included here to
 avoid identifying a tangent rank with an algebraic dimension. -/
theorem finiteType_dim_trdeg (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] : ∃ n : ℕ,
      ringKrullDim B = (n : WithBot ℕ∞) ∧ Algebra.trdeg k B = (n : Cardinal) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  refine ⟨n, ?_, ?_⟩
  all_goals algebraize [g.toRingHom]
  all_goals haveI : Module.Finite (MvPolynomial (Fin n) k) B := hfin
  all_goals haveI : FaithfulSMul (MvPolynomial (Fin n) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    letI := hm
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
    have hm' : (m.under (MvPolynomial (Fin n) k)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    have h1 := Brent.Equidim.mvPolynomial_height_of_isMaximal k n _ hm'
    have h2 : m.height = n := by
      apply le_antisymm
      · rw [← h1]
        exact Brent.Equidim.height_le_height_under_of_isIntegral m
      · rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
          (m.under (MvPolynomial (Fin n) k)) m, h1]
        exact le_self_add
    rw [← Brent.Equidim.height_eq_ringKrullDim_of_isMaximal' (k := k) m, h2]
    rfl
  · haveI : Algebra.IsAlgebraic (MvPolynomial (Fin n) k) B :=
      ⟨fun b => (Algebra.IsIntegral.isIntegral b).isAlgebraic⟩
    have h := (IsTranscendenceBasis.mvPolynomial (Fin n) k).algebraMap_comp
      (A := B)
    simpa using h.cardinalMk_eq_trdeg.symm

/-- Entries of the normalized 143-coordinate chart. Missing slots are the
three fixed diagonal entries. -/
noncomputable def gaugeEntry (w : GIdx) : MvPolynomial (Fin 143) k :=
  match slot w with
  | some i => X i
  | none => 1

def parameterEntry {S : Type} [CommRing S] (p : FamilyParameters S) : GIdx → S
  | .inl (g,a,b) => (p.global g).val a b
  | .inr (s,i) => (p.scale s i).val

theorem aeval_gaugeEntry {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1)
    (w : GIdx) : aeval (fun i => parameterEntry p (rowsA i)) (gaugeEntry k w) =
      parameterEntry p w := by
  cases hs : slot w with
  | some i => simp [gaugeEntry, hs, slot_some hs]
  | none =>
    have hg : ∃ g : Fin 3, w = .inl (g,(1,1),(1,1)) := by
      by_contra hn
      obtain ⟨i,hi⟩ := rowsA_cover w (fun g he => hn ⟨g,he⟩)
      obtain ⟨j,hj⟩ := slot_rowsA i
      rw [hi, hs] at hj
      contradiction
    obtain ⟨g,rfl⟩ := hg
    simp [gaugeEntry, hs, parameterEntry, h]

noncomputable def gaugeMat (g : Fin 3) :
    Matrix SquareVertex SquareVertex (MvPolynomial (Fin 143) k) :=
  Matrix.of fun a b => gaugeEntry k (.inl (g,a,b))

noncomputable def gaugeScale (s : SquareSummand) (i : Fin 2) : MvPolynomial (Fin 143) k :=
  gaugeEntry k (.inr (s,i))

noncomputable def gaugeD : MvPolynomial (Fin 143) k :=
  (∏ g, (gaugeMat k g).det) * ∏ s, ∏ i, gaugeScale k s i

abbrev GaugeRing := Localization.Away (gaugeD k)

theorem aeval_gaugeMat {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1)
    (g : Fin 3) : (gaugeMat k g).map (aeval (fun i => parameterEntry p (rowsA i))) =
      (p.global g).val := by
  ext a b
  exact aeval_gaugeEntry k p h (.inl (g,a,b))

theorem aeval_gaugeD_isUnit {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1) :
    IsUnit (aeval (fun i => parameterEntry p (rowsA i)) (gaugeD k)) := by
  rw [gaugeD, map_mul, map_prod, map_prod]
  apply IsUnit.mul
  · apply IsUnit.prod_univ_iff.mpr
    intro g
    rw [RingHom.map_det, RingHom.mapMatrix_apply, aeval_gaugeMat k p h]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (p.global g).isUnit
  · apply IsUnit.prod_univ_iff.mpr
    intro s
    rw [map_prod]
    apply IsUnit.prod_univ_iff.mpr
    intro i
    rw [gaugeScale, aeval_gaugeEntry k p h]
    exact (p.scale s i).isUnit

theorem gaugeD_ne_zero : gaugeD k ≠ 0 := by
  have hu := aeval_gaugeD_isUnit k (FamilyParameters.one k)
    (fun g => by simp [FamilyParameters.one, Matrix.one_apply])
  intro hz
  rw [hz, map_zero] at hu
  exact not_isUnit_zero hu

instance gaugeRing_domain : IsDomain (GaugeRing k) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (gaugeD_ne_zero k))

theorem gauge_isUnit_of_dvd {f : MvPolynomial (Fin 143) k} (h : f ∣ gaugeD k) :
    IsUnit (algebraMap _ (GaugeRing k) f) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit (gaugeD k))

theorem gaugeMat_unit (g : Fin 3) :
    IsUnit ((gaugeMat k g).map (algebraMap _ (GaugeRing k))) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact gauge_isUnit_of_dvd k
    (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ g)) _)

theorem gaugeScale_unit (s : SquareSummand) (i : Fin 2) :
    IsUnit (algebraMap _ (GaugeRing k) (gaugeScale k s i)) :=
  gauge_isUnit_of_dvd k (Dvd.dvd.mul_left
    ((Finset.dvd_prod_of_mem (fun i => gaugeScale k s i) (Finset.mem_univ i)).trans
      (Finset.dvd_prod_of_mem (fun s => ∏ i, gaugeScale k s i) (Finset.mem_univ s))) _)

noncomputable def gaugeParameter : FamilyParameters (GaugeRing k) :=
  ⟨fun g => (gaugeMat_unit k g).unit, fun _ _ => 1,
    fun s i => (gaugeScale_unit k s i).unit⟩

noncomputable def gaugePsi : MvPolynomial Var k →ₐ[k] GaugeRing k :=
  aeval (orbitValue (gaugeParameter k)).coordinates

noncomputable def gaugeEval {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1) : GaugeRing k →+* S :=
  IsLocalization.Away.lift (gaugeD k) (g := (aeval (fun i => parameterEntry p (rowsA i))).toRingHom)
    (aeval_gaugeD_isUnit k p h)

theorem gaugeEval_algebraMap {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1)
    (f : MvPolynomial (Fin 143) k) :
    gaugeEval k p h (algebraMap _ (GaugeRing k) f) = aeval (fun i => parameterEntry p (rowsA i)) f :=
  IsLocalization.lift_eq _ _

theorem gaugeParameter_map {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1) :
    (gaugeParameter k).map (gaugeEval k p h) = trivialBlocks p := by
  simp only [gaugeParameter, FamilyParameters.map, trivialBlocks, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g
    apply Units.ext
    ext a b
    simp only [Units.val_map, RingHom.mapMatrix_apply, IsUnit.unit_spec, Matrix.map_apply]
    rw [gaugeEval_algebraMap]
    exact aeval_gaugeEntry k p h (.inl (g,a,b))
  · funext s g
    exact map_one _
  · funext s i
    apply Units.ext
    simp only [Units.val_map, IsUnit.unit_spec, MonoidHom.coe_coe]
    rw [gaugeEval_algebraMap, gaugeScale, aeval_gaugeEntry k p h]
    rfl

theorem gaugeEval_gaugePsi {S : Type} [CommRing S] [Algebra k S]
    (p : FamilyParameters S) (h : ∀ g, (p.global g).val (1,1) (1,1) = 1)
    (f : MvPolynomial Var k) :
    gaugeEval k p h (gaugePsi k f) = aeval (orbitValue p).coordinates f := by
  have hc : (orbitValue p).coordinates = fun x => gaugeEval k p h
      ((orbitValue (gaugeParameter k)).coordinates x) := by
    funext x
    rw [← LowerBound.coordinates_map, orbitValue_map, gaugeParameter_map]
    rfl
  rw [hc, gaugePsi]
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, aeval_C, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 143) k) (GaugeRing k),
      gaugeEval_algebraMap, MvPolynomial.algebraMap_eq, aeval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf => simp only [map_mul, hf, aeval_X]

/-- The chosen generic entries are nonzero, because specialization at the
identity parameter sends each to one. -/
theorem generic_diagonal_ne_zero (g : Fin 3) :
    ((generic k).global g).val (1,1) (1,1) ≠ 0 := by
  intro h
  let e := Component.evS k (FamilyParameters.one k)
  have he := Component.generic_map_evS k (FamilyParameters.one k)
  have h1 := congrArg (fun p : FamilyParameters k => (p.global g).val (1,1) (1,1)) he
  change e (((generic k).global g).val (1,1) (1,1)) =
    (1 : Matrix SquareVertex SquareVertex k) (1,1) (1,1) at h1
  rw [Matrix.one_apply, if_pos rfl] at h1
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The normalized 143-parameter chart has exactly the same polynomial
relations as the full generic group orbit. -/
theorem ker_gaugePsi : RingHom.ker (gaugePsi k) = orbitIdeal k := by
  ext f
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    let F := FractionRing (R k)
    let e : R k →+* F := algebraMap (R k) F
    let p := (generic k).map e
    have hp (g : Fin 3) : (p.global g).val (1,1) (1,1) ≠ 0 := by
      change e (((generic k).global g).val (1,1) (1,1)) ≠ 0
      intro hz
      apply generic_diagonal_ne_zero k g
      apply IsFractionRing.injective (R k) F
      simpa only [map_zero] using hz
    let c : Fin 3 → Fˣ := fun g => Units.mk0 _ (hp g)
    let q := centralNormalize p c
    have hq : ∀ g, (q.global g).val (1,1) (1,1) = 1 :=
      centralNormalize_diagonal p hp
    have hz := gaugeEval_gaugePsi k q hq f
    rw [h, map_zero, centralNormalize_value] at hz
    have hm : e (orbitPsi k f) = aeval (orbitValue p).coordinates f := by
      have hc : (orbitValue p).coordinates = fun x => e ((orbitValue (generic k)).coordinates x) := by
        funext x
        rw [← LowerBound.coordinates_map, orbitValue_map]
      rw [hc, orbitPsi]
      induction f using MvPolynomial.induction_on with
      | C a => rw [aeval_C, aeval_C, ← IsScalarTower.algebraMap_apply] <;> rfl
      | add f g hf hg => simp only [map_add, hf, hg]
      | mul_X f x hf => simp only [map_mul, hf, aeval_X]
    apply IsFractionRing.injective (R k) F
    rw [hm, ← hz, map_zero]
  · intro h
    have he := evS_orbitPsi k (gaugeParameter k) f
    rw [h, map_zero] at he
    exact he.symm

/-- Upper bound by the actual localized polynomial chart in 143 parameters. -/
theorem orbit_trdeg_upper : Algebra.trdeg k (OrbitRing k) ≤ (143 : Cardinal) := by
  let e : OrbitRing k →ₐ[k] GaugeRing k :=
    Ideal.Quotient.liftₐ (orbitIdeal k) (gaugePsi k) fun f hf => by
      change f ∈ RingHom.ker (gaugePsi k)
      rwa [ker_gaugePsi]
  have he : Function.Injective e := by
    refine (RingHom.injective_iff_ker_eq_bot e.toRingHom).2 ?_
    ext x
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    change f ∈ RingHom.ker (gaugePsi k) ↔ f ∈ orbitIdeal k
    rw [ker_gaugePsi]
  haveI : FaithfulSMul (MvPolynomial (Fin 143) k) (GaugeRing k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (gaugeD_ne_zero k)))
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin 143) k) (GaugeRing k) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers (gaugeD k))
  have hb := (IsTranscendenceBasis.mvPolynomial (Fin 143) k).algebraMap_comp
    (A := GaugeRing k)
  have ht : Algebra.trdeg k (GaugeRing k) = (143 : Cardinal) := by
    simpa using hb.cardinalMk_eq_trdeg.symm
  exact (trdeg_le_of_injective e he).trans (le_of_eq ht)

/-- Geometric dimension of the actual algebraic orbit closure over an
infinite field, in particular an algebraic closure of Q or F_3. -/
theorem orbitClosure_dimension_eq_143 [Infinite k] :
    ringKrullDim (MvPolynomial Var k ⧸ Component.vanishingIdeal k (orbitClosure k)) = 143 := by
  rw [orbitClosure_vanishingIdeal]
  obtain ⟨n,hn,ht⟩ := finiteType_dim_trdeg k (OrbitRing k)
  have he := le_antisymm (orbit_trdeg_upper k) (orbit_trdeg_lower k)
  rw [ht] at he
  have hn' : n = 143 := by exact_mod_cast he
  rw [hn, hn'] <;> rfl

/-- The same geometric dimension holds at every closed point of the
orbit closure, including the recursive point. -/
theorem orbitClosure_localDimension_eq_143 [Infinite k]
    (m : Ideal (OrbitRing k)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 143 := by
  rw [Brent.Equidim.ringKrullDim_localization_eq' (k := k) m]
  have h := orbitClosure_dimension_eq_143 k
  rw [orbitClosure_vanishingIdeal] at h
  exact h

theorem point_mem_orbitClosure : pointP k ∈ orbitClosure k := by
  apply subset_closure
  refine ⟨FamilyParameters.one k, ?_⟩
  rw [← value_of_blockTrivial false (p := FamilyParameters.one k) (fun _ _ => rfl),
    FamilyParameters.value_one]
  rfl

end Dimension
end Brent.Formal.OrbitClosure
