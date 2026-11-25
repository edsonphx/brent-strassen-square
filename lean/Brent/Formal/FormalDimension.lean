import Brent.Formal.CoordinateChange
import Brent.Formal.PowerSeriesNoetherian
import Brent.KernelCheck.UpperBound
import Brent.KernelCheck.CharZero

/-!
# `dim Â ≤ 197`

`Â = k⟦z⟧ ⧸ (centered Brent equations)` is a Noetherian local ring. The substitution
`z ↦ p + z` gives a ring map `A → Â` out of the algebraic local ring, sending the maximal
ideal onto the maximal ideal. The relations behind the bound `dim A ≤ 197` (generation of
`𝔪` by the 251 tangent coordinates modulo `𝔪²`, and the 54 quadratic relations modulo `𝔪³`)
therefore hold in `Â`. The same Nakayama and height-theorem arguments give `dim Â ≤ 197`,
in characteristic three and in characteristic zero.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries IsLocalRing

set_option linter.unusedSectionVars false

variable (k : Type) [Field k]

/-- The translation `z ↦ p + z` on polynomials. -/
noncomputable def ψ0 : MvPolynomial Var k →+* MvPowerSeries Var k :=
  MvPolynomial.eval₂Hom C (fun x => C (pt k x) + X x)

theorem constantCoeff_ψ0 (p : MvPolynomial Var k) :
    constantCoeff (ψ0 k p) = MvPolynomial.eval (strassenSquare k).coordinates p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [ψ0]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [ψ0, pt]

theorem brentPS_le : brentPS k ≤ RingHom.ker (constantCoeff (σ := Var) (R := k)) := by
  rw [brentPS, Ideal.span_le]
  rintro _ ⟨abc, rfl⟩
  change constantCoeff (ψ0 k _) = 0
  rw [constantCoeff_ψ0, eval_equation, strassenSquare_solves k abc.1 abc.2.1 abc.2.2, sub_self]

theorem brentPS_ne_top : brentPS k ≠ ⊤ := by
  intro h
  have := brentPS_le k (h ▸ Submodule.mem_top : (1 : MvPowerSeries Var k) ∈ brentPS k)
  simp at this

instance : Nontrivial (Ahat k) := Ideal.Quotient.nontrivial_iff.mpr (brentPS_ne_top k)

instance : IsLocalRing (Ahat k) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance : IsNoetherianRing (Ahat k) := inferInstance

/-- The quotient map. -/
noncomputable abbrev mkA : MvPowerSeries Var k →+* Ahat k := Ideal.Quotient.mk (brentPS k)

theorem isUnit_mkA_iff (f : MvPowerSeries Var k) : IsUnit (mkA k f) ↔ constantCoeff f ≠ 0 := by
  constructor
  · intro hu h0
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : f * g - 1 ∈ brentPS k := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one]
      exact sub_eq_zero.mpr hb
    have := brentPS_le k hmem
    rw [RingHom.mem_ker, map_sub, map_mul, h0, zero_mul, map_one, zero_sub, neg_eq_zero] at this
    exact one_ne_zero this
  · intro h
    exact (isUnit_iff_constantCoeff.mpr (Ne.isUnit h)).map _

theorem maximalIdeal_Ahat :
    maximalIdeal (Ahat k) = Ideal.span (Set.range fun x : Var => mkA k (X x)) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : constantCoeff f = 0 := by
      by_contra h
      exact ha ((isUnit_mkA_iff k f).mpr h)
    have hf : f ∈ Ideal.span (X '' ((Finset.univ : Finset Var) : Set Var)) := by
      refine mem_span_X_of_coeff _ f fun m hm => ?_
      have : m = 0 := Finsupp.ext fun i => hm i (Finset.mem_univ i)
      rw [this, coeff_zero_eq_constantCoeff_apply, h0]
    have := Ideal.mem_map_of_mem (mkA k) hf
    rw [Ideal.map_span, Set.image_image, Finset.coe_univ, Set.image_univ] at this
    exact this
  · rw [Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff, isUnit_mkA_iff]
    simp

/-! ### The map from the algebraic local ring -/

/-- The algebraic local ring at the recursive point. -/
abbrev Aalg := UpperBound.A k

/-- The coordinate ring maps to `Â`. -/
noncomputable def gQ : SquareCoordinateRing k →+* Ahat k :=
  Ideal.Quotient.lift _ ((mkA k).comp (ψ0 k)) (by
    intro p hp
    have hle : brentIdeal k SquareVertex SquareSummand ≤ RingHom.ker ((mkA k).comp (ψ0 k)) := by
      rw [brentIdeal, Ideal.span_le]
      rintro _ ⟨abc, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨abc, rfl⟩
    exact hle hp)

theorem gQ_mk (p : MvPolynomial Var k) : gQ k (Ideal.Quotient.mk _ p) = mkA k (ψ0 k p) := rfl

theorem gQ_unit (y : (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl) :
    IsUnit (gQ k y) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [gQ_mk, isUnit_mkA_iff, constantCoeff_ψ0]
  intro h
  exact hy h

/-- **The completion map** `A → Â`. -/
noncomputable def ψ : Aalg k →+* Ahat k :=
  IsLocalization.lift (M := (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl)
    (S := Aalg k) (gQ_unit k)

theorem ψ_toPoint (p : MvPolynomial Var k) :
    ψ k (toPointLocalRing (strassenSquare k) (strassenSquare_solves k) p) = mkA k (ψ0 k p) := by
  rw [toPointLocalRing_apply, ψ, IsLocalization.lift_eq, gQ_mk]

theorem map_maximalIdeal : Ideal.map (ψ k) (maximalIdeal (Aalg k)) = maximalIdeal (Ahat k) := by
  rw [maximalIdeal_pointLocalRing, ker_eval_eq_span, Ideal.map_span, Ideal.map_span,
    maximalIdeal_Ahat, Set.image_image, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun x => ?_))
  change ψ k (toPointLocalRing (strassenSquare k) (strassenSquare_solves k)
    (MvPolynomial.X x - MvPolynomial.C ((strassenSquare k).coordinates x))) = _
  rw [ψ_toPoint]
  simp [ψ0, pt]

theorem ψ_mem {a : Aalg k} (h : a ∈ maximalIdeal (Aalg k)) : ψ k a ∈ maximalIdeal (Ahat k) := by
  rw [← map_maximalIdeal]
  exact Ideal.mem_map_of_mem _ h

theorem ψ_mem_pow {a : Aalg k} {n : ℕ} (h : a ∈ maximalIdeal (Aalg k) ^ n) :
    ψ k a ∈ maximalIdeal (Ahat k) ^ n := by
  rw [← map_maximalIdeal, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ h

theorem ψ_intCast (t : ℤ) : ψ k (t : Aalg k) = (t : Ahat k) := by
  induction t using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [Int.cast_add, Int.cast_add, map_add, ih, Int.cast_one, Int.cast_one, map_one]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_sub, map_sub, ih, Int.cast_one, Int.cast_one, map_one]

/-! ### The dimension bound -/

set_option synthInstance.maxHeartbeats 400000 in
open TangentData QuadraticData CharThree UpperBound in
/-- **`dim Â ≤ 197` in characteristic three.** -/
theorem ringKrullDim_Ahat_le_charThree [CharP k 3] :
    ringKrullDim (Ahat k) ≤ ((143 + 54 : ℕ) : WithBot ℕ∞) := by
  refine triangular_dim_le (ψ k ∘ cs k) (ψ k ∘ xs k) (ψ k ∘ ys k)
    (fun l a b => ψ k (Mc k l a b)) quadraticMatching quadraticMatching_bijective.2
    (fun _ => ψ_mem k (z_mem k _)) (fun _ => ψ_mem k (z_mem k _)) (fun _ => ψ_mem k (z_mem k _))
    ?_ ?_ ?_ ?_
  · rw [← map_maximalIdeal]
    refine (Ideal.map_mono (gen k)).trans (le_of_eq ?_)
    simp only [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.range_comp]
  · intro ell
    have := ψ_mem_pow k (mixed_rel k ell)
    simpa only [map_sum, map_mul] using this
  · intro ell
    simp only [Mc_lead, map_one]
  · intro ell a b h
    simp only [Mc_zero k ell a b h, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
open TangentData QuadraticData CharThree UpperBound CharZeroBound in
/-- **`dim Â ≤ 197` in characteristic zero.** -/
theorem ringKrullDim_Ahat_le_charZero [CharZero k] :
    ringKrullDim (Ahat k) ≤ ((143 + 54 : ℕ) : WithBot ℕ∞) := by
  refine Transfer.charZero_dim_le ?_ (ψ k ∘ z k) (fun _ => ψ_mem k (z_mem k _)) ?_
    CharZeroBound.B ?_ projectedPolar B_diag B_polar B_nonmixed quadraticMatching
    quadraticMatching_bijective.2 (fun ell => (archived_polar_leading ell).1)
    (fun ell => (archived_polar_leading ell).2)
  · intro t ht
    have e : algebraMap k (Ahat k) (t : k) = (t : Ahat k) :=
      eq_intCast ((algebraMap k (Ahat k)).comp (Int.castRingHom k)) t
    rw [← e]
    exact (IsUnit.mk0 _ (Int.cast_ne_zero.mpr ht)).map _
  · rw [← map_maximalIdeal]
    refine (Ideal.map_mono (gen_z k)).trans (le_of_eq ?_)
    simp only [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.range_comp]
  · intro ell
    have := ψ_mem_pow k (rel_B k ell)
    rw [map_sum] at this
    refine (congrArg (· ∈ maximalIdeal (Ahat k) ^ 3) ?_).mp this
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    generalize CharZeroBound.B ell i j = t
    rw [map_mul, map_mul, Function.comp_apply, Function.comp_apply]
    rw [ψ_intCast]

end Brent.Formal
