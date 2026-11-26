import Brent.Formal.NormalEliminationZ3
import Brent.KernelCheck.UpperBound
import Brent.CM.LiftedQuadrics
import Brent.KernelCheck.KernelVanishing

/-! Source draft. Transport the actual unit-minor normal elimination to the
frozen 251-dimensional integral tangent frame, not an arbitrary choice of
free coordinates. -/
namespace Brent.Formal.NormalEliminationZ3

open MvPowerSeries Finsupp Brent.Z3 Brent.CM.LiftInstance
open scoped BigOperators

abbrev Z := Fin 251

noncomputable def frameLinear (R : Type) [CommRing R] (x : V) : MvPowerSeries Z R :=
  ∑ i : Z, fR R i x • X i

theorem centered_frameLinear (R : Type) [CommRing R] (x : V) :
    constantCoeff (frameLinear R x) = 0 := by
  simp [frameLinear]

theorem coeff_frameLinear (R : Type) [CommRing R] (x : V) (i : Z) :
    coeff (single i 1) (frameLinear R x) = fR R i x := by
  classical
  simp [frameLinear, coeff_X, Finsupp.single_eq_single_iff, smul_eq_mul,
    mul_ite, Finset.sum_ite_eq']

noncomputable def freeFrame (R : Type) [CommRing R] {n : ℕ}
    (col : Fin n → V) (x : V) : MvPowerSeries Z R := by
  classical
  exact if x ∈ Set.range col then 0 else frameLinear R x

theorem centered_freeFrame (R : Type) [CommRing R] {n : ℕ} (col : Fin n → V) (x : V) :
    constantCoeff (freeFrame R col x) = 0 := by
  classical
  unfold freeFrame
  split_ifs <;> simp [centered_frameLinear]

theorem map_freeFrame {n : ℕ} (col : Fin n → V) (x : V) :
    MvPowerSeries.map rho3 (freeFrame R0 col x) = freeFrame (ZMod 3) col x := by
  classical
  unfold freeFrame
  split_ifs
  · simp
  · simp [frameLinear, fR, smul_eq_C_mul, map_sum, map_mul, map_intCast]

/-- The selected equations have no linear terms after substitution of the
actual frozen integral frame, because every frame vector is in the kernel. -/
theorem coeff_frame_eqAt (e : E) (i : Z) :
    coeff (single i 1) (subst (frameLinear R0) (eqAt (strassenSquare R0) e)) = 0 := by
  classical
  rw [coeff_single_subst (hasSubst_of_constantCoeff_zero (centered_frameLinear R0))]
  simp only [coeff_frameLinear, coeff_eqAt (strassenSquare_solves R0)]
  have he := frame_inKer R0 i e
  change (∑ x, (JInt e x : R0) * fR R0 i x) = 0 at he
  convert he using 2 with x _
  rw [JInt, strassenSquare, Decomposition.jacobianColumn_map, eq_intCast]

/-- The derivatives of the free-coordinate chart are exactly the frozen
frame. The derivative is obtained by composing the two-sided inverse,
not by assuming that its linear part equals the frame. -/
theorem inverse_in_frame {n : ℕ} (col : Fin n → V) (hc : Function.Injective col)
    (eqn : Fin n → E) (b : V → MvPowerSeries V R0)
    (hb : ∀ x, constantCoeff (b x) = 0)
    (hab : ∀ x, subst (newCoord (strassenSquare R0) col hc eqn) (b x) = X x)
    (x : V) : LowZero 2 (subst (freeFrame R0 col) (b x) - frameLinear R0 x) := by
  classical
  let a := newCoord (strassenSquare R0) col hc eqn
  let l := frameLinear R0
  let c := freeFrame R0 col
  have ha := constantCoeff_newCoord _ (strassenSquare_solves R0) col hc eqn
  have hl := hasSubst_of_constantCoeff_zero (centered_frameLinear R0)
  have hc0 := centered_freeFrame R0 col
  let g : V → MvPowerSeries Z R0 := fun y => subst l (a y)
  have hg0 (y : V) : constantCoeff (g y) = 0 :=
    constantCoeff_subst_eq_zero hl (centered_frameLinear R0) (ha y)
  have hg (y : V) (i : Z) : coeff (single i 1) (g y) = coeff (single i 1) (c y) := by
    by_cases hy : y ∈ Set.range col
    · obtain ⟨j,rfl⟩ := hy
      change coeff (single i 1) (subst l (a (col j))) = _
      rw [show a (col j) = eqAt (strassenSquare R0) (eqn j) from newCoord_col _ col hc eqn j,
        coeff_frame_eqAt]
      simp [c, freeFrame, Set.mem_range_self]
    · change coeff (single i 1) (subst l (a y)) = _
      have hfree : a y = X y := newCoord_free _ col hc eqn ⟨y,hy⟩
      rw [hfree, subst_X hl]
      simp [c, freeFrame, hy, l]
  have hcomp : subst g (b x) = l x := by
    change subst (fun y => subst l (a y)) (b x) = l x
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hl, hab x, subst_X hl]
  apply lowZero_two
  · rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hc0) hc0 (hb x),
      centered_frameLinear, sub_zero]
  · intro i
    have he := congrArg (coeff (single i 1)) hcomp
    rw [coeff_single_subst (hasSubst_of_constantCoeff_zero hg0)] at he
    rw [map_sub, coeff_single_subst (hasSubst_of_constantCoeff_zero hc0)]
    simp_rw [hg] at he
    rw [he, sub_self]

/-- A centered normal substitution in precisely the frozen frame, with all
selected equations zero and naturality of every equation under reduction. -/
theorem normal_elimination_frozen_frame :
    ∃ (col : Fin 2101 → V) (eqn : Fin 2101 → E)
      (Y : V → MvPowerSeries Z R0),
      Function.Injective col ∧ Function.Injective eqn ∧
      (∀ x, constantCoeff (Y x) = 0) ∧
      (∀ x, LowZero 2 (Y x - frameLinear R0 x)) ∧
      (∀ j, subst Y (eqAt (strassenSquare R0) (eqn j)) = 0) ∧
      (∀ e : E, MvPowerSeries.map rho3 (subst Y (eqAt (strassenSquare R0) e)) =
        subst (fun x => MvPowerSeries.map rho3 (Y x)) (eqAt (strassenSquare (ZMod 3)) e)) := by
  obtain ⟨col,eqn,hc,he,hu⟩ := exists_unit_minor
  obtain ⟨b,hb,hab,hba,_,_,_,_⟩ := normal_elimination_for_minor col hc eqn hu
  let c := freeFrame R0 col
  let Y : V → MvPowerSeries Z R0 := fun x => subst c (b x)
  have hc0 := centered_freeFrame R0 col
  have hs := hasSubst_of_constantCoeff_zero hc0
  have hY (x : V) : constantCoeff (Y x) = 0 := constantCoeff_subst_eq_zero hs hc0 (hb x)
  refine ⟨col,eqn,Y,hc,he,hY,inverse_in_frame col hc eqn b hb hab, ?_, ?_⟩
  · intro j
    change subst (fun x => subst c (b x)) (eqAt (strassenSquare R0) (eqn j)) = 0
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hs,
      ← newCoord_col (strassenSquare R0) col hc eqn j, hba (col j), subst_X hs]
    classical
    simp [c, freeFrame, Set.mem_range_self]
  · intro e
    rw [map_subst_centered rho3 hY, map_eqAt_square]

/-! The cancellation at degree two is ring-theoretic. In particular it
applies to R0, where the variable ideal is not the maximal ideal. -/
section Residual

variable {R : Type*} [CommRing R]

/-- The cubic term of a centered perturbation is in the cube of the variable ideal. -/
theorem cubic_in_cube (m : Ideal R) (D : Decomposition R SquareVertex SquareSummand)
    (hD : ∀ x, D.coordinates x ∈ m) (e : E) : D.entry e.1 e.2.1 e.2.2 ∈ m ^ 3 := by
  unfold Decomposition.entry
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [pow_succ, pow_two]
  exact Ideal.mul_mem_mul (Ideal.mul_mem_mul (hD (s,.u,e.1)) (hD (s,.v,e.2.1)))
    (hD (s,.w,e.2.2))

/-- The weighted residual equation has exactly the same degree-two part as
the weighted quadratic on the linear frame. This proof works over any
commutative ring and uses the actual left-kernel equation. -/
theorem weighted_residual_mod_cube (m : Ideal R)
    (p Y L : Decomposition R SquareVertex SquareSummand) (w : E → R)
    (hY : ∀ x, Y.coordinates x ∈ m) (hL : ∀ x, L.coordinates x ∈ m)
    (hYL : ∀ x, Y.coordinates x - L.coordinates x ∈ m ^ 2)
    (hw : ∀ x : V, ∑ e : E, p.jacobianColumn x e.1 e.2.1 e.2.2 * w e = 0) :
    (∑ e : E, w e * ((p.line Y 1).entry e.1 e.2.1 e.2.2 - p.entry e.1 e.2.1 e.2.2)) -
      (∑ e : E, w e * p.quadraticEntry L e.1 e.2.1 e.2.2) ∈ m ^ 3 := by
  have hj : ∑ e : E, w e * p.jacobianEntry Y e.1 e.2.1 e.2.2 = 0 := by
    simp only [Decomposition.jacobianEntry_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun x _ => ?_
    have h : ∑ e : E, w e * (Y.coordinates x * p.jacobianColumn x e.1 e.2.1 e.2.2) =
        Y.coordinates x * ∑ e : E, p.jacobianColumn x e.1 e.2.1 e.2.2 * w e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [h, hw, mul_zero]
  have he : (∑ e : E, w e * ((p.line Y 1).entry e.1 e.2.1 e.2.2 - p.entry e.1 e.2.1 e.2.2)) -
      (∑ e : E, w e * p.quadraticEntry L e.1 e.2.1 e.2.2) =
      (∑ e : E, w e * p.jacobianEntry Y e.1 e.2.1 e.2.2) +
      ∑ e : E, w e * (p.quadraticEntry Y e.1 e.2.1 e.2.2 -
        p.quadraticEntry L e.1 e.2.1 e.2.2 + Y.entry e.1 e.2.1 e.2.2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Decomposition.entry_line]
    ring
  rw [he, hj, zero_add]
  refine Submodule.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ ?_
  exact Ideal.add_mem _ (Decomposition.quadraticEntry_sub_mem m p Y L
      (UpperBound.components hY) (UpperBound.components hL) (UpperBound.components_sub hYL)
      e.1 e.2.1 e.2.2) (cubic_in_cube m Y hY e)

end Residual

section IntegralResidual

open Brent.CM.LiftedQuadrics Brent.TangentData Brent.QuadraticData

local notation "S" => MvPowerSeries Z R0

/-- The lifted residual weighted by the actual certified integral left-kernel row. -/
noncomputable def liftedWeight (ell : Fin 54) (e : E) : S :=
  C (lamExact ell (squareEquationNumber e))

/-- The quadratic polynomial on all 251 frozen coordinates, before removing
its identically zero blocks. This is a polynomial, not a truncated residual. -/
noncomputable def fullFrameQuadric (ell : Fin 54) : MvPolynomial Z R0 :=
  ∑ e : E, MvPolynomial.C (lamExact ell (squareEquationNumber e)) *
    ((strassenSquare R0).map MvPolynomial.C).quadraticEntry
      (Decomposition.lc (fun i : Z => MvPolynomial.X i)
        (fun i => (frameDirection R0 i).map MvPolynomial.C)) e.1 e.2.1 e.2.2

theorem ofCoords_coord (g : V → S) (x : V) : (ofCoords g).coordinates x = g x := by
  obtain ⟨s,m,a⟩ := x
  cases m <;> rfl

theorem linear_frame_decomposition : ofCoords (frameLinear R0) =
    Decomposition.lc (fun i : Z => X i) (fun i => (frameDirection R0 i).map C) := by
  apply Decomposition.eq_of_components <;> funext s a <;>
    simp [ofCoords, frameLinear, Decomposition.lc, Decomposition.map,
      frameDirection, fR, fInt, MvPowerSeries.smul_eq_C_mul, mul_comm]

theorem subst_eqAt_entry (Y : V → S) (hY : ∀ x, constantCoeff (Y x) = 0) (e : E) :
    subst Y (eqAt (strassenSquare R0) e) =
      (((strassenSquare R0).map C).line (ofCoords Y) 1).entry e.1 e.2.1 e.2.2 -
        ((strassenSquare R0).map C).entry e.1 e.2.1 e.2.2 := by
  have hs := hasSubst_of_constantCoeff_zero hY
  rw [← substAlgHom_apply hs, eqAt, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom,
    eval₂_equation_gen]
  have hc (r : R0) : substAlgHom hs (C r) = C r := by
    have h := (substAlgHom hs).commutes r
    simpa only [algebraMap_apply] using h
  simp only [Function.comp_def, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, map_add,
    hc, substAlgHom_X, Decomposition.entry_map, strassenSquare_solves R0]
  congr 1
  apply Decomposition.eq_of_components <;> funext s a <;>
    simp [ofCoords, Decomposition.line, Decomposition.map, Decomposition.coordinates]

theorem exact_weight_annihilates (ell : Fin 54) (x : V) :
    ∑ e : E, ((strassenSquare R0).map C).jacobianColumn x e.1 e.2.1 e.2.2 *
      liftedWeight ell e = 0 := by
  simp only [liftedWeight, Decomposition.jacobianColumn_map, ← map_mul, ← map_sum,
    lamExact_annihilates, map_zero]

/-- For the actual integral covectors and actual frozen-frame normal tuple,
the entire residual minus its polynomial quadratic part lies in (z)^3. -/
theorem actual_residual_initial_quadric (ell : Fin 54) (Y : V → S)
    (hY : ∀ x, constantCoeff (Y x) = 0)
    (hYL : ∀ x, LowZero 2 (Y x - frameLinear R0 x)) :
    LowZero 3 ((∑ e : E, liftedWeight ell e * subst Y (eqAt (strassenSquare R0) e)) -
      (fullFrameQuadric ell : S)) := by
  let m := mX Z R0
  let p := (strassenSquare R0).map C
  let L := ofCoords (frameLinear R0)
  have hYm (x : V) : (ofCoords Y).coordinates x ∈ m := by
    rw [ofCoords_coord, ← pow_one m]
    exact mem_pow_of_lowZero 1 _ (lowZero_one_of_constantCoeff (hY x))
  have hLm (x : V) : L.coordinates x ∈ m := by
    change (ofCoords (frameLinear R0)).coordinates x ∈ m
    rw [ofCoords_coord, ← pow_one m]
    exact mem_pow_of_lowZero 1 _ (lowZero_one_of_constantCoeff (centered_frameLinear R0 x))
  have hdiff (x : V) : (ofCoords Y).coordinates x - L.coordinates x ∈ m ^ 2 := by
    change (ofCoords Y).coordinates x - (ofCoords (frameLinear R0)).coordinates x ∈ m ^ 2
    rw [ofCoords_coord, ofCoords_coord]
    exact mem_pow_of_lowZero 2 _ (hYL x)
  have h := weighted_residual_mod_cube m p (ofCoords Y) L (liftedWeight ell)
    hYm hLm hdiff (exact_weight_annihilates ell)
  simp_rw [← subst_eqAt_entry Y hY] at h
  have hquad : (fullFrameQuadric ell : S) = ∑ e : E,
      liftedWeight ell e * p.quadraticEntry L e.1 e.2.1 e.2.2 := by
    rw [fullFrameQuadric, MvPolynomial.coe_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_C]
    congr 1
    rw [show L = Decomposition.lc (fun i : Z => X i) (fun i => (frameDirection R0 i).map C)
      from linear_frame_decomposition]
    simp [Decomposition.quadraticEntry, Decomposition.lc, Decomposition.map, p,
      MvPolynomial.coe_sum, MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  rw [hquad]
  exact lowZero_of_mem_pow 3 h

/-- The quadratic coefficients on the full integral frame, with the true
left-kernel lift rather than a coordinatewise representative modulo three. -/
noncomputable def liftBilinear (ell : Fin 54) (i j : Z) : R0 :=
  ∑ e : E, (strassenSquare R0).bilinearEntry (frameDirection R0 i)
    (frameDirection R0 j) e.1 e.2.1 e.2.2 * lamExact ell (squareEquationNumber e)

noncomputable def liftPolar (ell : Fin 54) (i j : Z) : R0 :=
  ∑ e : E, (strassenSquare R0).polarizedEntry (frameDirection R0 i)
    (frameDirection R0 j) e.1 e.2.1 e.2.2 * lamExact ell (squareEquationNumber e)

theorem liftBilinear_diag (ell : Fin 54) (i : Z) : liftBilinear ell i i = 0 := by
  exact KernelVanishing.square_zero _ (lamExact_annihilates ell)
    (fun r hr => (mul_eq_zero.mp hr).resolve_left (by norm_num)) i

theorem liftBilinear_polar (ell : Fin 54) (i j : Z) :
    liftBilinear ell i j + liftBilinear ell j i = liftPolar ell i j := by
  rw [liftBilinear, liftBilinear, liftPolar, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Decomposition.polarizedEntry_eq_bilinear]
  ring

theorem liftPolar_nonmixed (ell : Fin 54) (i j : Z)
    (h : ¬ ((143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) ∨
             (143 ≤ j.val ∧ j.val < 197 ∧ 197 ≤ i.val))) : liftPolar ell i j = 0 :=
  KernelVanishing.nonmixed_zero _ (lamExact_annihilates ell) i j h

theorem fullFrameQuadric_expand (ell : Fin 54) : fullFrameQuadric ell =
    ∑ i : Z, ∑ j : Z, MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.C (liftBilinear ell i j) := by
  simp only [fullFrameQuadric, Decomposition.quadraticEntry_lc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [liftBilinear, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Decomposition.bilinearEntry_map, map_mul]
  ring

theorem fullFrameQuadric_ordered (ell : Fin 54) : fullFrameQuadric ell =
    ∑ i : Z, ∑ j : Z, (if i < j then MvPolynomial.X i * MvPolynomial.X j *
      MvPolynomial.C (liftPolar ell i j) else 0) := by
  rw [fullFrameQuadric_expand, sum_sum_eq_ordered]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h h'
  · rw [← liftBilinear_polar, map_add]; ring
  · subst j; rw [liftBilinear_diag, map_zero, mul_zero]
  · rfl

/-- The exact integral mixed polar coefficients are the ones in qtExact. -/
theorem liftPolar_mixed (ell a b : Fin 54) : liftPolar ell (xFrameIndex a) (yFrameIndex b) =
    ∑ e : E, (mixedEntry a b e : R0) * lamExact ell (squareEquationNumber e) := by
  have hx : frameDirection R0 (xFrameIndex a) = (xDirection a).map (Int.castRingHom R0) := by
    apply Decomposition.eq_of_components <;> funext s c
    · exact congrArg (fun n : Int => (n : R0)) (archived_left_coordinates a (s,.u,c))
    · exact congrArg (fun n : Int => (n : R0)) (archived_left_coordinates a (s,.v,c))
    · exact congrArg (fun n : Int => (n : R0)) (archived_left_coordinates a (s,.w,c))
  have hy : frameDirection R0 (yFrameIndex b) = (yDirection b).map (Int.castRingHom R0) := by
    apply Decomposition.eq_of_components <;> funext s c
    · exact congrArg (fun n : Int => (n : R0)) (archived_right_coordinates b (s,.u,c))
    · exact congrArg (fun n : Int => (n : R0)) (archived_right_coordinates b (s,.v,c))
    · exact congrArg (fun n : Int => (n : R0)) (archived_right_coordinates b (s,.w,c))
  rw [liftPolar, hx, hy]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  have he : mixedEntry a b e = strassenSquareInt.polarizedEntry (xDirection a) (yDirection b)
      e.1 e.2.1 e.2.2 := by
    unfold mixedEntry
    simp only [Decomposition.quadraticEntry, Decomposition.polarizedEntry, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    change ((xDirection a).u s e.1 + (yDirection b).u s e.1) *
      ((xDirection a).v s e.2.1 + (yDirection b).v s e.2.1) * strassenSquareInt.w s e.2.2 +
      ((xDirection a).u s e.1 + (yDirection b).u s e.1) * strassenSquareInt.v s e.2.1 *
        ((xDirection a).w s e.2.2 + (yDirection b).w s e.2.2) +
      strassenSquareInt.u s e.1 * ((xDirection a).v s e.2.1 + (yDirection b).v s e.2.1) *
        ((xDirection a).w s e.2.2 + (yDirection b).w s e.2.2) - _ - _ = _
    ring
  rw [he, ← CharThree.polarizedEntry_map]
  rfl

/-- No nonmixed or diagonal terms remain in the actual lifted quadratic. -/
theorem fullFrameQuadric_mixed (ell : Fin 54) : fullFrameQuadric ell =
    ∑ a : Fin 54, ∑ b : Fin 54,
      MvPolynomial.X (xFrameIndex a) * MvPolynomial.X (yFrameIndex b) *
        MvPolynomial.C (∑ e : E, (mixedEntry a b e : R0) * lamExact ell (squareEquationNumber e)) := by
  rw [fullFrameQuadric_ordered]
  have hx : ∀ i : Z, (∀ a, xFrameIndex a ≠ i) → ¬ (143 ≤ i.val ∧ i.val < 197) := by
    intro i hi ⟨h1,h2⟩
    exact hi ⟨i.val-143,by omega⟩ (Fin.ext (by simp only [xFrameIndex]; omega))
  have hy : ∀ j : Z, (∀ b, yFrameIndex b ≠ j) → ¬ (197 ≤ j.val) := by
    intro j hj h1
    exact hj ⟨j.val-197,by have := j.isLt; omega⟩ (Fin.ext (by simp only [yFrameIndex]; omega))
  let F (i j : Z) : MvPolynomial Z R0 := if i < j then MvPolynomial.X i * MvPolynomial.X j *
    MvPolynomial.C (liftPolar ell i j) else 0
  have hG : ∀ i j : Z, ¬ (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) → F i j = 0 := by
    intro i j hij
    dsimp [F]
    split_ifs with hlt
    · rw [liftPolar_nonmixed ell i j ?_, map_zero, mul_zero]
      rintro (h | h)
      · exact hij h
      · have : i.val < j.val := hlt
        omega
    · rfl
  change (∑ i : Z, ∑ j : Z, F i j) = _
  rw [sum_comp_of_zero (fun i => ∑ j : Z, F i j) xFrameIndex UpperBound.xFrameIndex_injective
    (fun i hi => Finset.sum_eq_zero fun j _ => hG i j fun hh => hx i hi ⟨hh.1,hh.2.1⟩)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_comp_of_zero (F (xFrameIndex a)) yFrameIndex UpperBound.yFrameIndex_injective
    (fun j hj => hG _ j fun hh => hy j hj hh.2.2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hlt : xFrameIndex a < yFrameIndex b := by
    show (xFrameIndex a).val < (yFrameIndex b).val
    simp only [xFrameIndex,yFrameIndex]; omega
  rw [F, if_pos hlt, liftPolar_mixed]

end IntegralResidual

end Brent.Formal.NormalEliminationZ3
