import Brent.Formal.NormalFrameZ3
import Brent.Formal.Completion
import Brent.Formal.SliceIndependence

/-! Full residual presentation in the same frozen integral tangent frame.
The proof uses the actual unit minor and every Brent equation. No assertion
of surjectivity or of equality of ideals is taken as an extra hypothesis
in the final theorem. Source draft pending elaboration. -/
namespace Brent.Formal.NormalEliminationZ3
open MvPowerSeries Finsupp Brent.Z3 Brent.CM.LiftInstance
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A surjective map induces the quotient by the image ideal if its kernel
is contained in the original ideal. -/
noncomputable def residualQuotientEquiv {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (I : Ideal A)
    (hker : RingHom.ker f ≤ I) : (A ⧸ I) ≃+* (B ⧸ I.map f) := by
  let g := Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f) (by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hx))
  apply RingEquiv.ofBijective g
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (I.map f) (f a) = 0 at hx
    obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    have hz : a - b ∈ RingHom.ker f := by
      change f (a-b) = 0
      rw [map_sub, he, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
      simpa only [sub_add_cancel] using I.add_mem (hker hz) hb)
  · intro y
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨Ideal.Quotient.mk I a,rfl⟩

/-- A tangent vector over F3 that vanishes on the free coordinates is zero:
the selected rows then give the nonsingular pivot system on its remaining entries. -/
theorem free_restriction_injective (col : Fin 2101 → V) (hc : Function.Injective col)
    (eqn : Fin 2101 → E) (hu : IsUnit (minorAt (strassenSquare R0) col eqn).det)
    (v : V → ZMod 3) (hv : InKer (ZMod 3) v) (hz : ∀ x : Free col, v x = 0) : v = 0 := by
  classical
  let M := minorAt (strassenSquare (ZMod 3)) col eqn
  have hM : M = (minorAt (strassenSquare R0) col eqn).map rho3 := by
    ext i j
    have h := congrArg (coeff (single (col j) 1)) (map_eqAt_square (eqn i))
    rw [coeff_map, coeff_eqAt (strassenSquare_solves R0),
      coeff_eqAt (strassenSquare_solves (ZMod 3))] at h
    exact h.symm
  have hd : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact hu.map rho3
  let w : Fin 2101 → ZMod 3 := fun j => v (col j)
  have hw : M *ᵥ w = 0 := by
    funext i
    have h : (∑ x, (JInt (eqn i) x : ZMod 3) * v x) = 0 := hv (eqn i)
    have hsplit := Fintype.sum_equiv (splitEquiv' col hc)
      (fun a => (JInt (eqn i) (splitEquiv' col hc a) : ZMod 3) * v (splitEquiv' col hc a))
      (fun x => (JInt (eqn i) x : ZMod 3) * v x) (fun _ => rfl)
    rw [Fintype.sum_sum_type] at hsplit
    simp only [splitEquiv'_inl, splitEquiv'_inr, hz, mul_zero, Finset.sum_const_zero,
      add_zero, h] at hsplit
    simpa [M, w, Matrix.mulVec, dotProduct, minorAt, jacobian_cast] using hsplit
  have hw0 : w = 0 := by
    have h := congrArg (fun u => M⁻¹ *ᵥ u) hw
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h
  funext x
  by_cases hx : x ∈ Set.range col
  · obtain ⟨j,rfl⟩ := hx
    exact congrFun hw0 j
  · exact hz ⟨x,hx⟩

/-- The 251 frozen frame vectors restrict to a unit square matrix on the
free coordinates of this very minor, not some unrelated pivot chart. -/
theorem free_frame_unit (col : Fin 2101 → V) (hc : Function.Injective col)
    (eqn : Fin 2101 → E) (hu : IsUnit (minorAt (strassenSquare R0) col eqn).det)
    (e : Z ≃ Free col) :
    IsUnit (((minorInt (fun i => (e i).val) id).map (Int.cast : ℤ → R0)).det) := by
  classical
  let N := minorInt (fun i => (e i).val) id
  let M : Matrix Z Z (ZMod 3) := N.map (Int.cast : ℤ → ZMod 3)
  have hi : LinearIndependent (ZMod 3) M.col := by
    rw [Fintype.linearIndependent_iff]
    intro c h
    let v : V → ZMod 3 := ∑ i : Z, c i • fR (ZMod 3) i
    have hv : InKer (ZMod 3) v := by
      intro a
      simp only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have he : ∑ x, (JInt a x : ZMod 3) * (c i * fR (ZMod 3) i x) =
          c i * ∑ x, (JInt a x : ZMod 3) * fR (ZMod 3) i x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [he, frame_inKer (ZMod 3) i a, mul_zero]
    have hz (x : Free col) : v x = 0 := by
      have hx := congrFun h (e.symm x)
      simpa [v, M, N, minorInt, fR, Matrix.col] using hx
    exact Fintype.linearIndependent_iff.mp (frame_independent_field (ZMod 3)) c
      (free_restriction_injective col hc eqn hu v hv hz)
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hi)).ne_zero
  apply isUnit_minor_R0
  intro h3
  apply hdet
  rw [show M = N.map (Int.cast : ℤ → ZMod 3) from rfl, ← Int.cast_det]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3

/-- The change from free coordinates to the frozen frame is an actual
formal isomorphism. -/
theorem frame_subst_bijective (col : Fin 2101 → V) (hc : Function.Injective col)
    (eqn : Fin 2101 → E) (hu : IsUnit (minorAt (strassenSquare R0) col eqn).det) :
    Function.Bijective (subst (fun x : Free col => frameLinear R0 x)) := by
  classical
  let e : Z ≃ Free col := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, card_free col hc])
  apply subst_bijective_equiv e (fun x => centered_frameLinear R0 x)
  rw [Matrix.isUnit_iff_isUnit_det,
    ← Matrix.det_submatrix_equiv_self e]
  have he : (Matrix.of fun (x j : Free col) =>
      coeff (single (e.symm j) 1) (frameLinear R0 x.val)).submatrix e e =
        (minorInt (fun i => (e i).val) id).map (Int.cast : ℤ → R0) := by
    ext i j
    simp [coeff_frameLinear, minorInt, fR]
  rw [he]
  exact free_frame_unit col hc eqn hu e

/-- The residual map uses exactly the same substitution as the frozen-frame
quadratic calculation. It is surjective and its kernel is inside the
original Brent ideal, so the residual equations generate the full kernel
on taking the quotient. -/
theorem frozen_residual_map_of_free_bijective {R : Type} [CommRing R] [Nontrivial R]
    (col : Fin 2101 → V) (hc : Function.Injective col)
    (eqn : Fin 2101 → E)
    (hdc : Function.Bijective (subst (fun x : Free col => frameLinear R x)))
    (b : V → MvPowerSeries V R) (hb : ∀ x, constantCoeff (b x) = 0)
    (hab : ∀ x, subst (newCoord (strassenSquare R) col hc eqn) (b x) = X x)
    (hba : ∀ x, subst b (newCoord (strassenSquare R) col hc eqn x) = X x) :
    let Y : V → MvPowerSeries Z R := fun x => subst (freeFrame R col) (b x)
    let hY : ∀ x, constantCoeff (Y x) = 0 := fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (centered_freeFrame R col))
        (centered_freeFrame R col) (hb x)
    let g := (substAlgHom (hasSubst_of_constantCoeff_zero hY)).toRingHom
    Function.Surjective g ∧ RingHom.ker g ≤ idealAt (strassenSquare R) := by
  classical
  dsimp only
  let a := newCoord (strassenSquare R) col hc eqn
  let c := freeFrame R col
  let d : Free col → MvPowerSeries Z R := fun x => frameLinear R x
  have ha := hasSubst_of_constantCoeff_zero
    (constantCoeff_newCoord _ (strassenSquare_solves R) col hc eqn)
  have hs := hasSubst_of_constantCoeff_zero (centered_freeFrame R col)
  have hsb := hasSubst_of_constantCoeff_zero hb
  have hd := hasSubst_of_constantCoeff_zero (fun x : Free col => centered_frameLinear R x)
  have hcomp (f : MvPowerSeries V R) :
      subst c f = subst d (killCompl (freeEmb col) f) := by
    have hkill : (fun x : V => killCompl (R := R) (freeEmb col) (X x)) =
        fun x => if h : x ∈ Set.range col then 0 else X (⟨x,h⟩ : Free col) := by
      funext x
      by_cases hx : x ∈ Set.range col
      · rw [dif_pos hx, killCompl_X_eq_zero]
        rw [← range_freeEmb_compl] at hx
        exact hx
      · rw [dif_neg hx]
        exact killCompl_X (e := freeEmb col) (⟨x,hx⟩ : Free col)
    have hsub (x : V) : subst d (killCompl (freeEmb col) (X x)) = c x := by
      rw [show killCompl (freeEmb col) (X x : MvPowerSeries V R) =
        (fun x : V => if h : x ∈ Set.range col then 0 else X (⟨x,h⟩ : Free col)) x from congrFun hkill x]
      by_cases hx : x ∈ Set.range col
      · simp [c, freeFrame, hx, ← substAlgHom_apply hd]
      · simp [c, freeFrame, hx, subst_X hd, d]
    have hk' : killCompl (freeEmb col) f =
        subst (fun x : V => killCompl (freeEmb col) (X x : MvPowerSeries V R)) f := by
      simpa only [subst_self, id] using
        (killCompl_subst (freeEmb col) (a := fun x : V => (X x : MvPowerSeries V R))
          (fun _ => constantCoeff_X _) f)
    rw [hk', subst_comp_subst_apply
      (hasSubst_of_constantCoeff_zero (fun x : V => by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
          coeff_zero_eq_constantCoeff_apply, constantCoeff_X])) hd,
      show (fun x : V => subst d (killCompl (freeEmb col) (X x : MvPowerSeries V R))) = c from funext hsub]
  have hinv (f : MvPowerSeries V R) : subst a (subst b f) = f := by
    rw [subst_comp_subst_apply hsb ha, show (fun x => subst a (b x)) = X from funext hab,
      subst_self, id]
  have hinv' (f : MvPowerSeries V R) : subst b (subst a f) = f := by
    rw [subst_comp_subst_apply ha hsb, show (fun x => subst b (a x)) = X from funext hba,
      subst_self, id]
  have hY (f : MvPowerSeries V R) :
      subst (fun x => subst c (b x)) f = subst d (killCompl (freeEmb col) (subst b f)) := by
    rw [← subst_comp_subst_apply hsb hs, hcomp]
  constructor
  · intro z
    obtain ⟨u,rfl⟩ := hdc.2 z
    obtain ⟨w,rfl⟩ := killCompl_surjective (k := R) (freeEmb col) u
    refine ⟨subst a w, ?_⟩
    change subst (fun x => subst c (b x)) (subst a w) = _
    rw [hY, hinv']
  · intro f hf
    change subst (fun x => subst c (b x)) f = 0 at hf
    rw [hY] at hf
    have hk : killCompl (freeEmb col) (subst b f) = 0 := hdc.1 (by
      rw [hf, ← substAlgHom_apply hd, map_zero])
    have hm : subst b f ∈ Ideal.span (X '' (Set.range col) : Set (MvPowerSeries V R)) := by
      rw [← range_freeEmb_compl, ← ker_killCompl]
      exact hk
    have hmap := Ideal.mem_map_of_mem (substAlgHom ha) hm
    rw [Ideal.map_span] at hmap
    have hle : Ideal.span ((substAlgHom ha) '' (X '' Set.range col)) ≤
        idealAt (strassenSquare R) := by
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨_, ⟨j,rfl⟩,rfl⟩,rfl⟩
      rw [substAlgHom_X, newCoord_col]
      exact Ideal.subset_span ⟨eqn j,rfl⟩
    have hfinal := hle hmap
    change subst a (subst b f) ∈ idealAt (strassenSquare R) at hfinal
    rwa [hinv] at hfinal

/-- The full residual ideal (all 4096 equations, including the 2101 zero
ones), not merely a collection of its quadratic initial forms. -/
noncomputable def residualIdeal {R : Type} [CommRing R] [Nontrivial R]
    (Y : V → MvPowerSeries Z R) : Ideal (MvPowerSeries Z R) :=
  Ideal.span (Set.range fun e : E => subst Y (eqAt (strassenSquare R) e))

/-- Exactly 1995 rows are unselected. -/
theorem card_unselected (eqn : Fin 2101 → E) (he : Function.Injective eqn) :
    Fintype.card ↥(Set.range eqn)ᶜ = 1995 := by
  classical
  rw [Fintype.card_compl_set, square_equation_count,
    Set.card_range_of_injective he, Fintype.card_fin]

/-- Removing the selected, identically zero residuals does not change the
ideal. This is an equality of ideals, with no truncation. -/
theorem residualIdeal_eq_unselected {R : Type} [CommRing R] [Nontrivial R]
    (Y : V → MvPowerSeries Z R) (eqn : Fin 2101 → E)
    (h : ∀ j, subst Y (eqAt (strassenSquare R) (eqn j)) = 0) :
    residualIdeal Y = Ideal.span (Set.range fun e : ↥(Set.range eqn)ᶜ =>
      subst Y (eqAt (strassenSquare R) e.val)) := by
  classical
  unfold residualIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨e,rfl⟩
    by_cases he : e ∈ Set.range eqn
    · obtain ⟨j,rfl⟩ := he
      rw [h j]
      exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨⟨e,he⟩,rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨e,rfl⟩
    exact Ideal.subset_span ⟨e.val,rfl⟩

/-- Exact quotient presentation over the localized integers, with the
frozen tangent frame, the actual selected equations and base change of
all the residual generators. -/
theorem normal_elimination_frozen_quotient :
    ∃ (col : Fin 2101 → V) (eqn : Fin 2101 → E) (Y : V → MvPowerSeries Z R0),
      Function.Injective col ∧ Function.Injective eqn ∧
      (∀ x, constantCoeff (Y x) = 0) ∧
      (∀ x, LowZero 2 (Y x - frameLinear R0 x)) ∧
      (∀ j, subst Y (eqAt (strassenSquare R0) (eqn j)) = 0) ∧
      (∀ e : E, MvPowerSeries.map rho3 (subst Y (eqAt (strassenSquare R0) e)) =
        subst (fun x => MvPowerSeries.map rho3 (Y x)) (eqAt (strassenSquare (ZMod 3)) e)) ∧
      Nonempty (AhatAt (strassenSquare R0) ≃+* (MvPowerSeries Z R0 ⧸ residualIdeal Y)) := by
  obtain ⟨col,eqn,hc,he,hu⟩ := exists_unit_minor
  obtain ⟨b,hb,hab,hba,_,_,_,_⟩ := normal_elimination_for_minor col hc eqn hu
  let c := freeFrame R0 col
  let Y : V → MvPowerSeries Z R0 := fun x => subst c (b x)
  have hc0 := centered_freeFrame R0 col
  have hs := hasSubst_of_constantCoeff_zero hc0
  have hY (x : V) : constantCoeff (Y x) = 0 := constantCoeff_subst_eq_zero hs hc0 (hb x)
  let g := (substAlgHom (hasSubst_of_constantCoeff_zero hY)).toRingHom
  have hg : Function.Surjective g ∧ RingHom.ker g ≤ idealAt (strassenSquare R0) :=
    frozen_residual_map_of_free_bijective col hc eqn (frame_subst_bijective col hc eqn hu) b hb hab hba
  have hi : (idealAt (strassenSquare R0)).map g = residualIdeal Y := by
    rw [idealAt, Ideal.map_span, ← Set.range_comp]
    rfl
  refine ⟨col,eqn,Y,hc,he,hY,inverse_in_frame col hc eqn b hb hab, ?_, ?_, ?_⟩
  · intro j
    change subst (fun x => subst c (b x)) (eqAt (strassenSquare R0) (eqn j)) = 0
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hs,
      ← newCoord_col (strassenSquare R0) col hc eqn j, hba (col j), subst_X hs]
    classical
    simp [c, freeFrame, Set.mem_range_self]
  · intro e
    rw [map_subst_centered rho3 hY, map_eqAt_square]
  · exact ⟨(residualQuotientEquiv g hg.1 _ hg.2).trans (Ideal.quotEquivOfEq hi)⟩

/-- The free-frame matrix stays invertible after any coefficient map out of
Z_(3).  Its entries are the actual integer frame entries. -/
theorem frame_subst_bijective_baseChange {K : Type} [CommRing K] [Nontrivial K]
    (rho : R0 →+* K) (col : Fin 2101 → V) (hc : Function.Injective col)
    (eqn : Fin 2101 → E) (hu : IsUnit (minorAt (strassenSquare R0) col eqn).det) :
    Function.Bijective (subst (fun x : Free col => frameLinear K x)) := by
  classical
  let e : Z ≃ Free col := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, card_free col hc])
  apply subst_bijective_equiv e (fun x => centered_frameLinear K x)
  rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_submatrix_equiv_self e]
  have he : (Matrix.of fun (x j : Free col) =>
      coeff (single (e.symm j) 1) (frameLinear K x.val)).submatrix e e =
        ((minorInt (fun i => (e i).val) id).map (Int.cast : ℤ → R0)).map rho := by
    ext i j
    simp [coeff_frameLinear, minorInt, fR, map_intCast]
  rw [he, ← RingHom.map_det]
  exact (free_frame_unit col hc eqn hu e).map rho

/-- All centered cubic equations commute with coefficient change from Z_(3). -/
theorem map_eqAt_integral {K : Type} [CommRing K] [Nontrivial K]
    (rho : R0 →+* K) (e : E) :
    MvPowerSeries.map rho (eqAt (strassenSquare R0) e) = eqAt (strassenSquare K) e := by
  have hc (x : V) : rho ((strassenSquare R0).coordinates x) =
      (strassenSquare K).coordinates x := by
    obtain ⟨s,m,a⟩ := x
    cases m <;> simp [strassenSquare, Decomposition.map, Decomposition.coordinates, map_intCast]
  have ht : rho (matrixMultiplicationEntry R0 e.1 e.2.1 e.2.2) =
      matrixMultiplicationEntry K e.1 e.2.1 e.2.2 := by
    unfold matrixMultiplicationEntry
    split_ifs <;> simp
  simp only [eqAt, equation, map_sub, map_sum, map_mul, MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_C, map_add, MvPowerSeries.map_C, MvPowerSeries.map_X, hc, ht]

theorem map_newCoord_integral {K : Type} [CommRing K] [Nontrivial K]
    (rho : R0 →+* K) (col : Fin 2101 → V) (hc : Function.Injective col)
    (eqn : Fin 2101 → E) (x : V) :
    MvPowerSeries.map rho (newCoord (strassenSquare R0) col hc eqn x) =
      newCoord (strassenSquare K) col hc eqn x := by
  classical
  by_cases hx : x ∈ Set.range col
  · obtain ⟨i,rfl⟩ := hx
    rw [newCoord_col, newCoord_col, map_eqAt_integral]
  · let y : Free col := ⟨x,hx⟩
    change MvPowerSeries.map rho (newCoord (strassenSquare R0) col hc eqn y) =
      newCoord (strassenSquare K) col hc eqn y
    simp only [newCoord_free, MvPowerSeries.map_X]

theorem map_freeFrame_integral {K : Type} [CommRing K]
    (rho : R0 →+* K) (col : Fin 2101 → V) (x : V) :
    MvPowerSeries.map rho (freeFrame R0 col x) = freeFrame K col x := by
  classical
  unfold freeFrame
  split_ifs
  · simp
  · simp [frameLinear, fR, smul_eq_C_mul, map_sum, map_mul, map_intCast]

/-- The residual presentation is compatible with *the same* selected minor,
normal inverse and frozen frame after every specialization of the integral
coefficient ring to a field. The isomorphism has source the actual adic
completion, by `sqEquiv`, not a separately defined model of the germ. -/
theorem normal_elimination_completion_baseChange :
    ∃ (col : Fin 2101 → V) (eqn : Fin 2101 → E) (Y : V → MvPowerSeries Z R0),
      Function.Injective col ∧ Function.Injective eqn ∧
      (∀ x, constantCoeff (Y x) = 0) ∧
      (∀ x, LowZero 2 (Y x - frameLinear R0 x)) ∧
      (∀ j, subst Y (eqAt (strassenSquare R0) (eqn j)) = 0) ∧
      Nonempty (AhatAt (strassenSquare R0) ≃+* (MvPowerSeries Z R0 ⧸ residualIdeal Y)) ∧
      ∀ (K : Type) [Field K] (rho : R0 →+* K),
        let YK : V → MvPowerSeries Z K := fun x => MvPowerSeries.map rho (Y x)
        (∀ x, constantCoeff (YK x) = 0) ∧
        (∀ e : E, MvPowerSeries.map rho (subst Y (eqAt (strassenSquare R0) e)) =
          subst YK (eqAt (strassenSquare K) e)) ∧
        Nonempty (SquareCompletion K ≃+* (MvPowerSeries Z K ⧸ residualIdeal YK)) := by
  obtain ⟨col,eqn,hc,he,hu⟩ := exists_unit_minor
  obtain ⟨b,hb,hab,hba,_,_,_,_⟩ := normal_elimination_for_minor col hc eqn hu
  let c := freeFrame R0 col
  let Y : V → MvPowerSeries Z R0 := fun x => subst c (b x)
  have hc0 := centered_freeFrame R0 col
  have hs := hasSubst_of_constantCoeff_zero hc0
  have hY (x : V) : constantCoeff (Y x) = 0 := constantCoeff_subst_eq_zero hs hc0 (hb x)
  let g := (substAlgHom (hasSubst_of_constantCoeff_zero hY)).toRingHom
  have hg := frozen_residual_map_of_free_bijective col hc eqn
    (frame_subst_bijective col hc eqn hu) b hb hab hba
  have hi : (idealAt (strassenSquare R0)).map g = residualIdeal Y := by
    rw [idealAt, Ideal.map_span, ← Set.range_comp]
    rfl
  refine ⟨col,eqn,Y,hc,he,hY,inverse_in_frame col hc eqn b hb hab,?_,
    ⟨(residualQuotientEquiv g hg.1 _ hg.2).trans (Ideal.quotEquivOfEq hi)⟩,?_⟩
  · intro j
    change subst (fun x => subst c (b x)) (eqAt (strassenSquare R0) (eqn j)) = 0
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hs,
      ← newCoord_col (strassenSquare R0) col hc eqn j, hba (col j), subst_X hs]
    classical
    simp [c, freeFrame, Set.mem_range_self]
  · intro K _ rho
    dsimp only
    let bK : V → MvPowerSeries V K := fun x => MvPowerSeries.map rho (b x)
    let YK : V → MvPowerSeries Z K := fun x => MvPowerSeries.map rho (Y x)
    have hbK (x : V) : constantCoeff (bK x) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, bK, coeff_map,
        coeff_zero_eq_constantCoeff_apply, hb x, map_zero]
    have hYK (x : V) : constantCoeff (YK x) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, YK, coeff_map,
        coeff_zero_eq_constantCoeff_apply, hY x, map_zero]
    have hy (x : V) : YK x = subst (freeFrame K col) (bK x) := by
      change MvPowerSeries.map rho (subst c (b x)) = _
      rw [map_subst_centered rho hc0]
      congr 1
      exact funext (map_freeFrame_integral rho col)
    obtain ⟨hbaK,habK⟩ := inverse_tuple_baseChange rho
      (newCoord (strassenSquare R0) col hc eqn) b
      (constantCoeff_newCoord _ (strassenSquare_solves R0) col hc eqn) hb hba hab
    rw [show (fun x => MvPowerSeries.map rho (newCoord (strassenSquare R0) col hc eqn x)) =
      newCoord (strassenSquare K) col hc eqn from funext (map_newCoord_integral rho col hc eqn)]
      at habK hbaK
    let gK := (substAlgHom (hasSubst_of_constantCoeff_zero hYK)).toRingHom
    have hgK : Function.Surjective gK ∧ RingHom.ker gK ≤ idealAt (strassenSquare K) := by
      have hh := frozen_residual_map_of_free_bijective col hc eqn
        (frame_subst_bijective_baseChange rho col hc eqn hu) bK hbK habK hbaK
      have hY' (x : V) : constantCoeff (subst (freeFrame K col) (bK x)) = 0 :=
        constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (centered_freeFrame K col))
          (centered_freeFrame K col) (hbK x)
      have hmap : gK = (substAlgHom (hasSubst_of_constantCoeff_zero hY')).toRingHom := by
        apply RingHom.ext
        intro f
        change subst YK f = subst (fun x => subst (freeFrame K col) (bK x)) f
        rw [funext hy]
      rw [hmap]
      exact hh
    have hiK : (idealAt (strassenSquare K)).map gK = residualIdeal YK := by
      rw [idealAt, Ideal.map_span, ← Set.range_comp]
      rfl
    refine ⟨hYK,fun e => ?_,?_⟩
    · rw [map_subst_centered rho hY, map_eqAt_integral]
    · exact ⟨(sqEquiv K).trans ((residualQuotientEquiv gK hgK.1 _ hgK.2).trans
        (Ideal.quotEquivOfEq hiK))⟩

/-- Every field in the paper receives the integral coefficient map. -/
theorem coefficientMap_exists (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    Nonempty (R0 →+* K) := by
  rcases hK with h | h
  · letI := h
    exact ⟨(ZMod.castHom (dvd_refl 3) K).comp rho3⟩
  · letI := h
    have hu (y : (Ideal.span {(3 : ℤ)}).primeCompl) :
        IsUnit ((Int.castRingHom K) y) := by
      apply Ne.isUnit
      intro hz
      have hy : (y : ℤ) = 0 := Int.cast_injective (R := K) (by simpa using hz)
      exact y.2 (by rw [hy]; exact Ideal.zero_mem _)
    exact ⟨IsLocalization.lift (M := (Ideal.span {(3 : ℤ)}).primeCompl) (S := R0) hu⟩

/-- The explicit completed-local-ring quotient for every field in the
paper. The linear frame and the integral origin are specified, rather
than asserting existence of an arbitrary presentation. -/
theorem completion_frozen_residual_quotient (K : Type) [Field K]
    (hK : CharP K 3 ∨ CharZero K) :
    ∃ (Y : V → MvPowerSeries Z R0) (rho : R0 →+* K),
      (∀ x, LowZero 2 (Y x - frameLinear R0 x)) ∧
      Nonempty (SquareCompletion K ≃+* (MvPowerSeries Z K ⧸
        residualIdeal (fun x => MvPowerSeries.map rho (Y x)))) := by
  obtain ⟨col,eqn,Y,hc,he,hY,hlin,hsel,hint,hall⟩ := normal_elimination_completion_baseChange
  obtain ⟨rho⟩ := coefficientMap_exists K hK
  exact ⟨Y,rho,hlin,(hall K rho).2.2⟩

end Brent.Formal.NormalEliminationZ3
