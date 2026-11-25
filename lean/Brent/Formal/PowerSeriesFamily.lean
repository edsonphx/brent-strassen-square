import Brent.Formal.Overlap
import Brent.KernelCheck.FamilyQuadratics
import Brent.KernelCheck.LowerBound
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Finsupp.Antidiagonal

/-!
# The two exact families over power series

The variables are indexed by `Fin 251 ⊕ N`: one per frame direction, plus extra variables `N`
that the families do not use (later, the normal directions). In each chart, every global, block
and scale parameter is `1 + Σᵢ tᵢ Eᵢ`. Here `tᵢ` is the variable of frame direction `i` when `i`
belongs to the chart and `0` otherwise, and `Eᵢ` is the derivative of the exact chart along
direction `i`. These parameters are units, so each chart gives an exact solution of the Brent
equations over `k⟦Fin 251 ⊕ N⟧`. The first-order jet along a variable recovers the frame
direction, which computes the linear part.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries TangentData Finsupp

set_option linter.unusedSectionVars false

variable (k : Type) [Field k] (N : Type)

/-- The ambient power series ring. -/
abbrev PS := MvPowerSeries (Fin 251 ⊕ N) k

instance (i : Fin 251) (left : Bool) : Decidable (InChart i left) := by
  unfold InChart; infer_instance

/-! ### First-order jets -/

section Jet

variable {k} {W : Type} [DecidableEq W]

theorem coeff_single_mul (w : W) (f g : MvPowerSeries W k) :
    coeff (single w 1) (f * g) =
      constantCoeff f * coeff (single w 1) g + coeff (single w 1) f * constantCoeff g := by
  rw [coeff_mul, Finsupp.antidiagonal_single]
  simp only [Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map, Finset.Nat.antidiagonal_succ,
    zero_add, Finset.Nat.antidiagonal_zero, Finset.sum_cons, Finset.sum_singleton,
    Function.Embedding.coeFn_mk, Function.Embedding.refl_apply, Finsupp.single_zero,
    ← coeff_zero_eq_constantCoeff_apply, Finset.map_singleton]

/-- The first-order jet along the variable `w`. -/
noncomputable def jetAt (w : W) : MvPowerSeries W k →+* DualNumber k where
  toFun f := (constantCoeff f, coeff (single w 1) f)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change coeff (single w 1) (1 : MvPowerSeries W k) = 0
      rw [coeff_one, if_neg (by simp)]
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · simp
    · change coeff (single w 1) (f * g) = _
      rw [coeff_single_mul, DualNumber.snd_mul]
      change _ = constantCoeff f * coeff (single w 1) g + coeff (single w 1) f * constantCoeff g
      ring
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by apply TrivSqZeroExt.ext <;> simp

theorem jetAt_fst (w : W) (f : MvPowerSeries W k) : (jetAt w f).fst = constantCoeff f := rfl

theorem jetAt_snd (w : W) (f : MvPowerSeries W k) : (jetAt w f).snd = coeff (single w 1) f :=
  rfl

theorem jetAt_C (w : W) (r : k) : jetAt w (C r) = TrivSqZeroExt.inl r := by
  apply TrivSqZeroExt.ext
  · simp [jetAt_fst]
  · rw [jetAt_snd, coeff_C, if_neg (by simp)]; rfl

theorem jetAt_X (w v : W) : jetAt w (X v : MvPowerSeries W k) = if v = w then DualNumber.eps else 0 := by
  apply TrivSqZeroExt.ext
  · rw [jetAt_fst, constantCoeff_X]; split_ifs <;> simp
  · rw [jetAt_snd, coeff_X]
    by_cases h : v = w
    · subst h; simp
    · rw [if_neg (fun e => h (Finsupp.single_left_injective one_ne_zero e).symm), if_neg h]; rfl

end Jet

/-! ### The parameters -/

/-- The variable of frame direction `i` when `i` is selected. -/
noncomputable def selVar (P : Fin 251 → Prop) [DecidablePred P] (i : Fin 251) : PS k N :=
  if P i then X (Sum.inl i) else 0

noncomputable def tGlobal (g : Fin 3) (i : Fin 251) : Matrix SquareVertex SquareVertex k :=
  fun a b => (((castOrigin k i).global g).val a b).snd

noncomputable def tBlock (s : Fin 7) (g : Fin 3) (i : Fin 251) : Matrix (Fin 2) (Fin 2) k :=
  fun a b => (((castOrigin k i).block s g).val a b).snd

noncomputable def tScale (s : SquareSummand) (c : Fin 2) (i : Fin 251) : k :=
  (((castOrigin k i).scale s c).val).snd

theorem constantCoeff_selVar (P : Fin 251 → Prop) [DecidablePred P] (i : Fin 251) :
    constantCoeff (selVar k N P i) = 0 := by
  unfold selVar; split_ifs <;> simp

/-- An assignment of a power series with zero constant term to each frame direction. -/
def Assignment (W : Type) := {t : Fin 251 → MvPowerSeries W k // ∀ i, constantCoeff (t i) = 0}

/-- The assignment of a selection of directions. -/
noncomputable def selAssign (P : Fin 251 → Prop) [DecidablePred P] : Assignment k (Fin 251 ⊕ N) :=
  ⟨selVar k N P, constantCoeff_selVar k N P⟩

section Params

variable {k} {W : Type} {α : Type} [Fintype α] [DecidableEq α]

/-- `1 + Σᵢ tᵢ Eᵢ`. -/
noncomputable def psMat (t : Assignment k W) (E : Fin 251 → Matrix α α k) :
    Matrix α α (MvPowerSeries W k) :=
  1 + ∑ i, t.1 i • (E i).map C

theorem psMat_apply (t : Assignment k W) (E : Fin 251 → Matrix α α k) (a b : α) :
    psMat t E a b = (1 : Matrix α α (MvPowerSeries W k)) a b + ∑ i, t.1 i * C (E i a b) := by
  simp [psMat, Matrix.sum_apply]

theorem map_constantCoeff_psMat (t : Assignment k W) (E : Fin 251 → Matrix α α k) :
    (psMat t E).map constantCoeff = 1 := by
  ext a b
  rw [Matrix.map_apply, psMat_apply, map_add, map_sum]
  simp [t.2, Matrix.one_apply, apply_ite constantCoeff]

theorem isUnit_psMat (t : Assignment k W) (E : Fin 251 → Matrix α α k) : IsUnit (psMat t E) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
    RingHom.mapMatrix_apply, map_constantCoeff_psMat, Matrix.det_one]
  exact isUnit_one

/-- `1 + Σᵢ tᵢ eᵢ`. -/
noncomputable def psScal (t : Assignment k W) (e : Fin 251 → k) : MvPowerSeries W k :=
  1 + ∑ i, t.1 i * C (e i)

theorem constantCoeff_psScal (t : Assignment k W) (e : Fin 251 → k) :
    constantCoeff (psScal t e) = 1 := by
  simp [psScal, map_sum, t.2]

theorem isUnit_psScal (t : Assignment k W) (e : Fin 251 → k) : IsUnit (psScal t e) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_psScal]; exact isUnit_one

end Params

/-- The parameters attached to an assignment. -/
noncomputable def paramsOf {W : Type} (t : Assignment k W) : FamilyParameters (MvPowerSeries W k) :=
  ⟨fun g => (isUnit_psMat t (tGlobal k g)).unit,
   fun s g => (isUnit_psMat t (tBlock k s g)).unit,
   fun s c => (isUnit_psScal t (tScale k s c)).unit⟩

/-- The parameters of a chart over the power series ring. -/
noncomputable def psParams (left : Bool) : FamilyParameters (PS k N) :=
  paramsOf k (selAssign k N fun i => InChart i left)

/-- The exact family on a selection of directions, built in a chart. -/
noncomputable def selFamily (P : Fin 251 → Prop) [DecidablePred P] (left : Bool) :
    Decomposition (PS k N) SquareVertex SquareSummand :=
  (paramsOf k (selAssign k N P)).value left

/-- The exact family of a chart over the power series ring. -/
noncomputable def psFamily (left : Bool) : Decomposition (PS k N) SquareVertex SquareSummand :=
  (psParams k N left).value left

theorem psFamily_solves (left : Bool) : (psFamily k N left).Solves :=
  FamilyParameters.value_solves left _

/-! ### Changing the variables -/

section Maps

variable {k} {W W' : Type}

/-- Transport an assignment along a ring map fixing constants. -/
noncomputable def Assignment.map (t : Assignment k W) (φ : MvPowerSeries W k →+* MvPowerSeries W' k)
    (hφ : ∀ f, constantCoeff f = 0 → constantCoeff (φ f) = 0) : Assignment k W' :=
  ⟨fun i => φ (t.1 i), fun i => hφ _ (t.2 i)⟩

theorem paramsOf_map (t : Assignment k W) (φ : MvPowerSeries W k →+* MvPowerSeries W' k)
    (hC : ∀ r, φ (C r) = C r) (hφ : ∀ f, constantCoeff f = 0 → constantCoeff (φ f) = 0) :
    (paramsOf k t).map φ = paramsOf k (t.map φ hφ) := by
  simp only [paramsOf, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change φ (psMat t (tGlobal k g) a b) = psMat (t.map φ hφ) (tGlobal k g) a b
    rw [psMat_apply, psMat_apply, map_add, map_sum]
    simp only [map_mul, hC, Assignment.map]
    congr 1
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change φ (psMat t (tBlock k s g) a b) = psMat (t.map φ hφ) (tBlock k s g) a b
    rw [psMat_apply, psMat_apply, map_add, map_sum]
    simp only [map_mul, hC, Assignment.map]
    congr 1
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  · funext s c; apply Units.ext
    change φ (psScal t (tScale k s c)) = psScal (t.map φ hφ) (tScale k s c)
    simp only [psScal, map_add, map_one, map_sum, map_mul, hC, Assignment.map]

end Maps

/-! ### The orbit directions have trivial blocks -/

theorem tBlock_orbit (s : Fin 7) (g : Fin 3) (i : Fin 251) (hi : i.val < 143) :
    tBlock k s g i = 0 := by
  ext a b
  simp only [tBlock, castOrigin, frameOrigin, if_pos hi]
  split_ifs <;>
    simp [FamilyParameters.termUnit, FamilyParameters.globalUnit, FamilyParameters.map,
      FamilyParameters.one, Matrix.one_apply, apply_ite TrivSqZeroExt.snd]

/-- An assignment that only uses the orbit directions. -/
def OrbitOnly {W : Type} (t : Assignment k W) : Prop := ∀ i : Fin 251, 143 ≤ i.val → t.1 i = 0

theorem blockTrivial_of_orbitOnly {W : Type} (t : Assignment k W) (ht : OrbitOnly k t) :
    BlockTrivial (paramsOf k t) := by
  intro s g
  apply Units.ext
  change psMat t (tBlock k s g) = 1
  rw [psMat]
  conv_rhs => rw [← add_zero (1 : Matrix (Fin 2) (Fin 2) (MvPowerSeries W k))]
  congr 1
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < 143
  · rw [tBlock_orbit k s g i hi]; simp
  · rw [ht i (by omega), zero_smul]

/-- **Overlap over power series.** -/
theorem value_orbit_left_eq_right {W : Type} (t : Assignment k W) (ht : OrbitOnly k t) :
    (paramsOf k t).value true = (paramsOf k t).value false :=
  value_left_eq_right (blockTrivial_of_orbitOnly k t ht)

/-! ### Constant terms -/

theorem paramsOf_constantCoeff {W : Type} (t : Assignment k W) :
    (paramsOf k t).map constantCoeff = FamilyParameters.one k := by
  simp only [paramsOf, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; exact map_constantCoeff_psMat t _
  · funext s g; apply Units.ext; exact map_constantCoeff_psMat t _
  · funext s c; apply Units.ext; exact constantCoeff_psScal t _

/-- **Constant terms.** Every family passes through the recursive point. -/
theorem constantCoeff_value {W : Type} (t : Assignment k W) (left : Bool)
    (x : Variable SquareVertex SquareSummand) :
    constantCoeff (((paramsOf k t).value left).coordinates x) = (strassenSquare k).coordinates x := by
  rw [← LowerBound.coordinates_map, FamilyParameters.value_map, paramsOf_constantCoeff,
    FamilyParameters.value_one]

/-! ### The linear part -/

section Linear

variable {k N} (P : Fin 251 → Prop) [DecidablePred P]

theorem jetAt_selVar [DecidableEq N] (w : Fin 251 ⊕ N) (i : Fin 251) :
    jetAt w (selVar k N P i) = if P i ∧ Sum.inl i = w then DualNumber.eps else 0 := by
  unfold selVar
  by_cases h : P i
  · rw [if_pos h, jetAt_X]; simp [h]
  · rw [if_neg h, map_zero]; simp [h]

theorem jetAt_psMat [DecidableEq N] {α : Type} [Fintype α] [DecidableEq α]
    (w : Fin 251 ⊕ N) (E : Fin 251 → Matrix α α k) (a b : α) :
    jetAt w (psMat (selAssign k N P) E a b) =
      TrivSqZeroExt.inl ((1 : Matrix α α k) a b) +
        ∑ i, (if P i ∧ Sum.inl i = w then DualNumber.eps else 0) *
          TrivSqZeroExt.inl (E i a b) := by
  rw [psMat_apply, map_add, map_sum]
  simp only [selAssign, map_mul, jetAt_selVar, jetAt_C]
  congr 1
  by_cases h : a = b <;> simp [Matrix.one_apply, h]

theorem jetAt_psScal [DecidableEq N] (w : Fin 251 ⊕ N) (e : Fin 251 → k) :
    jetAt w (psScal (selAssign k N P) e) =
      1 + ∑ i, (if P i ∧ Sum.inl i = w then DualNumber.eps else 0) *
        TrivSqZeroExt.inl (e i) := by
  rw [psScal, map_add, map_one, map_sum]
  simp only [selAssign, map_mul, jetAt_selVar, jetAt_C]

/-- Along a selected direction the jet of the parameters is the exact chart's jet. -/
theorem params_jet [DecidableEq N] (j : Fin 251) (hj : P j) :
    (paramsOf k (selAssign k N P)).map (jetAt (Sum.inl j)) = castOrigin k j := by
  have hb := LowerBound.castOrigin_base' k j
  simp only [FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq] at hb
  have hsel : ∀ i : Fin 251, (P i ∧ (Sum.inl i : Fin 251 ⊕ N) = Sum.inl j) ↔ i = j :=
    fun i => ⟨fun h => Sum.inl_injective h.2, fun h => by subst h; exact ⟨hj, rfl⟩⟩
  change _ = FamilyParameters.mk (castOrigin k j).global (castOrigin k j).block
    (castOrigin k j).scale
  simp only [paramsOf, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((castOrigin k j).global g).val a b).fst =
        (1 : Matrix SquareVertex SquareVertex k) a b :=
      congrArg (fun u : (Matrix SquareVertex SquareVertex k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun hb.1 g)
    change jetAt (Sum.inl j) (psMat (selAssign k N P) (tGlobal k g) a b) = _
    rw [jetAt_psMat]
    simp only [hsel, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply TrivSqZeroExt.ext
    · simp [h1]
    · simp [tGlobal]
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((castOrigin k j).block s g).val a b).fst =
        (1 : Matrix (Fin 2) (Fin 2) k) a b :=
      congrArg (fun u : (Matrix (Fin 2) (Fin 2) k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun (congrFun hb.2.1 s) g)
    change jetAt (Sum.inl j) (psMat (selAssign k N P) (tBlock k s g) a b) = _
    rw [jetAt_psMat]
    simp only [hsel, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply TrivSqZeroExt.ext
    · simp [h1]
    · simp [tBlock]
  · funext s c; apply Units.ext
    have h1 : (((castOrigin k j).scale s c).val).fst = 1 :=
      congrArg (fun u : kˣ => (u : k)) (congrFun (congrFun hb.2.2 s) c)
    change jetAt (Sum.inl j) (psScal (selAssign k N P) (tScale k s c)) = _
    rw [jetAt_psScal]
    simp only [hsel, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply TrivSqZeroExt.ext
    · simp [h1]
    · simp [tScale]

/-- Along any other variable the jet of the parameters is trivial. -/
theorem params_jet_other [DecidableEq N] (w : Fin 251 ⊕ N) (hw : ∀ j, Sum.inl j = w → ¬ P j) :
    (paramsOf k (selAssign k N P)).map (jetAt w) = FamilyParameters.one _ := by
  have hsel : ∀ i : Fin 251, ¬ (P i ∧ (Sum.inl i : Fin 251 ⊕ N) = w) :=
    fun i h => hw i h.2 h.1
  simp only [paramsOf, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change jetAt w (psMat (selAssign k N P) (tGlobal k g) a b) = _
    rw [jetAt_psMat]
    simp [hsel, Matrix.one_apply, apply_ite TrivSqZeroExt.inl]
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change jetAt w (psMat (selAssign k N P) (tBlock k s g) a b) = _
    rw [jetAt_psMat]
    simp [hsel, Matrix.one_apply, apply_ite TrivSqZeroExt.inl]
  · funext s c; apply Units.ext
    change jetAt w (psScal (selAssign k N P) (tScale k s c)) = _
    rw [jetAt_psScal]
    simp [hsel]

theorem jetAt_coordinates [DecidableEq N] (left : Bool) (w : Fin 251 ⊕ N)
    (x : Variable SquareVertex SquareSummand) :
    jetAt w ((selFamily k N P left).coordinates x) =
      (((paramsOf k (selAssign k N P)).map (jetAt w)).value left).coordinates x := by
  rw [selFamily, ← FamilyParameters.value_map, LowerBound.coordinates_map]

theorem snd_strassenSquare (x : Variable SquareVertex SquareSummand) :
    ((strassenSquare (DualNumber k)).coordinates x).snd = 0 := by
  rw [strassenSquare, LowerBound.coordinates_map]
  simp

/-- **Linear part, selected directions.** -/
theorem coeff_sel_in [DecidableEq N] (left : Bool) (j : Fin 251) (hj : P j)
    (hjc : InChart j left) (x : Variable SquareVertex SquareSummand) :
    coeff (single (Sum.inl j) 1) ((selFamily k N P left).coordinates x) =
      (frameDirection k j).coordinates x := by
  rw [← jetAt_snd, jetAt_coordinates, params_jet P j hj, ← archived_origin k j left hjc]
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

/-- **Linear part, other variables.** -/
theorem coeff_sel_other [DecidableEq N] (left : Bool) (w : Fin 251 ⊕ N)
    (hw : ∀ j, Sum.inl j = w → ¬ P j) (x : Variable SquareVertex SquareSummand) :
    coeff (single w 1) ((selFamily k N P left).coordinates x) = 0 := by
  rw [← jetAt_snd, jetAt_coordinates, params_jet_other P w hw, FamilyParameters.value_one,
    snd_strassenSquare]

end Linear

end Brent.Formal
