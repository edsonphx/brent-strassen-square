import Brent.Formal.SmoothPoint
import Brent.PointTangents

/-!
# The recursive families near a block point

For a point `pq` of the parameter space with trivial global changes and scalings, the map
`t ↦ (pq · g(t)).value` with `g(t)` built from `1 + t` parameterizes the family near
`q = pq.value`. Its comorphism kills the Brent ideal at `q`, so it factors through `Â_q`.
Its linear part along a parameter is the tangent of the corresponding generator at `pq`,
which `Brent.PointTangents` computes in closed form.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries

set_option linter.unusedSectionVars false

/-- Parameters: global matrix units and term scalings (as in the orbit), and block matrix units. -/
abbrev GrpIdx := GIdx ⊕ (Fin 7 × Fin 3 × Fin 2 × Fin 2)

section Params

variable {k : Type} [Field k] {W : Type}

/-- The block factor `1 + (t_{l,g,a,b})`. -/
noncomputable def blkMat (t : GrpIdx → MvPowerSeries W k) (l : Fin 7) (g : Fin 3) :
    Matrix (Fin 2) (Fin 2) (MvPowerSeries W k) :=
  1 + Matrix.of fun a b => t (.inr (l, g, a, b))

def QCentered (t : GrpIdx → MvPowerSeries W k) : Prop := ∀ w, constantCoeff (t w) = 0

theorem centered_inl {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) :
    Centered (fun w => t (.inl w)) := fun w => ht _

theorem isUnit_blkMat {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) (l : Fin 7) (g : Fin 3) :
    IsUnit (blkMat t l g) := by
  have h : (blkMat t l g).map constantCoeff = 1 := by
    ext a b
    simp [blkMat, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply,
      apply_ite constantCoeff]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
    RingHom.mapMatrix_apply, h, Matrix.det_one]
  exact isUnit_one

/-- The group element with parameters `t`. -/
noncomputable def qGroup (t : GrpIdx → MvPowerSeries W k) (ht : QCentered t) :
    FamilyParameters (MvPowerSeries W k) :=
  ⟨fun g => (isUnit_orbMat (centered_inl ht) g).unit, fun l g => (isUnit_blkMat ht l g).unit,
   fun s c => (isUnit_orbScal (centered_inl ht) s c).unit⟩

/-- The tangent generator of a parameter. -/
noncomputable def qUnit : GrpIdx → FamilyParameters (DualNumber k)
  | .inl w => unitParams w
  | .inr (l, g, i, j) => FamilyParameters.blockUnit l g i j

theorem jetAt_one_apply [DecidableEq W] {n : Type} [DecidableEq n] (v : W) (a b : n) :
    jetAt v ((1 : Matrix n n (MvPowerSeries W k)) a b) =
      TrivSqZeroExt.inl ((1 : Matrix n n k) a b) := by
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

/-- **First-order jets of the group parameters.** -/
theorem qGroup_jet [DecidableEq W] {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) (v : W)
    (w₀ : GrpIdx) (h : ∀ w, jetAt v (t w) = if w = w₀ then DualNumber.eps else 0) :
    (qGroup t ht).map (jetAt v) = qUnit w₀ := by
  rcases w₀ with w₀ | ⟨l₀, g₀, i₀, j₀⟩
  · have h' : ∀ w, jetAt v (t (.inl w)) = if w = w₀ then DualNumber.eps else 0 := by
      intro w; rw [h]; simp
    have hO := orbParams_jet (centered_inl ht) v w₀ h'
    have hB : ∀ l g a b, jetAt v (blkMat t l g a b) = TrivSqZeroExt.inl ((1 : Matrix (Fin 2) (Fin 2) k) a b) := by
      intro l g a b
      rw [blkMat, Matrix.add_apply, map_add, Matrix.of_apply, h, if_neg (by simp)]
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    show _ = unitParams w₀
    rw [← hO]
    simp only [qGroup, orbParams, FamilyParameters.map, FamilyParameters.mk.injEq]
    refine ⟨by first | trivial | rfl, ?_, by first | trivial | rfl⟩
    funext l g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change jetAt v (blkMat t l g a b) = _
    rw [hB]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab] <;> rfl
  · have h' : ∀ w, jetAt v (t (.inl w)) = 0 := by
      intro w; rw [h]; simp
    have hM : ∀ g a b, jetAt v (orbMat (fun w => t (.inl w)) g a b) =
        TrivSqZeroExt.inl ((1 : Matrix SquareVertex SquareVertex k) a b) := by
      intro g a b
      rw [orbMat, Matrix.add_apply, map_add, Matrix.of_apply, h']
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have hS : ∀ s c, jetAt v (orbScal (fun w => t (.inl w)) s c) = 1 := by
      intro s c
      unfold orbScal
      split_ifs <;> simp [h']
    simp only [qGroup, FamilyParameters.map, qUnit, FamilyParameters.blockUnit,
      FamilyParameters.one, FamilyParameters.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
      change jetAt v (orbMat (fun w => t (.inl w)) g a b) = _
      rw [hM]
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    · funext l g; apply Units.ext; refine Matrix.ext fun a b => ?_
      change jetAt v (blkMat t l g a b) =
        (↑((FamilyParameters.blockUnit (R := k) l₀ g₀ i₀ j₀).block l g) :
          Matrix (Fin 2) (Fin 2) (DualNumber k)) a b
      rw [FamilyParameters.blockUnit_block]
      rw [blkMat, Matrix.add_apply, map_add, Matrix.of_apply, h, jetAt_one_apply]
      apply TrivSqZeroExt.ext
      · by_cases hl : l = l₀ <;> by_cases hab : a = b <;>
          simp [hl, hab, Matrix.one_apply, Decomposition.vertexUnit] <;> split_ifs <;> simp
      · by_cases hl : l = l₀
        · subst hl
          rw [if_pos rfl, matrixJet_val, Decomposition.vertexUnit]
          by_cases hg : g₀ = g
          · subst hg
            by_cases hab : i₀ = a ∧ j₀ = b
            · obtain ⟨rfl, rfl⟩ := hab; simp
            · rw [if_neg, if_pos rfl, Matrix.single_apply, if_neg hab]
              · simp
              · intro hc
                simp only [Sum.inr.injEq, Prod.mk.injEq] at hc
                exact hab ⟨hc.2.2.1.symm, hc.2.2.2.symm⟩
          · rw [if_neg, if_neg hg]
            · simp
            · intro hc
              simp only [Sum.inr.injEq, Prod.mk.injEq] at hc
              exact hg hc.2.1.symm
        · rw [if_neg hl, if_neg]
          · by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
          · intro hc
            simp only [Sum.inr.injEq, Prod.mk.injEq] at hc
            exact hl hc.1
    · funext s c; apply Units.ext
      change jetAt v (orbScal (fun w => t (.inl w)) s c) = 1
      exact hS s c

end Params

/-! ### The family through a block point -/

section Family

variable {k : Type} [Field k] {W : Type}
  (pq : FamilyParameters k) (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1)

/-- The family `t ↦ pq · g(t)` centered at `q = pq.value left`. -/
noncomputable def qArg (left : Bool) (t : GrpIdx → MvPowerSeries W k) (ht : QCentered t)
    (x : Var) : MvPowerSeries W k :=
  (((pq.map C).mul (qGroup t ht)).value left).coordinates x - C ((pq.value left).coordinates x)

theorem qGroup_constantCoeff {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) :
    (qGroup t ht).map constantCoeff = FamilyParameters.one k := by
  have hO := orbParams_constantCoeff (centered_inl ht)
  simp only [orbParams, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
    at hO
  simp only [qGroup, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨hO.1, ?_, hO.2.2⟩
  funext l g; apply Units.ext; ext a b
  change constantCoeff (blkMat t l g a b) = _
  simp [blkMat, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply,
    apply_ite constantCoeff]

theorem pq_map_C_constantCoeff :
    (pq.map (C (σ := W))).map constantCoeff = pq := by
  rw [FamilyParameters.map_comp]
  have : (constantCoeff (σ := W) (R := k)).comp C = RingHom.id k := by ext; simp
  rw [this, FamilyParameters.map_id]

theorem constantCoeff_qArg (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t)
    (x : Var) : constantCoeff (qArg pq left t ht x) = 0 := by
  rw [qArg, map_sub, ← LowerBound.coordinates_map, FamilyParameters.value_map,
    FamilyParameters.map_mul, pq_map_C_constantCoeff, qGroup_constantCoeff,
    FamilyParameters.mul_one, constantCoeff_C, sub_self]

theorem hasSubst_qArg (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) :
    HasSubst (qArg pq left t ht) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_qArg pq left ht)

/-- The comorphism of the family on `k⟦z⟧`. -/
noncomputable def qPull (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) :
    MvPowerSeries Var k →ₐ[k] MvPowerSeries W k :=
  substAlgHom (hasSubst_qArg pq left ht)

theorem qPull_eqAt (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t)
    (abc : EquationIndex SquareVertex) : qPull pq left ht (eqAt (pq.value left) abc) = 0 := by
  rw [qPull, eqAt, algHom_eval₂]
  have : (fun x => substAlgHom (hasSubst_qArg pq left ht)
      (C ((pq.value left).coordinates x) + X x)) =
      (((pq.map C).mul (qGroup t ht)).value left).coordinates := by
    funext x
    rw [map_add, algHom_C, substAlgHom_X, qArg]
    ring
  rw [this]
  exact eval_equation_solves _ (FamilyParameters.value_solves _ _) abc

/-- The comorphism factors through `Â_q`. -/
noncomputable def qHat (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) :
    AhatAt (pq.value left) →ₐ[k] MvPowerSeries W k :=
  Ideal.Quotient.liftₐ _ (qPull pq left ht) fun a ha => by
    have hle : idealAt (pq.value left) ≤ RingHom.ker (qPull pq left ht) := by
      rw [idealAt, Ideal.span_le]
      rintro _ ⟨abc, rfl⟩
      exact RingHom.mem_ker.mpr (qPull_eqAt pq left ht abc)
    exact RingHom.mem_ker.mp (hle ha)

theorem qHat_mk (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t)
    (f : MvPowerSeries Var k) :
    qHat pq left ht (Ideal.Quotient.mk _ f) = subst (qArg pq left t ht) f := by
  rw [qHat, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change substAlgHom (hasSubst_qArg pq left ht) f = _
  rw [substAlgHom_apply]

end Family

/-- The tangent of a parameter at `pq`, in closed form. -/
def qTangent {R : Type} [CommRing R] (pq : FamilyParameters R) (left : Bool) :
    GrpIdx → Var → R
  | .inl (.inl (g, i, j)), (s, m, (a, b)) => (pq.value left).vertexUnitCoefficient g i j s m a b
  | .inl (.inr (s₀, c)), (s, m, (a, b)) =>
      FamilyParameters.termUnitCoefficient (pq.value left) s₀ (decide (c = 1)) s m a b
  | .inr (l, g, i, j), (s, m, (a, b)) =>
      FamilyParameters.blockUnitCoefficientAt pq left l g i j s m a b

theorem qTangent_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (pq : FamilyParameters R) (left : Bool) (w : GrpIdx) (x : Var) :
    qTangent (pq.map f) left w x = f (qTangent pq left w x) := by
  obtain ⟨s, m, a, b⟩ := x
  rcases w with (⟨g, i, j⟩ | ⟨s₀, c⟩) | ⟨l, g, i, j⟩
  · exact FamilyParameters.globalCoefficientAt_map f pq left g i j s m a b
  · exact FamilyParameters.termCoefficientAt_map f pq left s₀ _ s m a b
  · exact FamilyParameters.blockUnitCoefficientAt_map f pq left l g i j s m a b

section Linear

variable {k : Type} [Field k] {W : Type} [DecidableEq W]
  (pq : FamilyParameters k) (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1)

theorem jetAt_comp_C (v : W) : (jetAt v).comp (C (σ := W) (R := k)) = Jets.constant k := by
  ext r
  · rfl
  · change coeff (Finsupp.single v 1) (C r : MvPowerSeries W k) = 0
    exact coeff_C_single v r

include hg hs in
/-- **The linear part of the family at `q`.** -/
theorem coeff_qArg (left : Bool) {t : GrpIdx → MvPowerSeries W k} (ht : QCentered t) (v : W)
    (w₀ : GrpIdx) (h : ∀ w, jetAt v (t w) = if w = w₀ then DualNumber.eps else 0) (x : Var) :
    coeff (Finsupp.single v 1) (qArg pq left t ht x) = qTangent pq left w₀ x := by
  rw [qArg, map_sub, coeff_C_single, sub_zero, ← jetAt_snd, ← LowerBound.coordinates_map,
    FamilyParameters.value_map, FamilyParameters.map_mul, FamilyParameters.map_comp,
    jetAt_comp_C, qGroup_jet ht v w₀ h]
  obtain ⟨s, m, a, b⟩ := x
  rcases w₀ with (⟨g, i, j⟩ | ⟨s₀, c⟩) | ⟨l, g, i, j⟩
  · rw [qTangent, ← FamilyParameters.globalUnit_tangentAt pq hg hs left g i j s m a b]
    cases m <;> rfl
  · rw [qTangent, ← FamilyParameters.termUnit_tangentAt pq hg hs left s₀ _ s m a b]
    cases m <;> rfl
  · rw [qTangent, ← FamilyParameters.blockUnit_tangentAt pq hg hs left l g i j s m a b]
    cases m <;> rfl

end Linear

end Brent.Formal
