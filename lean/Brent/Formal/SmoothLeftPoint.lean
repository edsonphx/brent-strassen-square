import Brent.SmoothLMinor
import Brent.Formal.SmoothLeftMinor
import Brent.Formal.SmoothLocal

/-!
# The smooth point `q_L` (§7, lines 621–642)

`q_L` is the left value of the block point `pqInt` (blocks 4 and 5 at `t = 1`). Over every field
of characteristic three or zero:

* the Jacobian at `q_L` has rank exactly 2155, so the tangent space has dimension 197;
* the local ring of the Brent scheme at `q_L` has Krull dimension 197;
* the formal neighbourhood `Â_{q_L}` is a power series ring in 197 variables.

The rank lower bound is the 2155 × 2155 minor of `Brent.SmoothLMinor`. The tangent lower bound
is 197 group directions whose minor on the free variables is triangular with diagonal `±1`
(`Brent.Formal.SmoothLeftMinor`). The theorems take the kernel check of the radix certificate as
the hypothesis `hchk`; `Brent.Formal.SmoothPoints` discharges it with `SmoothLChecks.checked`.
-/

open MvPowerSeries
open scoped BigOperators

namespace Brent.Formal.SmoothLeftPoint

open Brent Brent.Formal Brent.SmoothL Brent.Formal.SmoothLeftMinor

set_option linter.unusedSectionVars false

variable (k : Type) [Field k]

/-- The block point `pqInt` over `k`. -/
noncomputable abbrev pqk : FamilyParameters k := pqInt.map (Int.castRingHom k)

/-- The point `q_L`. -/
noncomputable abbrev qL : Decomposition k SquareVertex SquareSummand := (pqk k).value true

theorem pqk_global : (pqk k).global = fun _ => 1 := by
  funext g; apply Units.ext
  simp [pqk, FamilyParameters.map, pqInt]

theorem pqk_scale : (pqk k).scale = fun _ _ => 1 := by
  funext s c; apply Units.ext
  simp [pqk, FamilyParameters.map, pqInt]

theorem qL_eq : qL k = pointDec.map (Int.castRingHom k) := by
  rw [qL, ← FamilyParameters.value_map, pqInt_value_left]

/-- **(a)** `q_L` is a solution of the Brent equations. -/
theorem qL_solves : (qL k).Solves := FamilyParameters.value_solves _ _

theorem jacobianColumn_qL (x : Var) (e : EquationIndex SquareVertex) :
    (qL k).jacobianColumn x e.1 e.2.1 e.2.2 = (pointDec.jacobianColumn x e.1 e.2.1 e.2.2 : k) := by
  rw [qL_eq, Decomposition.jacobianColumn_map]; rfl

/-! ### Jacobian rank and tangent dimension -/

/-- The differential of the Brent equations at a point. -/
noncomputable def differentialAt (q : Decomposition k SquareVertex SquareSummand) :
    (Var → k) →ₗ[k] (EquationIndex SquareVertex → k) :=
  Matrix.mulVecLin (fun e x => q.jacobianColumn x e.1 e.2.1 e.2.2)

/-- The span of the Jacobian columns at a point. -/
noncomputable abbrev jacobianSpan (q : Decomposition k SquareVertex SquareSummand) :
    Submodule k (EquationIndex SquareVertex → k) :=
  Submodule.span k (Set.range fun x : Var => fun e : EquationIndex SquareVertex =>
    q.jacobianColumn x e.1 e.2.1 e.2.2)

theorem range_differentialAt (q : Decomposition k SquareVertex SquareSummand) :
    LinearMap.range (differentialAt k q) = jacobianSpan k q := by
  rw [differentialAt, Matrix.range_mulVecLin]
  rfl

theorem rank_add_nullity (q : Decomposition k SquareVertex SquareSummand) :
    Module.finrank k (jacobianSpan k q) + Module.finrank k (LinearMap.ker (differentialAt k q)) =
      2352 := by
  have h := (differentialAt k q).finrank_range_add_finrank_ker
  rw [range_differentialAt, Module.finrank_fintype_fun_eq_card, square_variable_count] at h
  exact h

/-- The tangent vector of the `i`-th chosen group parameter at `q_L`. -/
noncomputable def tangentVec (i : Fin 197) : Var → k := fun x => qTangent (pqk k) true (params i) x

theorem forget_comp_constant : (Jets.forget k).comp (Jets.constant k) = RingHom.id k := by
  ext; rfl

theorem tangentVec_mem_ker (i : Fin 197) : tangentVec k i ∈ LinearMap.ker (differentialAt k (qL k)) := by
  set d := (((pqk k).map (Jets.constant k)).mul (qUnit (params i))).value true
  have hd : d.Solves := FamilyParameters.value_solves _ _
  have hc : d.constantPart = qL k := by
    have : d.constantPart = d.map (Jets.forget k) := rfl
    rw [this, FamilyParameters.value_map, FamilyParameters.map_mul, FamilyParameters.map_comp,
      forget_comp_constant, FamilyParameters.map_id, qUnit_base, FamilyParameters.mul_one]
  have ht : ∀ x, d.tangentPart.coordinates x = tangentVec k i x := by
    intro x
    rw [tangentVec, ← snd_qUnit_value k (pqk k) (pqk_global k) (pqk_scale k) true (params i) x]
    obtain ⟨s, m, a⟩ := x
    cases m <;> rfl
  rw [LinearMap.mem_ker]
  funext e
  have h0 := Decomposition.tangent_satisfies_differential d hd e.1 e.2.1 e.2.2
  rw [hc, Decomposition.jacobianEntry_eq_sum] at h0
  simp only [differentialAt, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← h0]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ht, mul_comm]

/-- The tangent matrix restricted to the free variables is the cast of the integer minor. -/
theorem tangentVec_free (i j : Fin 197) :
    tangentVec k i (freeVar j) = (SmoothLeftMinor.minor.map (Int.castRingHom k)) i j := by
  rw [tangentVec, qTangent_map, qTangent_pqInt_left]
  rfl

theorem tangentVec_independent : LinearIndependent k (tangentVec k) := by
  have h : LinearIndependent k (SmoothLeftMinor.minor.map (Int.castRingHom k)).row :=
    Matrix.linearIndependent_rows_of_isUnit (isUnit_minor_map k)
  apply LinearIndependent.of_comp (LinearMap.funLeft k k freeVar)
  convert h using 1
  funext i j
  exact tangentVec_free k i j

theorem nullity_ge : 197 ≤ Module.finrank k (LinearMap.ker (differentialAt k (qL k))) := by
  have h := finrank_span_eq_card (tangentVec_independent k)
  rw [Fintype.card_fin] at h
  rw [← h]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact tangentVec_mem_ker k i

variable {k}

/-- The selected Jacobian columns at `q_L`, restricted to the selected equations. -/
theorem rank_ge (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    2155 ≤ Module.finrank k (jacobianSpan k (qL k)) := by
  let colVec : Fin 2155 → EquationIndex SquareVertex → k := fun i e =>
    (qL k).jacobianColumn (col i) e.1 e.2.1 e.2.2
  have hli : LinearIndependent k colVec := by
    have hu : IsUnit (minorInt.map (Int.castRingHom k)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have h : LinearIndependent k (minorInt.map (Int.castRingHom k)).row :=
      Matrix.linearIndependent_rows_of_isUnit hu
    apply LinearIndependent.of_comp (LinearMap.funLeft k k eqn)
    convert h using 1
    funext i j
    simp only [colVec, Function.comp_apply, LinearMap.funLeft_apply, jacobianColumn_qL,
      Matrix.row, Matrix.map_apply, minorInt, Matrix.of_apply]
    rfl
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h
  rw [← h]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨col i, rfl⟩

/-- **(b)** The Jacobian at `q_L` has rank exactly 2155. -/
theorem jacobian_rank (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    Module.finrank k (jacobianSpan k (qL k)) = 2155 := by
  have h1 := rank_add_nullity k (qL k)
  have h2 := nullity_ge k
  have h3 := rank_ge hdet
  omega

/-- **(c)** The tangent space at `q_L` has dimension 197. -/
theorem tangent_dimension (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    Module.finrank k (LinearMap.ker (differentialAt k (qL k))) = 197 := by
  have h1 := rank_add_nullity k (qL k)
  have h2 := jacobian_rank hdet
  omega

/-- **(d)** The local ring of the Brent scheme at `q_L` has Krull dimension 197. -/
theorem local_dimension (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    ringKrullDim (PointLocalRing (qL k) (qL_solves k)) = 197 := by
  apply le_antisymm
  · have h := pointLocalDimension_le (qL k) (qL_solves k)
    rw [square_variable_count] at h
    have hr : Module.finrank k (Submodule.span k (Set.range fun x : Var =>
        fun e : EquationIndex SquareVertex => (qL k).jacobianColumn x e.1 e.2.1 e.2.2)) = 2155 :=
      jacobian_rank hdet
    rw [hr] at h
    exact h
  · have hli : LinearIndependent k
        (Matrix.of fun i x => qTangent (pqk k) true (params i) x).row :=
      tangentVec_independent k
    exact_mod_cast le_localDimension_of_tangents k params (pqk k) (pqk_global k) (pqk_scale k)
      true hli

/-! ### The formal neighbourhood -/

section Formal

variable (k)

/-- The 197 chosen parameters as power series variables. -/
noncomputable def tPar (w : GrpIdx) : MvPowerSeries (Fin 197) k :=
  ∑ i, if params i = w then X i else 0

theorem tPar_centered : QCentered (tPar k) := by
  intro w
  simp [tPar, map_sum, apply_ite constantCoeff]

theorem jetAt_tPar (v : Fin 197) (w : GrpIdx) :
    jetAt v (tPar k w) = if w = params v then DualNumber.eps else 0 := by
  rw [tPar, map_sum]
  simp only [apply_ite (jetAt v), jetAt_X, map_zero]
  by_cases hw : w = params v
  · rw [if_pos hw, Finset.sum_eq_single v]
    · simp [hw]
    · intro i _ hi; simp [hi]
    · simp
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = v
    · subst hi; simp [Ne.symm hw]
    · simp [hi]

/-- The free variables as the variables outside the pivot columns. -/
noncomputable def freeEquiv : Fin 197 ≃ Free col := by
  classical
  refine Equiv.ofBijective (fun i => ⟨freeVar i, freeVar_not_col i⟩) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j h => freeVar_injective (congrArg Subtype.val h), ?_⟩
  rw [Fintype.card_fin, Fintype.card_compl_set, square_variable_count,
    Set.card_range_of_injective col_injective, Fintype.card_fin]

theorem freeEquiv_val (i : Fin 197) : (freeEquiv i).1 = freeVar i := rfl

/-- The family comorphism restricted to the 197 chosen parameters. -/
noncomputable def rho : AhatAt (qL k) →ₐ[k] MvPowerSeries (Fin 197) k :=
  qHat (pqk k) true (tPar_centered k)

theorem rho_surjective : Function.Surjective (rho k) := by
  letI : Fintype (Free col) := Fintype.ofEquiv (Fin 197) freeEquiv
  letI : DecidableEq (Free col) := Subtype.instDecidableEq
  let a : Free col → MvPowerSeries (Fin 197) k := fun x => qArg (pqk k) true (tPar k) (tPar_centered k) x.1
  have ha0 : ∀ x, constantCoeff (a x) = 0 := fun x => constantCoeff_qArg _ true _ _
  have hA : IsUnit (Matrix.of fun x v => coeff (Finsupp.single ((freeEquiv).symm v) 1) (a x)) := by
    have hM : (Matrix.of fun x v => coeff (Finsupp.single ((freeEquiv).symm v) 1) (a x)) =
        (Matrix.transpose (SmoothLeftMinor.minor.map (Int.castRingHom k))).submatrix (freeEquiv).symm
          (freeEquiv).symm := by
      ext x v
      simp only [a, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
      rw [coeff_qArg (pqk k) (pqk_global k) (pqk_scale k) true (tPar_centered k)
        ((freeEquiv).symm v) (params ((freeEquiv).symm v)) (jetAt_tPar k _)]
      have hx : x.1 = freeVar ((freeEquiv).symm x) := by
        rw [← freeEquiv_val, Equiv.apply_symm_apply]
      rw [hx]
      exact tangentVec_free k _ _
    rw [hM, Matrix.isUnit_submatrix_equiv, Matrix.isUnit_transpose]
    exact isUnit_minor_map k
  have hbij := subst_bijective_equiv (k := k) (freeEquiv) ha0 hA
  intro g
  obtain ⟨f, rfl⟩ := hbij.2 g
  have hX : HasSubst (fun x : Free col => (X x.1 : MvPowerSeries Var k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨Ideal.Quotient.mk _ (subst (fun x : Free col => (X x.1 : MvPowerSeries Var k)) f), ?_⟩
  rw [rho, qHat_mk, subst_comp_subst_apply hX (hasSubst_qArg _ true _)]
  congr 1
  funext x
  rw [subst_X (hasSubst_qArg _ true _)]

variable {k}

/-- **(e)** `Â_{q_L} ≃ k⟦z₁,…,z₁₉₇⟧`: the point `q_L` is smooth. -/
noncomputable def ahatEquiv (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    AhatAt (qL k) ≃ₐ[k] MvPowerSeries (Fin 197) k :=
  have hdet' : (minorAt (qL k) col eqn).det ≠ 0 := by
    have : minorAt (qL k) col eqn = Matrix.transpose (minorInt.map (Int.castRingHom k)) := by
      ext i j
      simp only [minorAt, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply, minorInt,
        jacobianColumn_qL]
      rfl
    rw [this, Matrix.det_transpose]
    exact hdet
  (AlgEquiv.ofBijective _ (freeMap_bijective (qL k) (qL_solves k) col col_injective eqn hdet'
    (rho k).toRingHom (rho_surjective k) (freeEquiv))).symm.trans
    (renameEquiv k (freeEquiv).symm)

end Formal

end Brent.Formal.SmoothLeftPoint
