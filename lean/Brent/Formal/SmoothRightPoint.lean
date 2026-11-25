import Brent.Formal.SmoothLeftPoint
import Brent.Formal.SmoothSwap

/-!
# The smooth point `q_R`

`q_R = pqInt.value false` is the swap of `q_L` (`swapDec_value_trivial`). The swap permutes the
variables (`piV`) and the equations (`Kp` in each slot), so it carries the Jacobian, the germ
family and the formal neighbourhood of `q_L` to those of `q_R`.
-/

open MvPowerSeries
open scoped BigOperators

namespace Brent.Formal.SmoothRightPoint

open Brent Brent.Formal Brent.SmoothL Brent.Formal.SmoothLeftMinor Brent.Formal.SmoothLeftPoint

set_option linter.unusedSectionVars false

variable {k : Type} [Field k]

/-- The swap on equation indices. -/
def eK : EquationIndex SquareVertex ≃ EquationIndex SquareVertex := Kp.prodCongr (Kp.prodCongr Kp)

theorem jacobianEntry_swapDec (p d : Decomposition k SquareVertex SquareSummand)
    (a b c : SquareVertex × SquareVertex) :
    (swapDec p).jacobianEntry (swapDec d) a b c = p.jacobianEntry d (Kp a) (Kp b) (Kp c) := by
  unfold Decomposition.jacobianEntry
  exact Fintype.sum_equiv Ks _ _ fun s => rfl

theorem swapDec_coordinateDirection (x : Var) :
    swapDec (Decomposition.coordinateDirection (R := k) x) =
      Decomposition.coordinateDirection (piV x) := by
  obtain ⟨s₀, m₀, a₀⟩ := x
  apply Decomposition.eq_of_components <;> funext s a <;>
    simp only [swapDec, Decomposition.coordinateDirection, piV, Prod.mk.injEq] <;>
    congr 1 <;> apply propext <;>
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> subst h1 h3 <;>
    exact ⟨rfl, h2, Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl rfl)⟩

theorem jacobianColumn_swapDec (p : Decomposition k SquareVertex SquareSummand) (x : Var)
    (a b c : SquareVertex × SquareVertex) :
    (swapDec p).jacobianColumn x a b c = p.jacobianColumn (piV x) (Kp a) (Kp b) (Kp c) := by
  unfold Decomposition.jacobianColumn
  rw [← jacobianEntry_swapDec, swapDec_coordinateDirection, piV_piV]

theorem jacobianSpan_swapDec (p : Decomposition k SquareVertex SquareSummand) :
    jacobianSpan k (swapDec p) = (jacobianSpan k p).map (LinearEquiv.funCongrLeft k k eK).toLinearMap := by
  rw [jacobianSpan, jacobianSpan, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨piV x, ?_⟩
    funext e
    simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, jacobianColumn_swapDec]
    rfl
  · rintro ⟨x, rfl⟩
    refine ⟨piV x, ?_⟩
    funext e
    simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, jacobianColumn_swapDec, piV_piV]
    rfl

theorem finrank_jacobianSpan_swapDec (p : Decomposition k SquareVertex SquareSummand) :
    Module.finrank k (jacobianSpan k (swapDec p)) = Module.finrank k (jacobianSpan k p) := by
  rw [jacobianSpan_swapDec, LinearEquiv.finrank_map_eq]

theorem qR_eq : (pqk k).value false = swapDec (qL k) :=
  (swapDec_value_trivial (pqk k) (pqk_global k) (pqk_scale k)).symm

/-- **(a)** `q_R` is a solution of the Brent equations. -/
theorem qR_solves : ((pqk k).value false).Solves := FamilyParameters.value_solves _ _

/-- **(b)** The Jacobian at `q_R` has rank exactly 2155. -/
theorem jacobian_rank (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    Module.finrank k (jacobianSpan k ((pqk k).value false)) = 2155 := by
  rw [qR_eq, finrank_jacobianSpan_swapDec]
  exact SmoothLeftPoint.jacobian_rank hdet

/-- **(c)** The tangent space at `q_R` has dimension 197. -/
theorem tangent_dimension (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    Module.finrank k (LinearMap.ker (differentialAt k ((pqk k).value false))) = 197 := by
  have h1 := rank_add_nullity k ((pqk k).value false)
  have h2 := jacobian_rank hdet
  omega

theorem le_local_dimension_swap :
    (197 : WithBot ℕ∞) ≤ ringKrullDim (PointLocalRing (swapDec (qL k)) (swapDec_solves (qL_solves k))) := by
  have hD : LinearIndependent k (Matrix.of fun i x => tangentVec k i (piV x)).row := by
    apply LinearIndependent.of_comp (LinearMap.funLeft k k piV)
    convert tangentVec_independent k using 1
  have h := GermLower.le_pointLocalDimension k 197 (swapDec (qL k)) (swapDec_solves (qL_solves k))
    (swapDec (germFamily k params (pqk k) true))
    (swapDec_solves (FamilyParameters.value_solves _ _))
    (fun x => by
      rw [coordinates_swapDec, coordinates_swapDec]
      exact germFamily_residue k params (pqk k) true (piV x))
    _ hD
    (fun j x => by
      rw [coordinates_swapDec, Matrix.of_apply]
      exact germFamily_germJet k params (pqk k) (pqk_global k) (pqk_scale k) true j (piV x))
  exact_mod_cast h

/-- **(d)** The local ring of the Brent scheme at `q_R` has Krull dimension 197. -/
theorem local_dimension (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    ringKrullDim (PointLocalRing ((pqk k).value false) qR_solves) = 197 := by
  apply le_antisymm
  · have h := pointLocalDimension_le ((pqk k).value false) qR_solves
    rw [square_variable_count] at h
    have hr : Module.finrank k (Submodule.span k (Set.range fun x : Var =>
        fun e : EquationIndex SquareVertex =>
          ((pqk k).value false).jacobianColumn x e.1 e.2.1 e.2.2)) = 2155 :=
      jacobian_rank hdet
    rw [hr] at h
    exact h
  · have key : ∀ (q : Decomposition k SquareVertex SquareSummand) (hq : q.Solves),
        q = swapDec (qL k) → (197 : WithBot ℕ∞) ≤ ringKrullDim (PointLocalRing q hq) := by
      rintro q hq rfl
      exact le_local_dimension_swap
    exact key _ _ qR_eq

/-- **(e)** `Â_{q_R} ≃ k⟦z₁,…,z₁₉₇⟧`. -/
theorem ahat_equiv (hdet : (minorInt.map (Int.castRingHom k)).det ≠ 0) :
    Nonempty (AhatAt ((pqk k).value false) ≃ₐ[k] MvPowerSeries (Fin 197) k) := by
  rw [qR_eq]
  exact ⟨(swapAtEquiv k (qL k)).symm.trans (ahatEquiv hdet)⟩

end Brent.Formal.SmoothRightPoint
