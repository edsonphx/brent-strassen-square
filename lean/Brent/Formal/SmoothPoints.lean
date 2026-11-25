import Brent.Generated.SmoothLChecks
import Brent.Formal.SmoothRightPoint
import Brent.Formal.SmoothCurves
import Brent.PointRegular

/-!
# §7: smooth points of the two family closures (lines 621–642)

The one-parameter curves `curve t` pass through the recursive point `p` at `t = 0`
(`curve_value_zero`) and through `q_L`, `q_R` at `t = 1` (`curve_one`). Over every field of
characteristic three or zero, at both points:

* (a) the Brent identity holds (already over `ℤ`);
* (b) the Jacobian has rank exactly 2155;
* (c) the tangent space has dimension `2352 − 2155 = 197`;
* (d) the local ring of the Brent scheme has Krull dimension 197;
* (e) the local ring is regular (embedding dimension equals local dimension), and the formal
  neighbourhood is `k⟦z₁,…,z₁₉₇⟧`.
-/

open MvPowerSeries

namespace Brent.Formal.SmoothPoints

open Brent Brent.Formal Brent.SmoothL Brent.Formal.SmoothLeftPoint

variable {k : Type} [Field k]

/-- The kernel-checked 2155 × 2155 minor is invertible in characteristic three and zero. -/
theorem minor_det_ne_zero (hK : CharP k 3 ∨ CharZero k) :
    (minorInt.map (Int.castRingHom k)).det ≠ 0 :=
  SmoothL.det_minor_ne_zero checked k hK

/-- (a) The integer Brent identity at `t = 1`, in both orientations. -/
theorem integer_solves (left : Bool) : (pqInt.value left).Solves :=
  FamilyParameters.value_solves _ _

/-- The curves reach `q_L` and `q_R` at `t = 1`. -/
theorem curve_one_value (left : Bool) : (curve (1 : k)).value left = (pqk k).value left := by
  rw [curve_one]

theorem qL_jacobian_rank (hK : CharP k 3 ∨ CharZero k) :
    Module.finrank k (jacobianSpan k (qL k)) = 2155 :=
  SmoothLeftPoint.jacobian_rank (minor_det_ne_zero hK)

theorem qR_jacobian_rank (hK : CharP k 3 ∨ CharZero k) :
    Module.finrank k (jacobianSpan k ((pqk k).value false)) = 2155 :=
  SmoothRightPoint.jacobian_rank (minor_det_ne_zero hK)

theorem qL_tangent_dimension (hK : CharP k 3 ∨ CharZero k) :
    Module.finrank k (LinearMap.ker (differentialAt k (qL k))) = 197 :=
  SmoothLeftPoint.tangent_dimension (minor_det_ne_zero hK)

theorem qR_tangent_dimension (hK : CharP k 3 ∨ CharZero k) :
    Module.finrank k (LinearMap.ker (differentialAt k ((pqk k).value false))) = 197 :=
  SmoothRightPoint.tangent_dimension (minor_det_ne_zero hK)

theorem qL_local_dimension (hK : CharP k 3 ∨ CharZero k) :
    ringKrullDim (PointLocalRing (qL k) (qL_solves k)) = 197 :=
  SmoothLeftPoint.local_dimension (minor_det_ne_zero hK)

theorem qR_local_dimension (hK : CharP k 3 ∨ CharZero k) :
    ringKrullDim (PointLocalRing ((pqk k).value false) SmoothRightPoint.qR_solves) = 197 :=
  SmoothRightPoint.local_dimension (minor_det_ne_zero hK)

/-- (e) Smoothness: the local ring at `q_L` is regular. -/
theorem qL_regular (hK : CharP k 3 ∨ CharZero k) :
    IsRegularLocalRing (PointLocalRing (qL k) (qL_solves k)) := by
  apply isRegularLocalRing_of_dim
  rw [qL_local_dimension hK, square_variable_count]
  have h := qL_jacobian_rank hK
  rw [jacobianSpan] at h
  rw [h]
  rfl

/-- (e) Smoothness: the local ring at `q_R` is regular. -/
theorem qR_regular (hK : CharP k 3 ∨ CharZero k) :
    IsRegularLocalRing (PointLocalRing ((pqk k).value false) SmoothRightPoint.qR_solves) := by
  apply isRegularLocalRing_of_dim
  rw [qR_local_dimension hK, square_variable_count]
  have h := qR_jacobian_rank hK
  rw [jacobianSpan] at h
  rw [h]
  rfl

theorem qL_formal (hK : CharP k 3 ∨ CharZero k) :
    Nonempty (AhatAt (qL k) ≃ₐ[k] MvPowerSeries (Fin 197) k) :=
  ⟨ahatEquiv (minor_det_ne_zero hK)⟩

theorem qR_formal (hK : CharP k 3 ∨ CharZero k) :
    Nonempty (AhatAt ((pqk k).value false) ≃ₐ[k] MvPowerSeries (Fin 197) k) :=
  SmoothRightPoint.ahat_equiv (minor_det_ne_zero hK)

/-- **§7 smooth points, all clauses.** For both orientations `left`, the curve at `t = 0` is
the recursive point and at `t = 1` is `q = pqInt.value left`, which solves the integer Brent
identity; over every field of characteristic three or zero the Jacobian at `q` has rank 2155,
the tangent space has dimension 197, the local ring has dimension 197 and is regular, and
`Â_q ≃ k⟦z₁,…,z₁₉₇⟧`. The block matrices have determinant one with inverse `t ↦ −t`. -/
theorem smooth_points (hK : CharP k 3 ∨ CharZero k) (left : Bool) :
    (curve (0 : k)).value left = strassenSquare k ∧
    (curve (1 : k)).value left = (pqInt.value left).map (Int.castRingHom k) ∧
    (pqInt.value left).Solves ∧
    Module.finrank k (jacobianSpan k ((pqk k).value left)) = 2155 ∧
    Module.finrank k (LinearMap.ker (differentialAt k ((pqk k).value left))) = 197 ∧
    ringKrullDim (PointLocalRing ((pqk k).value left) (FamilyParameters.value_solves _ _)) = 197 ∧
    IsRegularLocalRing (PointLocalRing ((pqk k).value left) (FamilyParameters.value_solves _ _)) ∧
    Nonempty (AhatAt ((pqk k).value left) ≃ₐ[k] MvPowerSeries (Fin 197) k) ∧
    (∀ t : k, (e12 t).det = 1 ∧ (e21 t).det = 1 ∧ e12 t * e12 (-t) = 1 ∧ e21 t * e21 (-t) = 1) := by
  have hcurve : ∀ t : k, (e12 t).det = 1 ∧ (e21 t).det = 1 ∧ e12 t * e12 (-t) = 1 ∧
      e21 t * e21 (-t) = 1 := fun t => ⟨det_e12 t, det_e21 t, e12_mul_neg t, e21_mul_neg t⟩
  have hv : (curve (1 : k)).value left = (pqInt.value left).map (Int.castRingHom k) := by
    rw [curve_one, FamilyParameters.value_map]
  cases left
  · exact ⟨curve_value_zero false, hv, integer_solves false, qR_jacobian_rank hK,
      qR_tangent_dimension hK, qR_local_dimension hK, qR_regular hK, qR_formal hK, hcurve⟩
  · exact ⟨curve_value_zero true, hv, integer_solves true, qL_jacobian_rank hK,
      qL_tangent_dimension hK, qL_local_dimension hK, qL_regular hK, qL_formal hK, hcurve⟩

end Brent.Formal.SmoothPoints
