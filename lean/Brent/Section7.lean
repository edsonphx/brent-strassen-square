import Brent.Formal.SmoothPoints
import Brent.Formal.Component
import Brent.Census.Exclusion
import Brent.Census.FieldTransfer
import Brent.LWH

/-!
# Task 5 (F20): one theorem per claim of §7 (Relation to the AlphaTensor schemes)

DRAFT, NOT YET COMPILED. Each theorem quotes its sentence of `paper.tex` and restates the
proved result under a name that `Audit.lean` lists. Fields: every field of characteristic three
or zero; the component statements also need `[Infinite k]` (true for algebraically closed `k`,
the paper's setting, lines 610–619).

Not yet included (waiting for Task B): the census counts 14,149 / 87 / {2445, 5969} and
"14,147 points pass both tests" (lines 696–705).
-/

namespace Brent.Section7

open Brent Brent.Formal Brent.Formal.FamilyClosure

variable (k : Type) [Field k]

/-- Lines 610–613: "The closure of either family image has dimension 197." -/
theorem closure_dimension [Infinite k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    ringKrullDim (MvPolynomial Var k ⧸ RingHom.ker (psi k left)) = 197 :=
  Component.ringKrullDim_closure k left hk

/-- Lines 613–619: the closure is irreducible, contains `p`, and is an irreducible component
of the Brent variety ("Each closure is therefore a component"). -/
theorem closure_component [Infinite k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    pointP k ∈ familyClosure k left ∧ IsIrreducible (familyClosure k left) ∧
      familyClosure k left ⊆ brentVariety k ∧
      ∀ Z : Set (Affine k), IsClosed Z → IsIrreducible Z → familyClosure k left ⊆ Z →
        Z ⊆ brentVariety k → Z = familyClosure k left :=
  Component.familyClosure_isComponent k left hk

/-- Lines 621–642: the one-parameter curves pass through `p` at `t = 0`, reach integer
solutions at `t = 1`, and these points are smooth: Jacobian rank 2155, tangent and local
dimension 197, regular local ring, completion `k⟦z₁,…,z₁₉₇⟧`. -/
theorem smooth_points (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    type_of% (SmoothPoints.smooth_points (k := k) hk left) :=
  SmoothPoints.smooth_points (k := k) hk left

/-- Lines 652–653: "Li, Wang and Hu's selected AlphaTensor point has tangent dimension 197
and orbit tangent dimension 143." -/
theorem lwh_point (hk : CharP k 3 ∨ CharZero k) : type_of% (LWH.lwh_point k hk) :=
  LWH.lwh_point k hk

/-- Lines 659–660, 698–699: the rank bounds rule out membership of 87 catalogue entries in
both family closures. -/
theorem rank_bound_exclusion (hk : CharP k 3 ∨ CharZero k) {n : ℕ} {b : Census.BoundW}
    (h : (n, b) ∈ Census.boundWitnesses) (v : Affine k) (hv : b.Agrees v) (left : Bool) :
    v ∉ familyClosure k left :=
  Census.not_mem_familyClosure hk h v hv left

/-- Lines 696–702: 87 + 2 = 89 distinct excluded catalogue indices. -/
theorem excluded_count : type_of% Census.excluded_card := Census.excluded_card

end Brent.Section7
