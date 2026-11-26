import Brent.Formal.SmoothPoints
import Brent.Formal.SwapSymmetry
import Brent.Formal.Component
import Brent.Census.Equivalences
import Brent.Census.FamilyProfile
import Brent.LWH

/-!
# §7 (Relation to the AlphaTensor schemes): one theorem per claim

DRAFT, NOT YET COMPILED.

Each theorem quotes its sentence of `paper.tex` and restates the proved result under a name that
`Audit.lean` lists. Fields: every field of characteristic three or zero. The paper's component
statements are made "over an algebraically closed field … after passing to the algebraic
closure in either characteristic" (lines 611–619): they are proved for every infinite field
(`closure_*`) and stated for algebraically closed fields as corollaries (`closure_*_algClosed`).
-/

namespace Brent.Section7

open Brent Brent.Formal Brent.Formal.FamilyClosure Brent.Census Brent.Catalogue

variable (k : Type) [Field k]

/-! ### Lines 608–619: the family closures are components of dimension 197 -/

/-- Lines 610–613: "The closure of either family image has dimension 197." -/
theorem closure_dimension [Infinite k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    ringKrullDim (MvPolynomial Var k ⧸ RingHom.ker (psi k left)) = 197 :=
  Component.ringKrullDim_closure k left hk

/-- Lines 613–619: the closure is irreducible, contains `p`, lies in `V`, and is an irreducible
component of `V` ("Each closure is therefore a component"). -/
theorem closure_component [Infinite k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    pointP k ∈ familyClosure k left ∧ IsIrreducible (familyClosure k left) ∧
      familyClosure k left ⊆ brentVariety k ∧
      ∀ Z : Set (Affine k), IsClosed Z → IsIrreducible Z → familyClosure k left ⊆ Z →
        Z ⊆ brentVariety k → Z = familyClosure k left :=
  Component.familyClosure_isComponent k left hk

/-- The vanishing ideal of the closure is a minimal prime of the Brent ideal. -/
theorem closure_minimalPrime [Infinite k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    RingHom.ker (psi k left) ∈ (brentIdeal k SquareVertex SquareSummand).minimalPrimes :=
  Component.ker_mem_minimalPrimes k left hk

theorem closure_dimension_algClosed [IsAlgClosed k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    ringKrullDim (MvPolynomial Var k ⧸ RingHom.ker (psi k left)) = 197 :=
  closure_dimension k hk left

theorem closure_component_algClosed [IsAlgClosed k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    pointP k ∈ familyClosure k left ∧ IsIrreducible (familyClosure k left) ∧
      familyClosure k left ⊆ brentVariety k ∧
      ∀ Z : Set (Affine k), IsClosed Z → IsIrreducible Z → familyClosure k left ⊆ Z →
        Z ⊆ brentVariety k → Z = familyClosure k left :=
  closure_component k hk left

/-! ### Lines 621–642: curves to smooth points -/

/-- Lines 629–631: "All four nonconstant matrices have determinant one and their inverses are
obtained by replacing `t` by `−t`." -/
theorem curve_matrices (t : k) :
    (e12 t).det = 1 ∧ (e21 t).det = 1 ∧ e12 t * e12 (-t) = 1 ∧ e21 t * e21 (-t) = 1 :=
  ⟨det_e12 t, det_e21 t, e12_mul_neg t, e21_mul_neg t⟩

/-- Lines 631–642: at `t = 0` the curves pass through `p`; at `t = 1` the integer Brent identity
holds, the Jacobian has rank 2155, the tangent and local dimensions are 197, the local ring is
regular and the completion is a power series ring in 197 variables. -/
theorem smooth_points (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    type_of% (SmoothPoints.smooth_points (k := k) hk left) :=
  SmoothPoints.smooth_points (k := k) hk left

/-! ### Lines 643–651: the swap symmetry -/

/-- Lines 646–649: the swap fixes `p` and exchanges the displayed families. -/
theorem swap_symmetry (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) :
    swapDec (strassenSquare k) = strassenSquare k ∧
      swapDec (leftFamily P Q T) = rightFamily P Q T :=
  ⟨swapDec_strassenSquare, swapDec_leftFamily P Q T⟩

/-! ### Lines 652–653: the Li–Wang–Hu point -/

/-- Lines 652–653: "Li, Wang and Hu's selected AlphaTensor point has tangent dimension 197 and
orbit tangent dimension 143." -/
theorem lwh_point (hk : CharP k 3 ∨ CharZero k) : type_of% (LWH.lwh_point k hk) :=
  LWH.lwh_point k hk

/-! ### Lines 659–705: exclusions using factor ranks and subspaces -/

/-- Lines 661–663: "Throughout either displayed family, the multiset of triples of ordinary
matrix ranks is 36(1,1,1), 12(2,2,2), 1(4,4,4)." Every field. -/
theorem family_rank_profile (pq : FamilyParameters k) (left : Bool) :
    rankProfile (pq.value left).coordinates = fullProfile :=
  family_profile pq left

/-- Lines 669–674: on the closure of the saturated families (closed under all equivalences) at
most 13 summands have a mode of rank above one and at most one summand has a mode of rank above
two (`RankBound k`). -/
theorem rank_bounds_closed :
    IsClosed (RankBound k) ∧
      closure (saturation (imageA k true) ∪ saturation (imageA k false)) ⊆ RankBound k :=
  ⟨isClosed_rankBound, closure_saturation_subset_rankBound⟩

/-- Lines 676–688: the anchor stacking conditions and the rank budgets hold on each family
closure. -/
theorem anchor_structure_closed (left : Bool) (t : SquareSummand) (ht : InGroup left t) :
    familyClosure k left ⊆ {v : Affine k | StackOK v t (anchor left t)} ∧
      familyClosure k left ⊆ {v : Affine k | BudgetOK v} :=
  ⟨closure_stackOK left t ht, closure_budgetOK left⟩

/-- Lines 696–699 and 704–705: the census over every field of characteristic three or zero. -/
theorem census (hk : CharP k 3 ∨ CharZero k) :
    (Finset.univ.filter fun p => profile k p = fullProfile).card = 14149 ∧
    (∀ p, profile k p = fullProfile ↔ RankBounds k p) ∧
    (open Classical in (Finset.univ.filter fun p => ¬ RankBounds k p).card = 87) ∧
    (open Classical in (Finset.univ.filter fun p => profile k p = fullProfile ∧ ¬ AnchorTest k p)
      = {2445, 5969}) ∧
    (open Classical in (Finset.univ.filter fun p => RankBounds k p ∧ AnchorTest k p).card = 14147) :=
  ⟨AllFields.card_fullProfile k hk, AllFields.fullProfile_iff_rankBounds k hk,
    AllFields.card_not_rankBounds k hk, AllFields.anchor_excluded k hk,
    AllFields.card_pass_both k hk⟩

/-- Lines 659–660, 698–699: the 87 entries failing the rank bounds lie outside the closure of the
saturated families, hence outside both family closures. -/
theorem rank_bound_exclusion (hk : CharP k 3 ∨ CharZero k) (p : Fin 14236)
    (hp : ¬ RankBounds k p) :
    catPoint k p ∉ closure (saturation (imageA k true) ∪ saturation (imageA k false)) ∧
      ∀ left, catPoint k p ∉ familyClosure k left :=
  ⟨catPoint_not_mem_saturated p hp, catPoint_not_mem_familyClosure_of_rankBounds p hp⟩

/-- Lines 700–704: 2445 and 5969 lie outside both family closures and outside the closure of the
families closed under all equivalences. -/
theorem anchor_exclusion (hk : CharP k 3 ∨ CharZero k) (p : Fin 14236)
    (hp : p = 2445 ∨ p = 5969) :
    catPoint k p ∉ closure (eqClosed k) ∧ ∀ left, catPoint k p ∉ familyClosure k left :=
  ⟨anchor_excluded_eqClosed hk p hp, fun left =>
    catalogue_excluded hk p (Or.inr hp) left⟩

/-- Lines 696–702: 89 catalogue entries are excluded in total. -/
theorem excluded_count (hk : CharP k 3 ∨ CharZero k) :
    (Finset.univ.filter fun p : Fin 14236 => ¬ RankBounds k p ∨ p = 2445 ∨ p = 5969).card = 89 :=
  card_excluded hk

end Brent.Section7
