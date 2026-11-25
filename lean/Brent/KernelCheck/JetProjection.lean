import Brent.FamilyParameters
import Brent.KernelCheck.QuadraticCertificates

open scoped BigOperators

namespace Brent.Decomposition

variable {R α ι : Type*} [CommRing R] [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

theorem jacobianEntry_expand (p v : Decomposition R α ι) (a b c : α × α) :
    p.jacobianEntry v a b c = ∑ x : Variable α ι, v.coordinates x * p.jacobianColumn x a b c := by
  have modes (f : Mode → R) : ∑ m, f m = f .u + f .v + f .w := by
    change Finset.sum {Mode.u, Mode.v, Mode.w} f = _
    simp [add_assoc]
  rw [Fintype.sum_prod_type]
  have byMode (f : Mode × (α × α) → R) : (∑ t, f t) = ∑ m, ∑ a, f (m, a) :=
    Fintype.sum_prod_type f
  simp_rw [byMode, modes]
  simp [jacobianEntry, jacobianColumn_eq, coordinates, mul_ite, mul_assoc]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Brent.Decomposition

namespace Brent.QuadraticData

theorem projected_differential_zero (ell : Fin 54) (v : Decomposition K SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare K).jacobianEntry v e.1 e.2.1 e.2.2 *
      functionalEntry ell (squareEquationNumber e) = 0 := by
  simp_rw [Decomposition.jacobianEntry_expand, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, archived_covectors_annihilate, mul_zero]
  simp

/-- The contraction of a polar term from an exact two-parameter deformation vanishes. -/
theorem projected_second_order_zero (ell : Fin 54)
    (d : Decomposition (DualNumber (DualNumber K)) SquareVertex SquareSummand)
    (solution : d.Solves) (atPoint : d.constantPart.constantPart = strassenSquare K) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare K).polarizedEntry
      d.tangentPart.constantPart d.constantPart.tangentPart e.1 e.2.1 e.2.2 *
      functionalEntry ell (squareEquationNumber e) = 0 := by
  have eq (e : EquationIndex SquareVertex) :
      (strassenSquare K).polarizedEntry d.tangentPart.constantPart
        d.constantPart.tangentPart e.1 e.2.1 e.2.2 =
      -((strassenSquare K).jacobianEntry d.tangentPart.tangentPart e.1 e.2.1 e.2.2) := by
    have h := d.mixed_entry_of_solution solution e.1 e.2.1 e.2.2
    rw [atPoint] at h
    exact eq_neg_of_add_eq_zero_right h
  simp_rw [eq, neg_mul, Finset.sum_neg_distrib, projected_differential_zero, neg_zero]

/-- Mixed coefficients of two first-order directions in the same exact family
vanish after projection by any of the certified left-kernel covectors. -/
theorem same_family_polar_zero (ell : Fin 54) (left : Bool)
    (p q : FamilyParameters (DualNumber K))
    (hp : p.map (Jets.forget K) = FamilyParameters.one K)
    (hq : q.map (Jets.forget K) = FamilyParameters.one K) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare K).polarizedEntry
      (q.value left).tangentPart (p.value left).tangentPart e.1 e.2.1 e.2.2 *
      functionalEntry ell (squareEquationNumber e) = 0 := by
  let params := Jets.pairParameters K p q
  let d := params.value left
  have inner : d.constantPart = p.value left := by
    change d.map (Jets.innerSpecialization K) = p.value left
    dsimp only [d, params]
    rw [FamilyParameters.value_map, Jets.pair_specializes_inner K p q hq]
  have outer : d.tangentPart.constantPart = (q.value left).tangentPart := by
    change (d.map (Jets.outerSpecialization K)).tangentPart = (q.value left).tangentPart
    dsimp only [d, params]
    rw [FamilyParameters.value_map, Jets.pair_specializes_outer K p q hp]
  have base : d.constantPart.constantPart = strassenSquare K := by
    rw [inner]
    change (p.value left).map (Jets.forget K) = strassenSquare K
    rw [FamilyParameters.value_map, hp, FamilyParameters.value_one]
  have h := projected_second_order_zero ell d (FamilyParameters.value_solves left params) base
  rwa [inner, outer] at h

end Brent.QuadraticData
