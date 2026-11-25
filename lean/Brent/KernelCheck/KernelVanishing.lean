import Brent.KernelCheck.FamilyQuadratics
import Brent.QuadraticExpansion

/-!
# Same-chart polar terms vanish against every left-kernel covector

Let `μ` be any covector annihilating the Jacobian, over any commutative ring. For two frame
directions in a common exact chart, the two-parameter jet of the exact family shows that the
polar term is in the image of the Jacobian, so its contraction with `μ` vanishes. This extends
`archived_same_chart_zero` from the 54 certified covectors to the whole left kernel.
-/

open scoped BigOperators

namespace Brent.KernelVanishing

open TangentData QuadraticData

variable {R : Type} [CommRing R] (μ : EquationIndex SquareVertex → R)
  (hμ : ∀ x : Variable SquareVertex SquareSummand,
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).jacobianColumn x e.1 e.2.1 e.2.2 * μ e = 0)
include hμ

theorem differential_zero (v : Decomposition R SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).jacobianEntry v e.1 e.2.1 e.2.2 * μ e = 0 := by
  simp_rw [Decomposition.jacobianEntry_expand, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hμ, mul_zero]
  simp

theorem second_order_zero
    (d : Decomposition (DualNumber (DualNumber R)) SquareVertex SquareSummand)
    (solution : d.Solves) (atPoint : d.constantPart.constantPart = strassenSquare R) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).polarizedEntry
      d.tangentPart.constantPart d.constantPart.tangentPart e.1 e.2.1 e.2.2 * μ e = 0 := by
  have eq (e : EquationIndex SquareVertex) :
      (strassenSquare R).polarizedEntry d.tangentPart.constantPart
        d.constantPart.tangentPart e.1 e.2.1 e.2.2 =
      -((strassenSquare R).jacobianEntry d.tangentPart.tangentPart e.1 e.2.1 e.2.2) := by
    have h := d.mixed_entry_of_solution solution e.1 e.2.1 e.2.2
    rw [atPoint] at h
    exact eq_neg_of_add_eq_zero_right h
  simp_rw [eq, neg_mul, Finset.sum_neg_distrib, differential_zero μ hμ, neg_zero]

theorem family_polar_zero (left : Bool) (p q : FamilyParameters (DualNumber R))
    (hp : p.map (Jets.forget R) = FamilyParameters.one R)
    (hq : q.map (Jets.forget R) = FamilyParameters.one R) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).polarizedEntry
      (q.value left).tangentPart (p.value left).tangentPart e.1 e.2.1 e.2.2 * μ e = 0 := by
  let params := Jets.pairParameters R p q
  let d := params.value left
  have inner : d.constantPart = p.value left := by
    change d.map (Jets.innerSpecialization R) = p.value left
    dsimp only [d, params]
    rw [FamilyParameters.value_map, Jets.pair_specializes_inner R p q hq]
  have outer : d.tangentPart.constantPart = (q.value left).tangentPart := by
    change (d.map (Jets.outerSpecialization R)).tangentPart = (q.value left).tangentPart
    dsimp only [d, params]
    rw [FamilyParameters.value_map, Jets.pair_specializes_outer R p q hp]
  have base : d.constantPart.constantPart = strassenSquare R := by
    rw [inner]
    change (p.value left).map (Jets.forget R) = strassenSquare R
    rw [FamilyParameters.value_map, hp, FamilyParameters.value_one]
  have h := second_order_zero μ hμ d (FamilyParameters.value_solves left params) base
  rwa [inner, outer] at h

omit hμ in
theorem castOrigin_base_any (i : Fin 251) :
    (castOrigin R i).map (Jets.forget R) = FamilyParameters.one R := by
  have comp : (Jets.forget R).comp (Jets.map Int (Int.castRingHom R)) =
      (Int.castRingHom R).comp (Jets.forget Int) := rfl
  rw [castOrigin, FamilyParameters.map_comp, comp, ← FamilyParameters.map_comp,
    frameOrigin_base, FamilyParameters.map_one]

theorem same_chart_zero (i j : Fin 251) (left : Bool) (hi : InChart i left) (hj : InChart j left) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).polarizedEntry
      (frameDirection R i) (frameDirection R j) e.1 e.2.1 e.2.2 * μ e = 0 := by
  have h := family_polar_zero μ hμ left (castOrigin R j) (castOrigin R i)
    (castOrigin_base_any j) (castOrigin_base_any i)
  rwa [archived_origin R i left hi, archived_origin R j left hj] at h

/-- All polar terms outside the mixed block vanish against every left-kernel covector. -/
theorem nonmixed_zero (i j : Fin 251)
    (nonmixed : ¬ ((143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) ∨
                    (143 ≤ j.val ∧ j.val < 197 ∧ 197 ≤ i.val))) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).polarizedEntry
      (frameDirection R i) (frameDirection R j) e.1 e.2.1 e.2.2 * μ e = 0 := by
  by_cases h : i.val < 197 ∧ j.val < 197
  · exact same_chart_zero μ hμ i j true h.1 h.2
  · apply same_chart_zero μ hμ i j false <;> simp [InChart] <;> omega

/-- The square terms vanish when `2` is not a zero divisor. -/
theorem square_zero (h2 : ∀ r : R, 2 * r = 0 → r = 0) (i : Fin 251) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare R).bilinearEntry
      (frameDirection R i) (frameDirection R i) e.1 e.2.1 e.2.2 * μ e = 0 := by
  apply h2
  rw [Finset.mul_sum]
  have h := nonmixed_zero μ hμ i i (by omega)
  rw [← h]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Decomposition.polarizedEntry_eq_bilinear]
  ring

end Brent.KernelVanishing
