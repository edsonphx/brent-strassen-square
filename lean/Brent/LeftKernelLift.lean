import Brent.CM.LiftInstance
import Brent.Z3Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Brent.Generated.RankChecks

/-! The arbitrary left kernel, using the actual integer elimination trace.
No field-rank argument is used to invert a matrix over the localized integers:
the pivot submatrix is triangular with diagonal ±1 over every coefficient ring. -/
open scoped BigOperators
namespace Brent.LeftKernelLift

open Brent.JacobianTrace Brent.Z3 Brent.CM.LiftInstance

variable (R : Type*) [CommRing R]

abbrev E := Fin 4096
abbrev P := Fin 2101

def vec (r : SparseRow.Row) : E → R := fun e => (SparseRow.coefficient e.val r : R)
def orig (i : Fin 2352) := vec R (original i)
def red (i : Fin 2352) := vec R (reduced i)
def basisRow (i : P) := red R (select i)

/-- The functional defined by a row covector, acting on equation vectors. -/
def pair (l : E → R) : (E → R) →ₗ[R] R where
  toFun v := ∑ e, v e * l e
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a v := by simp [mul_assoc, Finset.mul_sum]

/-- The left kernel of the actual sparse Jacobian in Appendix A numbering. -/
def InLeft (l : E → R) : Prop := ∀ i, pair R l (orig R i) = 0

theorem span_trace :
    Submodule.span R (Set.range (orig R)) = Submodule.span R (Set.range (red R)) := by
  apply rowSpan_eq_of_elimination (steps := fun i =>
    (operations i).map fun (j,a) => (j,(a : R)))
  · intro i a ha
    obtain ⟨⟨j,c⟩, hj, rfl⟩ := List.mem_map.mp ha
    exact (SparseRow.checked_radix_step 4096 12 original reduced operations i (checkedSteps i)).1 _ hj
  · intro i
    have equal : SparseRow.decode (K := R) (fun e : E => e.val)
        (SparseRow.reduce reduced (original i) (operations i)) = red R i := by
      funext e
      simp only [SparseRow.decode, SparseRow.coefficient_reduce, red, vec,
        (SparseRow.checked_radix_step 4096 12 original reduced operations i (checkedSteps i)).2 e]
    have hh := SparseRow.decode_reduce (K := R) (fun e : E => e.val)
      reduced (original i) (operations i)
    rw [equal] at hh
    simpa [red, orig, vec, SparseRow.decode, List.map_map, Function.comp_def] using hh

theorem span_selected :
    Submodule.span R (Set.range (red R)) = Submodule.span R (Set.range (basisRow R)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h := coverage_of_auxiliary checkedAuxiliary i
    cases hi : cover i with
    | none =>
      have hr : reduced i = [] := by simpa [SparseRow.checkCover, hi] using h
      have hz : red R i = 0 := by
        funext e
        simp [red, vec, hr, SparseRow.coefficient]
      rw [hz]
      exact Submodule.zero_mem _
    | some j =>
      have hr : select j = i := by simpa [SparseRow.checkCover, hi] using h
      exact Submodule.subset_span ⟨j, by simp [basisRow, hr]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨select i, rfl⟩

theorem inLeft_iff_selected (l : E → R) :
    InLeft R l ↔ ∀ i, pair R l (basisRow R i) = 0 := by
  have h₁ : InLeft R l ↔ Submodule.span R (Set.range (orig R)) ≤ LinearMap.ker (pair R l) := by
    rw [Submodule.span_le]
    simp [InLeft, Set.range_subset_iff, LinearMap.mem_ker]
  have h₂ : (∀ i, pair R l (basisRow R i) = 0) ↔
      Submodule.span R (Set.range (basisRow R)) ≤ LinearMap.ker (pair R l) := by
    rw [Submodule.span_le]
    simp [Set.range_subset_iff, LinearMap.mem_ker]
  rw [h₁, span_trace, span_selected, ← h₂]

/-- A matrix with unit determinant, not merely nonzero determinant. -/
def D : Matrix P P R := fun i j => basisRow R i (pivot j)

theorem D_unit : IsUnit (D R).det := by
  have hp := pivots_of_auxiliary checkedAuxiliary
  have ht : (D R).BlockTriangular id := by
    intro i j hij
    have h := hp i
    simp only [SparseRow.checkPivot, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    have hz := SparseRow.coeff_zero_below _ _ _ (increasing_of_auxiliary checkedAuxiliary hij) h.2
    simp [D, basisRow, red, vec, hz]
  rw [Matrix.det_of_upperTriangular ht]
  refine IsUnit.prod_univ_iff.mpr fun i => ?_
  have h := hp i
  simp only [SparseRow.checkPivot, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h.1 with h | h <;> simp [D, basisRow, red, vec, h]

/-- Insert correction coefficients only on the chosen pivot coordinates. -/
def insertPivot (c : P → R) (e : E) : R := ∑ j : P, if pivot j = e then c j else 0

theorem pair_insertPivot (l : E → R) (c : P → R) (i : P) :
    pair R (fun e => l e + insertPivot R c e) (basisRow R i) =
      pair R l (basisRow R i) + (D R *ᵥ c) i := by
  classical
  change (∑ e, basisRow R i e * (l e + ∑ j : P, if pivot j = e then c j else 0)) =
    (∑ e, basisRow R i e * l e) + (D R *ᵥ c) i
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, D, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Projection to the left kernel, using only the unit pivot determinant. -/
noncomputable def project (l : E → R) : E → R :=
  fun e => l e + insertPivot R ((D R)⁻¹ *ᵥ fun i => -pair R l (basisRow R i)) e

theorem project_inLeft (l : E → R) : InLeft R (project R l) := by
  rw [inLeft_iff_selected]
  intro i
  change pair R (fun e => l e + insertPivot R
    ((D R)⁻¹ *ᵥ fun i => -pair R l (basisRow R i)) e) (basisRow R i) = 0
  rw [pair_insertPivot, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (D_unit R),
    Matrix.one_mulVec]
  exact add_neg_cancel _

theorem project_eq_self (l : E → R) (h : InLeft R l) : project R l = l := by
  funext e
  have hz : (fun i => -pair R l (basisRow R i)) = 0 := by
    funext i
    simp [(inLeft_iff_selected R l).mp h i]
  simp [project, hz, insertPivot]

/-- The left kernel is precisely the fixed set of this explicit projection. -/
theorem project_idempotent (l : E → R) : project R (project R l) = project R l :=
  project_eq_self R _ (project_inLeft R l)

/-- Arbitrary modular left-kernel rows lift, not just the 54 archived rows. -/
theorem leftKernel_lift_mod3 (l : E → ZMod 3) (h : InLeft (ZMod 3) l) :
    ∃ L : E → R0, InLeft R0 L ∧ ∀ e, rho3 (L e) = l e := by
  classical
  choose L hL using fun e => rho3_surjective (l e)
  refine ⟨project R0 L, project_inLeft R0 L, fun e => ?_⟩
  have hzero (i : P) : rho3 (pair R0 L (basisRow R0 i)) = 0 := by
    have hh := (inLeft_iff_selected (ZMod 3) l).mp h i
    change rho3 (∑ e, basisRow R0 i e * L e) = 0
    simpa only [map_sum, map_mul, basisRow, red, vec, map_intCast, hL] using hh
  simp only [project, map_add, hL, insertPivot, map_sum, apply_ite rho3, map_zero,
    Matrix.mulVec, dotProduct, map_mul, map_neg, hzero, neg_zero, mul_zero, Finset.sum_const_zero,
    ite_self, add_zero]

/-- Match the packed covector condition with the actual Brent Jacobian. -/
theorem inLeft_iff_jacobian (l : E → R) : InLeft R l ↔
    ∀ x : Variable SquareVertex SquareSummand,
      ∑ e : EquationIndex SquareVertex,
        (strassenSquare R).jacobianColumn x e.1 e.2.1 e.2.2 * l (squareEquationNumber e) = 0 := by
  have eq (x : Variable SquareVertex SquareSummand) :
      pair R l (orig R (squareVariableNumber x)) =
        ∑ e : EquationIndex SquareVertex,
          (strassenSquare R).jacobianColumn x e.1 e.2.1 e.2.2 * l (squareEquationNumber e) := by
    change (∑ e : E, orig R (squareVariableNumber x) e * l e) = _
    rw [← squareEquationNumber.sum_comp (fun e => orig R (squareVariableNumber x) e * l e)]
    apply Finset.sum_congr rfl
    intro e _
    simp only [orig, original, Equiv.symm_apply_apply, vec, squareJacobianColumn_correct]
    rw [strassenSquare, Decomposition.jacobianColumn_map, eq_intCast]
  constructor
  · intro h x
    rw [← eq x]
    exact h _
  · intro h i
    simpa only [Equiv.apply_symm_apply, eq] using h (squareVariableNumber.symm i)

theorem actual_leftKernel_lift_mod3 (l : E → ZMod 3)
    (h : ∀ x : Variable SquareVertex SquareSummand,
      ∑ e : EquationIndex SquareVertex,
        (strassenSquare (ZMod 3)).jacobianColumn x e.1 e.2.1 e.2.2 * l (squareEquationNumber e) = 0) :
    ∃ L : E → R0, (∀ x : Variable SquareVertex SquareSummand,
      ∑ e : EquationIndex SquareVertex,
        (strassenSquare R0).jacobianColumn x e.1 e.2.1 e.2.2 * L (squareEquationNumber e) = 0) ∧
      ∀ e, rho3 (L e) = l e := by
  obtain ⟨L, hL, hr⟩ := leftKernel_lift_mod3 l ((inLeft_iff_jacobian _ l).mpr h)
  exact ⟨L, (inLeft_iff_jacobian _ L).mp hL, hr⟩

end Brent.LeftKernelLift
