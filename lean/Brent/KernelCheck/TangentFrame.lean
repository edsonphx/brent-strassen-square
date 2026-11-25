import Brent.Generated.TangentChecks
import Brent.FrameBlocks
import Brent.Generated.FrameBlockChecks
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

open scoped BigOperators

namespace Brent.TangentData

private theorem checkedRank (i : Fin 251) : checkFrameRank i = true := by
  have h := checkedFrame i
  simp only [checkFrame, Bool.and_eq_true] at h
  exact h.1

private theorem checkedTangent (i : Fin 251) : checkTangent i = true := by
  have h := checkedFrame i
  simp only [checkFrame, Bool.and_eq_true] at h
  exact h.2

/-- The 251 archived vectors have the full rank of the linearized kernel. -/
theorem archived_frame_rank (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k
      (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i)))) = 251 :=
  frame_rank_of_checks checkedRank k

/-- All 251 archived directions annihilate the signed integer Brent Jacobian. -/
theorem archived_frame_tangent (i : Fin 251) (e : EquationIndex SquareVertex) :
    ∑ j : Fin 2352, SparseRow.coefficient j.val (frame i) *
      strassenSquareInt.jacobianColumn (squareVariableNumber.symm j) e.1 e.2.1 e.2.2 = 0 :=
  frame_tangent_of_checks checkedRank checkedTangent i e

private theorem archived_frame_independent (k : Type*) [Field k] :
    LinearIndependent k (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i)) :=
  linearIndependent_iff_card_eq_finrank_span.mpr (by
    change Fintype.card (Fin 251) = Module.finrank k (Submodule.span k
      (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i))))
    rw [archived_frame_rank, Fintype.card_fin])

private def commonFrameIndex (i : Fin 143) : Fin 251 := ⟨i.val, by have := i.isLt; omega⟩

/-- The three parts of the frozen frame have ranks 143, 54, and 54. -/
theorem archived_frame_split (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k
        (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame (commonFrameIndex i))))) = 143 ∧
    Module.finrank k (Submodule.span k
        (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame (xFrameIndex i))))) = 54 ∧
    Module.finrank k (Submodule.span k
        (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame (yFrameIndex i))))) = 54 := by
  have independent := archived_frame_independent k
  have common_inj : Function.Injective commonFrameIndex := by
    intro i j eq
    exact Fin.ext (congrArg (fun x : Fin 251 => x.val) eq)
  have left_inj : Function.Injective xFrameIndex := by
    intro i j eq
    apply Fin.ext
    have h := congrArg (fun x : Fin 251 => x.val) eq
    change 143 + i.val = 143 + j.val at h
    omega
  have right_inj : Function.Injective yFrameIndex := by
    intro i j eq
    apply Fin.ext
    have h := congrArg (fun x : Fin 251 => x.val) eq
    change 197 + i.val = 197 + j.val at h
    omega
  exact ⟨(finrank_span_eq_card (independent.comp _ common_inj)).trans (Fintype.card_fin _),
    (finrank_span_eq_card (independent.comp _ left_inj)).trans (Fintype.card_fin _),
    (finrank_span_eq_card (independent.comp _ right_inj)).trans (Fintype.card_fin _)⟩

theorem archived_left_coordinates (i : Fin 54) (x : Variable SquareVertex SquareSummand) :
    SparseRow.coefficient (squareVariableNumber x).val (frame (xFrameIndex i)) =
      (QuadraticData.xDirection i).coordinates x :=
  xFrame_coordinates_of_check i (checkedBlock i) x

theorem archived_right_coordinates (i : Fin 54) (x : Variable SquareVertex SquareSummand) :
    SparseRow.coefficient (squareVariableNumber x).val (frame (yFrameIndex i)) =
      (QuadraticData.yDirection i).coordinates x :=
  yFrame_coordinates_of_check i (checkedBlock i) x

end Brent.TangentData
