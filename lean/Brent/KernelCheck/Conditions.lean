import Brent.JacobianTrace
import Brent.RadixReplay
import Mathlib.Order.Fin.Basic

namespace Brent.JacobianTrace

/-- Check coverage, unit pivots, and successive pivot order in the same batches as the row identities. -/
def checkAuxiliary (i : Fin 2352) : Bool :=
  SparseRow.checkCover reduced select cover i &&
    if h : i.val < 2101 then
      let j : Fin 2101 := ⟨i.val, h⟩
      SparseRow.checkPivot (reduced (select j)) (pivot j).val &&
        if h' : i.val + 1 < 2101 then decide ((pivot j).val < (pivot ⟨i.val + 1, h'⟩).val)
        else true
    else true

theorem coverage_of_auxiliary (h : ∀ i, checkAuxiliary i = true) :
    ∀ i, SparseRow.checkCover reduced select cover i = true := by
  intro i
  have v := h i
  simp only [checkAuxiliary, Bool.and_eq_true] at v
  exact v.1

theorem pivots_of_auxiliary (h : ∀ i, checkAuxiliary i = true) :
    ∀ j, SparseRow.checkPivot (reduced (select j)) (pivot j).val = true := by
  intro j
  have v := h ⟨j.val, by have := j.isLt; omega⟩
  simp only [checkAuxiliary, dif_pos j.isLt, Bool.and_eq_true] at v
  exact v.2.1

theorem increasing_of_auxiliary (h : ∀ i, checkAuxiliary i = true) :
    StrictMono (Fin.val ∘ pivot) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro (j : Fin 2100)
  have hj := j.isLt
  have h1 : j.val < 2101 := by omega
  have h2 : j.val + 1 < 2101 := by omega
  have v := h ⟨j.val, by omega⟩
  simp only [checkAuxiliary, dif_pos h1, dif_pos h2, Bool.and_eq_true,
    decide_eq_true_eq] at v
  exact v.2.2

theorem rank_of_kernel_checks
    (step : ∀ i, SparseRow.checkRadixStep 4096 12 original reduced operations i = true)
    (aux : ∀ i, checkAuxiliary i = true)
    (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k (Set.range (fun x : Variable SquareVertex SquareSummand =>
      fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) = 2101 :=
  square_jacobian_rank_of_trace k 2101
    (SparseRow.rank_of_checked_radix_trace 12 squareEquationNumber original reduced operations select
      (squareEquationNumber.symm ∘ pivot) cover
      (by simpa [Function.comp_def] using increasing_of_auxiliary aux)
      step (by simpa [Function.comp_def] using pivots_of_auxiliary aux) (coverage_of_auxiliary aux))

end Brent.JacobianTrace
