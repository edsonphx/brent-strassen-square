import Brent.Generated.QuadraticData
import Brent.Generated.RankChecks
import Brent.SparseContraction

open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 400000

namespace Brent.QuadraticData

private def unpack (fuel packed : Nat) : SparseRow.Row :=
  match fuel with
  | 0 => []
  | n + 1 => if packed = 0 then [] else
    let word := packed % 65536
    let magnitude : Int := (word % 256) / 2
    (word / 256, if word % 2 = 0 then magnitude else -magnitude) ::
      unpack n (packed / 65536)

private def column (data : Array (Array Nat)) (i : Nat) : SparseRow.Row :=
  unpack 54 ((data[i / 48]!)[i % 48]!)

/-- The 54 archived covectors, stored by equation coordinate. -/
def coefficients (e : Nat) : SparseRow.Row := column functionalData e

def annihilatorQuotient (i : Fin 2101) : SparseRow.Row :=
  column annihilatorQuotientData i.val

abbrev K := ZMod 3

private def decodeF3 (r : SparseRow.Row) (e : Fin 4096) : K :=
  SparseRow.coefficient e.val r

private theorem eval_list_sum (l : List (Fin 4096 → K)) (e : Fin 4096) :
    l.sum e = (l.map fun f => f e).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

def functionalEntry (i : Fin 54) (e : Fin 4096) : K :=
  SparseRow.coefficient i.val (coefficients e.val)

noncomputable def functional (i : Fin 54) : (Fin 4096 → K) →ₗ[K] K where
  toFun f := ∑ e, f e * functionalEntry i e
  map_add' f g := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a f := by simp [mul_assoc, Finset.mul_sum]

def checkAnnihilatorPivot (i : Fin 2101) : Bool :=
  SparseRow.checkMod 54 16 3
    (SparseRow.contract coefficients (JacobianTrace.reduced (JacobianTrace.select i))) []
    (annihilatorQuotient i)

private theorem reduced_fits (i : Fin 2352) :
    ∀ a ∈ JacobianTrace.reduced i, a.1 < 4096 := by
  have h := JacobianTrace.checkedSteps i
  simp only [SparseRow.checkRadixStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

private theorem pivot_eval_zero (checks : ∀ j, checkAnnihilatorPivot j = true) (i : Fin 54)
    (j : Fin 2101) :
    functional i (decodeF3 (JacobianTrace.reduced (JacobianTrace.select j))) = 0 := by
  have h := SparseRow.checked_mod 54 16
    (SparseRow.contract coefficients (JacobianTrace.reduced (JacobianTrace.select j))) []
    (annihilatorQuotient j) (checks j) i
  rw [SparseRow.coefficient_contract_dense _ _ 4096 _ (reduced_fits _)] at h
  simpa [functional, functionalEntry, decodeF3, SparseRow.coefficient] using h

private theorem reduced_eval_zero (checks : ∀ j, checkAnnihilatorPivot j = true) (i : Fin 54)
    (j : Fin 2352) :
    functional i (decodeF3 (JacobianTrace.reduced j)) = 0 := by
  have h := JacobianTrace.coverage_of_auxiliary JacobianTrace.checkedAuxiliary j
  cases hj : JacobianTrace.cover j with
  | none =>
    simp [SparseRow.checkCover, hj] at h
    rw [h]
    simp [functional, decodeF3, SparseRow.coefficient]
  | some k =>
    simp [SparseRow.checkCover, hj] at h
    rw [← h]
    exact pivot_eval_zero checks i k

theorem original_eval_zero (checks : ∀ j, checkAnnihilatorPivot j = true) (i : Fin 54)
    (j : Fin 2352) :
    functional i (decodeF3 (JacobianTrace.original j)) = 0 := by
  have h := (SparseRow.checked_radix_step 4096 12 JacobianTrace.original JacobianTrace.reduced
    JacobianTrace.operations j (JacobianTrace.checkedSteps j)).2
  let vector (s : Fin 2352 × Int) : Fin 4096 → K :=
    (s.2 : K) • decodeF3 (JacobianTrace.reduced s.1)
  have eq : (decodeF3 (JacobianTrace.original j) : Fin 4096 → K) =
      decodeF3 (JacobianTrace.reduced j) +
      ((JacobianTrace.operations j).map vector).sum := by
    funext e
    have hj := congrArg (fun x : Int => (x : K)) (h e)
    simp only [Int.cast_sub, Int.cast_list_sum, List.map_map, Function.comp_def,
      Int.cast_mul] at hj
    simp only [Pi.add_apply, eval_list_sum, List.map_map, Function.comp_def, vector,
      Pi.smul_apply, smul_eq_mul, decodeF3]
    exact sub_eq_iff_eq_add.mp hj.symm
  rw [eq, map_add, map_list_sum, reduced_eval_zero checks i j, zero_add]
  simp only [List.map_map, Function.comp_def, vector, map_smul, reduced_eval_zero checks i,
    smul_zero, List.map_const', List.sum_replicate]

/-- The checked finite covectors annihilate the actual Jacobian modulo three. -/
theorem annihilates_jacobian (checks : ∀ j, checkAnnihilatorPivot j = true)
    (i : Fin 54) (x : Variable SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex,
      (strassenSquare K).jacobianColumn x e.1 e.2.1 e.2.2 *
        functionalEntry i (squareEquationNumber e) = 0 := by
  let f (e : Fin 4096) : K :=
    (SparseRow.coefficient e.val (squareJacobianColumn x) : K) * functionalEntry i e
  have h : ∑ e : Fin 4096, f e = 0 := by
    simpa only [f, functional, LinearMap.coe_mk, AddHom.coe_mk, decodeF3,
      JacobianTrace.original, Equiv.symm_apply_apply]
      using original_eval_zero checks i (squareVariableNumber x)
  have hsum : ∑ e : EquationIndex SquareVertex, f (squareEquationNumber e) = 0 :=
    (squareEquationNumber.sum_comp f).trans h
  refine Eq.trans (Finset.sum_congr rfl (fun e _ => ?_)) hsum
  dsimp only [f]
  rw [squareJacobianColumn_correct]
  obtain ⟨s, m, a⟩ := x
  obtain ⟨b, c, d⟩ := e
  cases m <;>
    simp only [Decomposition.jacobianColumn_eq, strassenSquare, Decomposition.map] <;>
      split_ifs <;> simp

end Brent.QuadraticData
