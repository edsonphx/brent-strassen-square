import Brent.RankReplay
import Brent.SquareJacobian
import Brent.Generated.JacobianData
import Mathlib.Order.Fin.Basic

/-!
This optional module computes the complete trace using Lean's compiler.
The rank implication in Brent.RankReplay is kernel-verified separately.
Audit the extra computational axioms in RankAudit.lean.
-/
namespace Brent
namespace JacobianTrace

private def pick {α : Type*} [Inhabited α] (data : Array (Array α)) (i : Nat) : α :=
  (data[i / 48]!)[i % 48]!

-- Each 16-bit word contains the coordinate followed by a signed 3-bit value.
-- The certificate checker uses the decoded rows, independent of this encoding.
private def unpack (fuel : Nat) (packed : Nat) : SparseRow.Row :=
  match fuel with
  | 0 => []
  | n + 1 => if packed = 0 then [] else
    let word := packed % 65536
    let magnitude : Int := (word % 8) / 2
    (word / 8, if word % 2 = 0 then magnitude else -magnitude) ::
      unpack n (packed / 65536)

private def original (i : Fin 2352) := squareJacobianColumn (squareVariableNumber.symm i)
private def reduced (i : Fin 2352) := unpack 256 (pick reducedData i.val)
private def operations (i : Fin 2352) : List (Fin 2352 × Int) :=
  (unpack 256 (pick operationsData i.val)).map fun (j, x) => (Fin.ofNat 2352 j, x)
private def select (i : Fin 2101) := pick selectData i.val
private def pivot (i : Fin 2101) := pick pivotData i.val
private def cover (i : Fin 2352) := pick coverData i.val

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem steps_checked : ∀ i, SparseRow.checkStep original reduced operations i = true := by
  native_decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pivots_checked :
    ∀ i, SparseRow.checkPivot (reduced (select i)) (pivot i).val = true := by
  native_decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pivot_increasing : StrictMono (Fin.val ∘ pivot) := by
  rw [Fin.strictMono_iff_lt_succ]
  native_decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem coverage_checked :
    ∀ i, SparseRow.checkCover reduced select cover i = true := by
  native_decide

theorem rank_decoded (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k (Set.range (fun i =>
      SparseRow.decode (K := k) (fun e : EquationIndex SquareVertex =>
        (squareEquationNumber e).val) (original i)))) = 2101 :=
  SparseRow.rank_of_checked_trace _ original reduced operations select
    (squareEquationNumber.symm ∘ pivot) cover
    (by simpa [Function.comp_def] using pivot_increasing)
    steps_checked (by simpa [Function.comp_def] using pivots_checked) coverage_checked

end JacobianTrace

/-- Rank 2101 in the actual Brent differential. This declaration depends on
the compiler-backed checks `steps_checked`, `pivots_checked`,
`pivot_increasing`, and `coverage_checked`. -/
theorem square_jacobian_rank (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k (Set.range (fun x : Variable SquareVertex SquareSummand =>
      fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) = 2101 := by
  have sameColumn (x : Variable SquareVertex SquareSummand) (e : EquationIndex SquareVertex) :
      (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2 =
        SparseRow.decode (K := k) (fun e => (squareEquationNumber e).val)
          (squareJacobianColumn x) e := by
    simp only [SparseRow.decode, squareJacobianColumn_correct]
    obtain ⟨s, m, x⟩ := x
    obtain ⟨a, b, c⟩ := e
    cases m <;>
      simp only [Decomposition.jacobianColumn_eq, strassenSquare, Decomposition.map] <;>
        split_ifs <;> simp
  have hsame : Set.range (fun x : Variable SquareVertex SquareSummand =>
      fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2) =
      Set.range (fun i => SparseRow.decode (K := k) (fun e : EquationIndex SquareVertex =>
        (squareEquationNumber e).val) (JacobianTrace.original i)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨squareVariableNumber x, ?_⟩
      funext e
      simpa [JacobianTrace.original] using (sameColumn x e).symm
    · rintro ⟨x, rfl⟩
      exact ⟨squareVariableNumber.symm x, funext (sameColumn (squareVariableNumber.symm x))⟩
  rw [hsame, JacobianTrace.rank_decoded]

/-- The kernel of the linearized Brent equations has dimension 251.
This calculation uses the same compiler assumptions as the rank declaration. -/
theorem square_jacobian_nullity (k : Type*) [Field k] :
    Module.finrank k (LinearMap.ker (squareDifferential k)) = 251 :=
  square_nullity_of_rank k 2101 (square_jacobian_rank k)

end Brent
