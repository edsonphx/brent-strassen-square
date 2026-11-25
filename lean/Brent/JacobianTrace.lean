import Brent.RankReplay
import Brent.SquareJacobian
import Brent.Generated.JacobianData

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

def original (i : Fin 2352) := squareJacobianColumn (squareVariableNumber.symm i)
def reduced (i : Fin 2352) := unpack 256 (pick reducedData i.val)
def operations (i : Fin 2352) : List (Fin 2352 × Int) :=
  (unpack 256 (pick operationsData i.val)).map fun (j, x) => (Fin.ofNat 2352 j, x)
def select (i : Fin 2101) := pick selectData i.val
def pivot (i : Fin 2101) := pick pivotData i.val
def cover (i : Fin 2352) := pick coverData i.val

end JacobianTrace

/-- Identify the sparse column rank with the differential of the Brent equations. -/
theorem square_jacobian_rank_of_trace (k : Type*) [Field k] (rank : Nat)
    (traceRank : Module.finrank k (Submodule.span k (Set.range (fun i =>
        SparseRow.decode (K := k) (fun e : EquationIndex SquareVertex =>
          (squareEquationNumber e).val) (JacobianTrace.original i)))) = rank) :
    Module.finrank k (Submodule.span k (Set.range (fun x : Variable SquareVertex SquareSummand =>
      fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) = rank := by
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
  rw [hsame, traceRank]

end Brent
