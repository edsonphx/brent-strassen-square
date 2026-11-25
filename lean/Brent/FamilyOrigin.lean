import Brent.BlockTangents
import Brent.FrameBlocks
import Brent.Generated.FamilyOrigins

open scoped BigOperators

namespace Brent.TangentData

private def sourceIndex (i : Fin 251) : Nat :=
  (familyOrigins[i.val / 48]!)[i.val % 48]!

private def sourceTerm (n : Nat) : SquareSummand :=
  finProdFinEquiv.symm (Fin.ofNat 49 (n / 2))

private def sourceVertex (n : Nat) : Fin 3 × SquareVertex × SquareVertex :=
  (Fin.ofNat 3 (n / 16),
    finProdFinEquiv.symm (Fin.ofNat 4 (n / 4)),
    finProdFinEquiv.symm (Fin.ofNat 4 n))

private def sourceBlock (n : Nat) : Fin 7 × Fin 3 × Fin 2 × Fin 2 :=
  (Fin.ofNat 7 (n / 12), Fin.ofNat 3 (n / 4), Fin.ofNat 2 (n / 2), Fin.ofNat 2 n)

/-- A frame index is available in the left chart unless in the right-only block,
and in the right chart unless in the left-only block. -/
def InChart (i : Fin 251) (left : Bool) : Prop :=
  if left then i.val < 197 else i.val < 143 ∨ 197 ≤ i.val

def frameOrigin (R : Type) [CommRing R] (i : Fin 251) : FamilyParameters (DualNumber R) :=
  let n := sourceIndex i
  if i.val < 143 then
    if n < 98 then FamilyParameters.termUnit (sourceTerm n) (n % 2 == 0)
    else
      let v := sourceVertex (n - 98)
      FamilyParameters.globalUnit v.1 v.2.1 v.2.2
  else
    let v := sourceBlock n
    FamilyParameters.blockUnit v.1 v.2.1 v.2.2.1 v.2.2.2

theorem frameOrigin_base (R : Type) [CommRing R] (i : Fin 251) :
    (frameOrigin R i).map (Jets.forget R) = FamilyParameters.one R := by
  unfold frameOrigin
  by_cases h : i.val < 143 <;> by_cases hn : sourceIndex i < 98 <;> simp [h, hn]

private def originCoefficient (R : Type) [CommRing R] (i : Fin 251)
    (x : Variable SquareVertex SquareSummand) : R :=
  let (s, m, (a, b)) := x
  let n := sourceIndex i
  if i.val < 143 then
    if n < 98 then
      FamilyParameters.termUnitCoefficient (strassenSquare R) (sourceTerm n) (n % 2 == 0) s m a b
    else
      let v := sourceVertex (n - 98)
      (strassenSquare R).vertexUnitCoefficient v.1 v.2.1 v.2.2 s m a b
  else
    let v := sourceBlock n
    FamilyParameters.blockUnitCoefficient (i.val < 197) v.1 v.2.1 v.2.2.1 v.2.2.2 s m a b

private theorem frameOrigin_tangent (R : Type) [CommRing R] (i : Fin 251)
    (left : Bool) (h : InChart i left) (x : Variable SquareVertex SquareSummand) :
    ((frameOrigin R i).value left).tangentPart.coordinates x = originCoefficient R i x := by
  obtain ⟨s, m, a, b⟩ := x
  unfold frameOrigin originCoefficient
  dsimp only
  split_ifs with hi hn
  · exact FamilyParameters.termUnit_tangent ..
  · exact FamilyParameters.globalUnit_tangent ..
  · have ht : left = decide (i.val < 197) := by
      cases left <;> simp_all [InChart] <;> (try omega)
    rw [ht]
    exact FamilyParameters.blockUnit_tangent ..

private def originRow (i : Fin 251) : SparseRow.Row :=
  SparseRow.ofIndexed (fun j : Fin 2352 =>
    (j.val, originCoefficient Int i (squareVariableNumber.symm j)))

/-- Compare the computed chart derivative with the complete frozen signed frame vector. -/
def checkOrigin (i : Fin 251) : Bool :=
  decide (originRow i = frame i)

private theorem originRow_correct (i : Fin 251) (x : Variable SquareVertex SquareSummand) :
    SparseRow.coefficient (squareVariableNumber x).val (originRow i) = originCoefficient Int i x := by
  rw [originRow, SparseRow.coefficient_ofIndexed]
  simp only [Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.symm_apply_apply]

theorem origin_of_check (i : Fin 251) (left : Bool) (h : InChart i left)
    (hc : checkOrigin i = true) (x : Variable SquareVertex SquareSummand) :
    ((frameOrigin Int i).value left).tangentPart.coordinates x =
      SparseRow.coefficient (squareVariableNumber x).val (frame i) := by
  rw [frameOrigin_tangent Int i left h, ← originRow_correct]
  rw [checkOrigin, decide_eq_true_eq] at hc
  rw [hc]

end Brent.TangentData
