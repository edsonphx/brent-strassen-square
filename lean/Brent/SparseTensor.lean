import Brent.SparseContraction
import Brent.SquareJacobian
import Mathlib.Algebra.BigOperators.Ring.List

namespace Brent.SparseTensor

abbrev Coordinate := SquareVertex × SquareVertex

/-- The row-major numbering of the 16 entries in a mode. -/
def coordinateNumber : Coordinate ≃ Fin 16 :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

abbrev Factor := List (Fin 16 × Int)

def entry (r : Factor) (i : Fin 16) : Int :=
  (r.map fun x => if x.1 = i then x.2 else 0).sum

def ofFunction (f : Coordinate → Int) : Factor :=
  (List.ofFn (fun i => (i, f (coordinateNumber.symm i)))).filter (fun x => x.2 != 0)

theorem entry_ofFunction (f : Coordinate → Int) (i : Fin 16) :
    entry (ofFunction f) i = f (coordinateNumber.symm i) := by
  let p (j : Fin 16) : Nat × Int := (j.val, f (coordinateNumber.symm j))
  have eq : (ofFunction f).map (fun x => (x.1.val, x.2)) = SparseRow.ofIndexed p := by
    have move (xs : Factor) : (xs.filter (fun x => x.2 != 0)).map (fun x => (x.1.val, x.2)) =
        (xs.map (fun x => (x.1.val, x.2))).filter (fun x => x.2 != 0) := by
      rw [List.filter_map]
      rfl
    rw [ofFunction, SparseRow.ofIndexed, move, List.map_ofFn]
    rfl
  have convert (r : Factor) : SparseRow.coefficient i.val (r.map (fun x => (x.1.val, x.2))) = entry r i := by
    rw [SparseRow.coefficient_indexedMap]
    simp [entry, Fin.val_inj]
  rw [← convert, eq, SparseRow.coefficient_ofIndexed]
  simp [p, Fin.val_inj]

private def tripleIndex (a b c : Fin 16) : Nat :=
  (squareEquationNumber (coordinateNumber.symm a, coordinateNumber.symm b,
    coordinateNumber.symm c)).val

/-- Produce the sparse Kronecker contribution of three factor rows. -/
def tensor (u v w : Factor) : SparseRow.Row :=
  u.flatMap fun a => v.flatMap fun b => w.map fun c =>
    (tripleIndex a.1 b.1 c.1, a.2 * b.2 * c.2)

theorem coefficient_tensor (u v w : Factor) (e : EquationIndex SquareVertex) :
    SparseRow.coefficient (squareEquationNumber e).val (tensor u v w) =
      entry u (coordinateNumber e.1) * entry v (coordinateNumber e.2.1) *
        entry w (coordinateNumber e.2.2) := by
  have one (a b c : Fin 16) (d f g : Int) :
      (if tripleIndex a b c = (squareEquationNumber e).val then d * f * g else 0) =
        (if a = coordinateNumber e.1 then d else 0) *
        (if b = coordinateNumber e.2.1 then f else 0) *
        (if c = coordinateNumber e.2.2 then g else 0) := by
    obtain ⟨x, y, z⟩ := e
    simp only [tripleIndex, Fin.val_inj, Equiv.apply_eq_iff_eq,
      Prod.mk.injEq, Equiv.symm_apply_eq]
    split_ifs <;> simp_all
  simp only [tensor, SparseRow.coefficient_flatMap, SparseRow.coefficient_indexedMap, one,
    entry, List.sum_map_mul_left, List.sum_map_mul_right]

theorem tensor_fits (u v w : Factor) :
    ∀ x ∈ tensor u v w, x.1 < 4096 := by
  intro x hx
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hx
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  exact (squareEquationNumber (coordinateNumber.symm a.1, coordinateNumber.symm b.1,
    coordinateNumber.symm c.1)).isLt

end Brent.SparseTensor
