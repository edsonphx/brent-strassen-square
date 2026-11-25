import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace Brent.SparseRow

/-- A sparse integer row. Semantics sum duplicate coordinates, so the
arithmetic soundness lemma does not need a sortedness hypothesis. -/
abbrev Row := List (Nat × Int)

def coefficient (j : Nat) : Row → Int
  | [] => 0
  | (i, v) :: tail => (if i = j then v else 0) + coefficient j tail

private def writeEntry (i : Nat) (v : Int) (tail : Row) : Row :=
  if v = 0 then tail else (i, v) :: tail

private theorem coefficient_writeEntry (j i : Nat) (v : Int) (tail : Row) :
    coefficient j (writeEntry i v tail) = (if i = j then v else 0) + coefficient j tail := by
  by_cases h : v = 0 <;> simp [writeEntry, coefficient, h]

/-- Build a row from an indexed rectangular block of possible entries. -/
def ofIndexed {n : Nat} (f : Fin n → Nat × Int) : Row :=
  (List.ofFn f).filter fun x => x.2 != 0

theorem coefficient_ofIndexed {n : Nat} (f : Fin n → Nat × Int) (k : Nat) :
    coefficient k (ofIndexed f) =
      ∑ i, if (f i).1 = k then (f i).2 else 0 := by
  induction n with
  | zero => simp [ofIndexed, coefficient]
  | succ n ih =>
    rw [ofIndexed, List.ofFn_succ, List.filter_cons, Fin.sum_univ_succ]
    by_cases hz : (f 0).2 = 0
    · simp [hz]
      exact ih _
    · simp [hz, coefficient]
      rw [← ofIndexed, ih]

private def merge (a : Int) : Nat → Row → Row → Row
  | 0, x, _ => x
  | _ + 1, x, [] => x
  | n + 1, [], (j, y) :: ys => writeEntry j (-a * y) (merge a n [] ys)
  | n + 1, (i, x) :: xs, (j, y) :: ys =>
    if i < j then (i, x) :: merge a n xs ((j, y) :: ys)
    else if j < i then writeEntry j (-a * y) (merge a n ((i, x) :: xs) ys)
    else writeEntry i (x - a * y) (merge a n xs ys)

private theorem coefficient_merge (a : Int) (fuel : Nat) (xs ys : Row) (k : Nat)
    (enough : xs.length + ys.length ≤ fuel) :
    coefficient k (merge a fuel xs ys) = coefficient k xs - a * coefficient k ys := by
  induction fuel generalizing xs ys with
  | zero =>
    have h : ys = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h, merge, coefficient]
  | succ n ih =>
    cases ys with
    | nil => simp [merge, coefficient]
    | cons y ys =>
      rcases y with ⟨j, y⟩
      cases xs with
      | nil =>
        simp only [merge, coefficient_writeEntry]
        rw [ih _ _ (by simp at enough ⊢; omega)]
        by_cases h : j = k <;> simp [coefficient, h]
        all_goals ring
      | cons x xs =>
        rcases x with ⟨i, x⟩
        simp only [merge]
        split_ifs with hlt hgt
        · rw [coefficient, ih _ _ (by simp at enough ⊢; omega)]
          simp only [coefficient]
          ring
        · rw [coefficient_writeEntry, ih _ _ (by simp at enough ⊢; omega)]
          by_cases h : j = k <;> simp [coefficient, h]
          all_goals ring
        · have heq : j = i := by omega
          subst j
          rw [coefficient_writeEntry, ih _ _ (by simp at enough ⊢; omega)]
          by_cases h : i = k <;> simp [coefficient, h]
          all_goals ring

/-- Merge sorted sparse rows and compute `x - a * y`, omitting new zeros. -/
def subScaled (a : Int) (xs ys : Row) : Row :=
  merge a (xs.length + ys.length) xs ys

theorem coefficient_subScaled (a : Int) (xs ys : Row) (k : Nat) :
    coefficient k (subScaled a xs ys) = coefficient k xs - a * coefficient k ys :=
  coefficient_merge a _ xs ys k le_rfl

/-- Replay a row of an elimination trace. Indices refer to already supplied pivot rows. -/
def reduce {ι : Type*} (prior : ι → Row) (row : Row) : List (ι × Int) → Row
  | [] => row
  | (i, a) :: steps => reduce prior (subScaled a row (prior i)) steps

theorem coefficient_reduce {ι : Type*} (prior : ι → Row) (row : Row)
    (steps : List (ι × Int)) (k : Nat) :
    coefficient k (reduce prior row steps) =
      coefficient k row - (steps.map fun (i, a) => a * coefficient k (prior i)).sum := by
  induction steps generalizing row with
  | nil => simp [reduce]
  | cons head tail ih =>
    rcases head with ⟨i, a⟩
    simp only [reduce, ih, coefficient_subScaled, List.map_cons, List.sum_cons]
    ring

end Brent.SparseRow
