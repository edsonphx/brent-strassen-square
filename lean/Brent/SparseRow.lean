import Mathlib.Algebra.BigOperators.Ring.Finset
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

/-- Merge sorted sparse rows and compute `x - a * y`, omitting new zeros. -/
def subScaled (a : Int) : Row → Row → Row
  | x, [] => x
  | [], (j, y) :: ys => writeEntry j (-a * y) (subScaled a [] ys)
  | (i, x) :: xs, (j, y) :: ys =>
    if i < j then (i, x) :: subScaled a xs ((j, y) :: ys)
    else if j < i then writeEntry j (-a * y) (subScaled a ((i, x) :: xs) ys)
    else writeEntry i (x - a * y) (subScaled a xs ys)
termination_by xs ys => xs.length + ys.length

theorem coefficient_subScaled (a : Int) (xs ys : Row) (k : Nat) :
    coefficient k (subScaled a xs ys) = coefficient k xs - a * coefficient k ys := by
  fun_induction subScaled a xs ys with
  | case1 xs => simp [coefficient]
  | case2 j y ys ih =>
    rw [coefficient_writeEntry, ih]
    by_cases h : j = k <;> simp [coefficient, h]
    all_goals ring
  | case3 i x xs j y ys h ih =>
    simp only [coefficient, ih]
    ring
  | case4 i x xs j y ys h₁ h₂ ih =>
    rw [coefficient_writeEntry, ih]
    by_cases h : j = k <;> simp [coefficient, h]
    all_goals ring
  | case5 i x xs j y ys h₁ h₂ ih =>
    have h : j = i := by omega
    subst j
    rw [coefficient_writeEntry, ih]
    by_cases h : i = k <;> simp [coefficient, h]
    all_goals ring

end Brent.SparseRow
