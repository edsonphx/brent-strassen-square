import Brent.RadixReplay
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace Brent.SparseRow

/-- Apply a sparse linear map, permitting several contributions at each output coordinate. -/
def contract (A : Nat → Row) (r : Row) : Row :=
  r.flatMap fun (j, a) => (A j).map fun (i, b) => (i, a * b)

theorem coefficient_append (r t : Row) (j : Nat) :
    coefficient j (r ++ t) = coefficient j r + coefficient j t := by
  induction r with
  | nil => simp [coefficient]
  | cons x xs ih =>
    rcases x with ⟨i, a⟩
    simp [coefficient, ih, add_assoc]

theorem coefficient_flatMap {ι : Type*} (values : List ι) (f : ι → Row) (j : Nat) :
    coefficient j (values.flatMap f) = (values.map fun x => coefficient j (f x)).sum := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, coefficient_append, ih, List.map_cons, List.sum_cons]

theorem coefficient_indexedMap {ι : Type*} (values : List ι) (f : ι → Nat × Int) (j : Nat) :
    coefficient j (values.map f) = (values.map fun x => if (f x).1 = j then (f x).2 else 0).sum := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    rcases eq : f x with ⟨k,v⟩
    simp [eq, coefficient, ih]

private theorem coefficient_scale (a : Int) (r : Row) (j : Nat) :
    coefficient j (r.map fun (i, b) => (i, a * b)) = a * coefficient j r := by
  induction r with
  | nil => simp [coefficient]
  | cons x xs ih =>
    rcases x with ⟨i, b⟩
    simp only [List.map_cons, coefficient, ih, mul_add, mul_ite, mul_zero]

theorem coefficient_contract (A : Nat → Row) (r : Row) (j : Nat) :
    coefficient j (contract A r) = (r.map fun x => x.2 * coefficient j (A x.1)).sum := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i, a⟩
    simp only [contract, List.flatMap_cons, coefficient_append, coefficient_scale, List.map_cons, List.sum_cons]
    rw [← contract, ih]

/-- Check a congruence by supplying the integer quotient in each coordinate. -/
def checkMod (width bits : Nat) (p : Int) (actual expected quotient : Row) : Bool :=
  checkRadixStep width bits (fun _ : Fin 2 => actual)
    (fun i => if i = 0 then quotient else expected) (fun _ => [(0, p)]) 1

theorem checked_mod {p : Nat} (width bits : Nat) (actual expected quotient : Row)
    (h : checkMod width bits p actual expected quotient = true) (j : Fin width) :
    (coefficient j.val actual : ZMod p) = (coefficient j.val expected : ZMod p) := by
  have he := (checked_radix_step width bits (fun _ : Fin 2 => actual)
    (fun i => if i = 0 then quotient else expected) (fun _ => [(0, (p : Int))]) 1 h).2 j
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, if_true, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero] at he
  have cast := congrArg (fun i : Int => (i : ZMod p)) he
  simpa using cast.symm

theorem coefficient_contract_dense (A : Nat → Row) (r : Row) (width j : Nat)
    (fits : ∀ x ∈ r, x.1 < width) :
    coefficient j (contract A r) =
      ∑ i : Fin width, coefficient i.val r * coefficient j (A i.val) := by
  rw [coefficient_contract]
  induction r with
  | nil => simp [coefficient]
  | cons x xs ih =>
    rcases x with ⟨i,a⟩
    have hi := fits _ (List.mem_cons_self ..)
    have rest := ih (fun x hx => fits x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, coefficient, add_mul, Finset.sum_add_distrib]
    rw [rest]
    congr 1
    let k : Fin width := ⟨i, hi⟩
    have eq (l : Fin width) : i = l.val ↔ l = k := ⟨fun h => Fin.ext h.symm, fun h => h ▸ rfl⟩
    simp [eq, ite_mul, k]

end Brent.SparseRow
