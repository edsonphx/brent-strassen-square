import Brent.Generated.TangentData
import Brent.Generated.RankChecks
import Brent.SparseContraction
import Mathlib.Algebra.BigOperators.Ring.List

open scoped BigOperators

namespace Brent.TangentData

private def pick {α : Type*} [Inhabited α] (data : Array (Array α)) (i : Nat) : α :=
  (data[i / 48]!)[i % 48]!

private def unpack (fuel packed : Nat) : SparseRow.Row :=
  match fuel with
  | 0 => []
  | n + 1 => if packed = 0 then [] else
    let word := packed % 65536
    let magnitude : Int := (word % 8) / 2
    (word / 8, if word % 2 = 0 then magnitude else -magnitude) ::
      unpack n (packed / 65536)

/-- The archived frame in the order (G,X,Y). -/
def frame (i : Fin 251) : SparseRow.Row := unpack 256 (pick tangentData i.val)
private def reduced (i : Fin 251) : SparseRow.Row := unpack 512 (pick tangentReducedData i.val)
private def operations (i : Fin 251) : List (Fin 251 × Int) :=
  (unpack 256 (pick tangentOperationsData i.val)).map fun (k, a) => (Fin.ofNat 251 k, a)
private def select (i : Fin 251) := pick tangentSelectData i.val
private def pivot (i : Fin 251) := pick tangentPivotData i.val
private def cover (i : Fin 251) := pick tangentCoverData i.val

/-- The local row identity and triangular-pivot conditions for one frame row. -/
def checkFrameRank (i : Fin 251) : Bool :=
  SparseRow.checkRadixStep 2352 12 frame reduced operations i &&
  SparseRow.checkPivot (reduced (select i)) (pivot i).val &&
  SparseRow.checkCover reduced select cover i &&
  if h : i.val + 1 < 251 then decide ((pivot i).val < (pivot ⟨i.val + 1, h⟩).val)
  else true

private theorem steps_of_rank (h : ∀ i, checkFrameRank i = true) :
    ∀ i, SparseRow.checkRadixStep 2352 12 frame reduced operations i = true := by
  intro i
  have hi := h i
  simp only [checkFrameRank, Bool.and_eq_true] at hi
  exact hi.1.1.1

/-- The checked archived frame has rank 251 over every field. -/
theorem frame_rank_of_checks (checks : ∀ i, checkFrameRank i = true) (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k
      (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i)))) = 251 := by
  have checked (i : Fin 251) := checks i
  simp only [checkFrameRank, Bool.and_eq_true] at checked
  apply SparseRow.rank_of_checked_radix_trace 12 id frame reduced operations select pivot cover
  · change StrictMono (Fin.val ∘ pivot)
    rw [Fin.strictMono_iff_lt_succ]
    intro (i : Fin 250)
    have hi := checked i.castSucc
    have hb : i.castSucc.val + 1 < 251 := by have := i.isLt; simpa using Nat.succ_lt_succ this
    have hor := hi.2
    simp only [dif_pos hb, decide_eq_true_eq] at hor
    exact hor
  · exact steps_of_rank checks
  · exact fun i => (checked i).1.1.2
  · exact fun i => (checked i).1.2

private def dot (r : SparseRow.Row) (a : Nat → Int) : Int :=
  (r.map fun (i, c) => c * a i).sum

private theorem dot_contract (A : Nat → SparseRow.Row) (r : SparseRow.Row) (a : Nat → Int) :
    dot (SparseRow.contract A r) a = dot r (fun i => dot (A i) a) := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i,c⟩ := x
    simp only [dot, SparseRow.contract, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, List.map_cons, List.sum_cons, mul_assoc]
    rw [List.sum_map_mul_left]
    exact congrArg (_ + ·) ih

private theorem dot_dense (r : SparseRow.Row) (a : Nat → Int) (n : Nat)
    (fits : ∀ x ∈ r, x.1 < n) :
    dot r a = ∑ i : Fin n, SparseRow.coefficient i.val r * a i.val := by
  induction r with
  | nil => simp [dot, SparseRow.coefficient]
  | cons x xs ih =>
    rcases x with ⟨i,c⟩
    have hi := fits _ (List.mem_cons_self ..)
    have rest := ih (fun x hx => fits x (List.mem_cons_of_mem _ hx))
    simp only [dot, List.map_cons, List.sum_cons, SparseRow.coefficient, add_mul, Finset.sum_add_distrib]
    change c * a i + dot xs a = _
    rw [rest]
    congr 1
    let k : Fin n := ⟨i, hi⟩
    have eq (l : Fin n) : i = l.val ↔ l = k := ⟨fun h => Fin.ext h.symm, fun h => h ▸ rfl⟩
    simp [eq, ite_mul, k]

private def replaceByPivot (x : Fin 2352 × Int) : Option (Nat × Int) :=
  (JacobianTrace.cover x.1).map fun j => (j.val, x.2)

private def expansion (i : Nat) : SparseRow.Row :=
  let j := Fin.ofNat 2352 i
  ((j, (1 : Int)) :: JacobianTrace.operations j).filterMap replaceByPivot

private theorem pivot_fold (l : List (Fin 2352 × Int)) (e : Nat) :
    dot (l.filterMap replaceByPivot)
        (fun j => SparseRow.coefficient e (JacobianTrace.reduced (JacobianTrace.select (Fin.ofNat 2101 j)))) =
      (l.map fun x => x.2 * SparseRow.coefficient e (JacobianTrace.reduced x.1)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h := JacobianTrace.coverage_of_auxiliary JacobianTrace.checkedAuxiliary x.1
    cases hv : JacobianTrace.cover x.1 with
    | none =>
      simp [SparseRow.checkCover, hv] at h
      simpa [dot, replaceByPivot, hv, h, SparseRow.coefficient] using ih
    | some j =>
      simp [SparseRow.checkCover, hv] at h
      have hj : Fin.ofNat 2101 j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
      simp only [List.filterMap_cons, replaceByPivot, hv, Option.map_some, dot,
        List.map_cons, List.sum_cons, hj, h]
      exact congrArg (_ + ·) ih

private theorem evaluate_expansion (i : Fin 2352) (e : Fin 4096) :
    dot (expansion i.val)
        (fun j => SparseRow.coefficient e.val (JacobianTrace.reduced (JacobianTrace.select (Fin.ofNat 2101 j)))) =
      SparseRow.coefficient e.val (JacobianTrace.original i) := by
  have hi : Fin.ofNat 2352 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [expansion, hi, pivot_fold]
  simp only [List.map_cons, List.sum_cons, one_mul]
  have h := (SparseRow.checked_radix_step 4096 12 _ _ _ i (JacobianTrace.checkedSteps i)).2 e
  exact (sub_eq_iff_eq_add.mp h.symm).symm

private def projected (i : Fin 251) : SparseRow.Row := SparseRow.contract expansion (frame i)

def checkTangent (i : Fin 251) : Bool :=
  SparseRow.checkRadixStep 2101 16 (fun _ : Fin 1 => projected i) (fun _ => []) (fun _ => []) 0

def checkFrame (i : Fin 251) : Bool := checkFrameRank i && checkTangent i

private theorem projected_fits (checkedTangent : ∀ i, checkTangent i = true) (i : Fin 251) : ∀ x ∈ projected i, x.1 < 2101 := by
  have h := checkedTangent i
  simp only [checkTangent, SparseRow.checkRadixStep, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  exact h.1.1.1.1

private theorem frame_fits (checkedRank : ∀ i, checkFrameRank i = true) (i : Fin 251) : ∀ x ∈ frame i, x.1 < 2352 := by
  have h := steps_of_rank checkedRank i
  simp only [SparseRow.checkRadixStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

private theorem projected_zero (checkedTangent : ∀ i, checkTangent i = true) (i : Fin 251) (e : Fin 2101) :
    SparseRow.coefficient e.val (projected i) = 0 := by
  have h := (SparseRow.checked_radix_step 2101 16 (fun _ : Fin 1 => projected i)
    (fun _ => []) (fun _ => []) 0 (checkedTangent i)).2 e
  simpa [SparseRow.coefficient] using h.symm

private theorem sparse_tangent (checkedRank : ∀ i, checkFrameRank i = true)
    (checkedTangent : ∀ i, checkTangent i = true) (i : Fin 251) (e : Fin 4096) :
    ∑ j : Fin 2352,
      SparseRow.coefficient j.val (frame i) * SparseRow.coefficient e.val (JacobianTrace.original j) = 0 := by
  let test (j : Nat) := SparseRow.coefficient e.val
    (JacobianTrace.reduced (JacobianTrace.select (Fin.ofNat 2101 j)))
  have hz : dot (projected i) test = 0 := by
    rw [dot_dense _ _ 2101 (projected_fits checkedTangent i)]
    simp only [projected_zero checkedTangent, zero_mul, Finset.sum_const_zero]
  unfold projected at hz
  rw [dot_contract, dot_dense _ _ 2352 (frame_fits checkedRank i)] at hz
  simpa only [test, evaluate_expansion] using hz

/-- All 251 archived directions annihilate the signed integer Brent Jacobian. -/
theorem frame_tangent_of_checks (checkedRank : ∀ i, checkFrameRank i = true)
    (checkedTangent : ∀ i, checkTangent i = true) (i : Fin 251) (e : EquationIndex SquareVertex) :
    ∑ j : Fin 2352, SparseRow.coefficient j.val (frame i) *
      strassenSquareInt.jacobianColumn (squareVariableNumber.symm j) e.1 e.2.1 e.2.2 = 0 := by
  simpa only [JacobianTrace.original, squareJacobianColumn_correct] using
    sparse_tangent checkedRank checkedTangent i (squareEquationNumber e)

end Brent.TangentData
