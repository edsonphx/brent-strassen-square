import Brent.RankCertificate
import Mathlib.Data.Int.Cast.Lemmas

namespace Brent.SparseRow

/-- Decode a sparse row into a vector over the field used for the rank theorem. -/
def decode {K κ : Type*} [Field K] (coord : κ → Nat) (r : Row) (i : κ) : K :=
  coefficient (coord i) r

private theorem decode_reduce {K κ : Type*} [Field K] {ι : Type*}
    (coord : κ → Nat) (prior : ι → Row) (r : Row) (trace : List (ι × ℤ)) :
    (decode (K := K) coord (reduce prior r trace)) =
      decode coord r - (trace.map fun (i, a) => (a : K) • decode coord (prior i)).sum := by
  induction trace generalizing r with
  | nil => simp [reduce]
  | cons head tail ih =>
    rcases head with ⟨i, a⟩
    have he : decode (K := K) coord (subScaled a r (prior i)) =
        decode coord r - (a : K) • decode coord (prior i) := by
      funext j
      simp [decode, coefficient_subScaled, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [reduce, ih, he, List.map_cons, List.sum_cons]
    abel

/-- One independently checkable step in an integer pivot trace. -/
def checkStep {n : ℕ} (original reduced : Fin n → Row)
    (steps : Fin n → List (Fin n × ℤ)) (i : Fin n) : Bool :=
  (steps i).all (fun a => decide (a.1 < i)) &&
    decide (reduce reduced (original i) (steps i) = reduced i)

private theorem coeff_zero_below (r : Row) (pivot k : Nat) (hk : k < pivot)
    (h : r.all (fun a => decide (pivot ≤ a.1)) = true) : coefficient k r = 0 := by
  induction r with
  | nil => rfl
  | cons a tail ih =>
    rcases a with ⟨j, v⟩
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hne : j ≠ k := by omega
    simp [coefficient, hne, ih h.2]

/-- A unit pivot is present, and no entries occur before it. -/
def checkPivot (r : Row) (pivot : Nat) : Bool :=
  let c := coefficient pivot r
  (decide (c = 1) || decide (c = -1)) &&
    r.all (fun a => decide (pivot ≤ a.1))

/-- Check that a source row is either zero or one of the selected rows. -/
def checkCover {n r : ℕ} (reduced : Fin n → Row)
    (select : Fin r → Fin n) (index : Fin n → Option (Fin r)) (i : Fin n) : Bool :=
  match index i with
  | none => decide (reduced i = [])
  | some j => decide (select j = i)

/-- Integer row identities and unit pivots certify the rank over every field. -/
theorem rank_of_elimination_certificate {K κ : Type*} [Field K] {n r : ℕ}
    (coord : κ → Nat) (original reduced : Fin n → Row) (steps : Fin n → List (Fin n × ℤ))
    (select : Fin r → Fin n) (pivot : Fin r → κ) (index : Fin n → Option (Fin r))
    (increasing : StrictMono (coord ∘ pivot))
    (earlier : ∀ i, ∀ x ∈ steps i, x.1 < i)
    (identity : ∀ i j, coefficient (coord j) (reduced i) = coefficient (coord j) (original i) -
      ((steps i).map fun x => x.2 * coefficient (coord j) (reduced x.1)).sum)
    (hpiv : ∀ i, checkPivot (reduced (select i)) (coord (pivot i)) = true)
    (hcover : ∀ i, checkCover reduced select index i = true) :
    Module.finrank K (Submodule.span K (Set.range (fun i => decode (K := K) coord (original i)))) = r := by
  have hp (i : Fin r) := hpiv i
  simp only [checkPivot, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
  apply rowRank_eq_of_elimination (reduced := fun i => decode coord (reduced i))
    (steps := fun i => (steps i).map fun (j, a) => (j, (a : K))) (select := select) (pivot := pivot)
  · intro i x hx
    obtain ⟨⟨j, a⟩, hj, rfl⟩ := List.mem_map.mp hx
    exact earlier i _ hj
  · intro i
    have equal : (decode (K := K) coord (reduce reduced (original i) (steps i))) =
        decode coord (reduced i) := by
      funext j
      simp only [decode, coefficient_reduce, identity i j]
    have hh := decode_reduce (K := K) coord reduced (original i) (steps i)
    rw [equal] at hh
    simpa [List.map_map, Function.comp_def] using hh
  · intro i
    rcases (hp i).1 with h | h <;> simp [decode, h]
  · intro i j hj
    have hlt : coord (pivot j) < coord (pivot i) := increasing hj
    have hz := coeff_zero_below _ _ _ hlt (hp i).2
    simp [decode, hz]
  · intro i
    have hh := hcover i
    cases h : index i with
    | none =>
      left
      simp [checkCover, h] at hh
      funext j
      simp [decode, hh, coefficient]
    | some j =>
      right
      exact ⟨j, by simpa [checkCover, h] using hh⟩

/-- Replay soundness for the sparse merge checker. -/
theorem rank_of_checked_trace {K κ : Type*} [Field K] {n r : ℕ}
    (coord : κ → Nat) (original reduced : Fin n → Row) (steps : Fin n → List (Fin n × ℤ))
    (select : Fin r → Fin n) (pivot : Fin r → κ) (index : Fin n → Option (Fin r))
    (increasing : StrictMono (coord ∘ pivot))
    (hstep : ∀ i, checkStep original reduced steps i = true)
    (hpiv : ∀ i, checkPivot (reduced (select i)) (coord (pivot i)) = true)
    (hcover : ∀ i, checkCover reduced select index i = true) :
    Module.finrank K (Submodule.span K (Set.range (fun i => decode (K := K) coord (original i)))) = r := by
  have ht (i : Fin n) := hstep i
  simp only [checkStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  apply rank_of_elimination_certificate coord original reduced steps select pivot index increasing
    (fun i => (ht i).1) _ hpiv hcover
  intro i j
  have hh := coefficient_reduce reduced (original i) (steps i) (coord j)
  rwa [(ht i).2] at hh

end Brent.SparseRow
