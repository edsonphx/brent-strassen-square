import Brent.RankReplay

open scoped BigOperators

namespace Brent.SparseRow

private theorem signed_radix (b : ℤ) (hb : b ≠ 0) {n : Nat} (digit : Fin n → ℤ)
    (bound : ∀ i, (digit i).natAbs < b.natAbs)
    (encoded : (∑ i, digit i * b ^ i.val) = 0) :
    ∀ i, digit i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have split : (∑ i, digit i * b ^ i.val) =
        digit 0 + b * ∑ j : Fin n, digit j.succ * b ^ j.val := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [split] at encoded
    have div : b ∣ digit 0 := by
      refine ⟨-(∑ j : Fin n, digit j.succ * b ^ j.val), ?_⟩
      rw [mul_neg]
      exact eq_neg_of_add_eq_zero_left encoded
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs div (bound 0)
    have tail : (∑ j : Fin n, digit j.succ * b ^ j.val) = 0 := by
      rw [h0, zero_add] at encoded
      exact (mul_eq_zero.mp encoded).resolve_left hb
    intro i
    induction i using Fin.cases with
    | zero => exact h0
    | succ j => exact ih (fun j => digit j.succ) (fun j => bound j.succ) tail j

/-- Encode the coefficients at distinct digit positions of an integer. -/
def radixEncode (bits : Nat) (r : Row) : Int :=
  (r.map fun (j, a) => a * (1 <<< (bits * j) : Nat)).sum

def coordinateBound (r : Row) : Nat := (r.map fun x => x.2.natAbs).sum

private theorem coefficient_natAbs_le (r : Row) (k : Nat) :
    (coefficient k r).natAbs ≤ coordinateBound r := by
  induction r with
  | nil => simp [coefficient, coordinateBound]
  | cons x xs ih =>
    rcases x with ⟨j, v⟩
    by_cases eq : j = k
    · simp only [coefficient, eq, if_true, coordinateBound, List.map_cons, List.sum_cons]
      exact (Int.natAbs_add_le ..).trans (Nat.add_le_add_left ih _)
    · simp [coefficient, coordinateBound, eq]
      exact ih.trans (Nat.le_add_left _ _)

private theorem encode_eq_sum (r : Row) (n b : Nat)
    (bounded : r.all (fun x => decide (x.1 < n)) = true) :
    radixEncode b r = ∑ i : Fin n, coefficient i.val r * (2 ^ b : Int) ^ i.val := by
  induction r with
  | nil => simp [radixEncode, coefficient]
  | cons x xs ih =>
    rcases x with ⟨j, v⟩
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at bounded
    simp only [radixEncode, List.map_cons, List.sum_cons, coefficient, add_mul, Finset.sum_add_distrib]
    rw [← ih bounded.2]
    congr 1
    let a : Fin n := ⟨j, bounded.1⟩
    have hj (i : Fin n) : j = i.val ↔ i = a := by
      constructor
      · exact fun eq => Fin.ext eq.symm
      · rintro rfl
        rfl
    simp only [hj, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change v * ↑(1 <<< (b * j) : Nat) = v * (2 ^ b : Int) ^ j
    simp [Nat.shiftLeft_eq, pow_mul]

/-- Check the elimination identity with signed radix arithmetic. The digit bound rules out
cancellation between coordinates, and the index checks rule out hidden terms outside the matrix. -/
def checkRadixStep {n : Nat} (width bits : Nat) (original reduced : Fin n → Row)
    (steps : Fin n → List (Fin n × Int)) (i : Fin n) : Bool :=
  let os := original i
  let rs := reduced i
  let ts := steps i
  let fits := fun (r : Row) => r.all fun x => decide (x.1 < width)
  fits os && fits rs &&
    (ts.all fun (j, _) => decide (j < i) && fits (reduced j)) &&
    decide (coordinateBound os + coordinateBound rs +
      (ts.map fun (j, a) => a.natAbs * coordinateBound (reduced j)).sum < 2 ^ bits) &&
    decide (radixEncode bits os =
      radixEncode bits rs + (ts.map fun (j, a) => a * radixEncode bits (reduced j)).sum)

private theorem combination_natAbs_le {ι : Type*} (r : ι → Row) (ts : List (ι × Int)) (k : Nat) :
    ((ts.map fun x => x.2 * coefficient k (r x.1)).sum).natAbs ≤
      (ts.map fun x => x.2.natAbs * coordinateBound (r x.1)).sum := by
  induction ts with
  | nil => simp [coordinateBound]
  | cons x xs ih =>
    rcases x with ⟨j, a⟩
    simp only [List.map_cons, List.sum_cons]
    apply (Int.natAbs_add_le ..).trans
    rw [Int.natAbs_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (coefficient_natAbs_le ..)) ih

private theorem encode_combination {ι : Type*} (r : ι → Row) (ts : List (ι × Int)) (n b : Nat)
    (fits : ∀ x ∈ ts, (r x.1).all (fun u => decide (u.1 < n)) = true) :
    (ts.map fun (j, a) => a * radixEncode b (r j)).sum =
      ∑ i : Fin n, (ts.map fun x => x.2 * coefficient i.val (r x.1)).sum * (2 ^ b : Int) ^ i.val := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨j, a⟩
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [encode_eq_sum _ _ _ (fits _ (List.mem_cons_self ..)),
      ih (fun x hx => fits x (List.mem_cons_of_mem _ hx)), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem checked_radix_step {n : Nat} (width bits : Nat) (original reduced : Fin n → Row)
    (steps : Fin n → List (Fin n × Int)) (i : Fin n)
    (h : checkRadixStep width bits original reduced steps i = true) :
    (∀ x ∈ steps i, x.1 < i) ∧ ∀ k : Fin width,
      coefficient k.val (reduced i) = coefficient k.val (original i) -
        ((steps i).map fun x => x.2 * coefficient k.val (reduced x.1)).sum := by
  simp only [checkRadixStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ho, hr⟩, ht⟩, hb⟩, he⟩ := h
  refine ⟨fun x hx => (ht x hx).1, ?_⟩
  have ho' : (original i).all (fun x => decide (x.1 < width)) = true :=
    List.all_eq_true.mpr (by simpa using ho)
  have hr' : (reduced i).all (fun x => decide (x.1 < width)) = true :=
    List.all_eq_true.mpr (by simpa using hr)
  rw [encode_eq_sum _ _ _ ho', encode_eq_sum _ _ _ hr',
    encode_combination _ _ width _ (fun x hx => List.all_eq_true.mpr (by simpa using (ht x hx).2))] at he
  let f (k : Fin width) := coefficient k.val (original i) - coefficient k.val (reduced i) -
    ((steps i).map fun x => x.2 * coefficient k.val (reduced x.1)).sum
  have hd (k : Fin width) : (f k).natAbs < (2 ^ bits : Int).natAbs := by
    rw [Int.natAbs_pow]
    dsimp [f]
    exact lt_of_le_of_lt ((Int.natAbs_sub_le ..).trans (Nat.add_le_add
      ((Int.natAbs_sub_le ..).trans (Nat.add_le_add (coefficient_natAbs_le ..) (coefficient_natAbs_le ..)))
      (combination_natAbs_le ..))) hb
  have hz : (∑ k, f k * (2 ^ bits : Int) ^ (k : Fin width).val) = 0 := by
    simp only [f, sub_mul, Finset.sum_sub_distrib]
    omega
  intro k
  have hk := signed_radix (2 ^ bits) (pow_ne_zero _ (by decide)) f hd hz k
  dsimp [f] at hk
  omega

/-- Transfer checked bounded-radix identities to the rank over every field. -/
theorem rank_of_checked_radix_trace {K κ : Type*} [Field K] {n r width : Nat}
    (bits : Nat) (coord : κ → Fin width) (original reduced : Fin n → Row)
    (steps : Fin n → List (Fin n × Int)) (select : Fin r → Fin n)
    (pivot : Fin r → κ) (index : Fin n → Option (Fin r))
    (increasing : StrictMono (Fin.val ∘ coord ∘ pivot))
    (hstep : ∀ i, checkRadixStep width bits original reduced steps i = true)
    (hpiv : ∀ i, checkPivot (reduced (select i)) (coord (pivot i)).val = true)
    (hcover : ∀ i, checkCover reduced select index i = true) :
    Module.finrank K (Submodule.span K (Set.range (fun i =>
      decode (K := K) (fun j => (coord j).val) (original i)))) = r :=
  rank_of_elimination_certificate _ original reduced steps select pivot index increasing
    (fun i => (checked_radix_step width bits _ _ _ i (hstep i)).1)
    (fun i j => (checked_radix_step width bits _ _ _ i (hstep i)).2 (coord j)) hpiv hcover

end Brent.SparseRow
