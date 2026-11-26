import Brent.PaperDetails
import Brent.Catalogue.Kernel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A finite-dimensional proof of the precise Hadamard estimate needed in
§7. Unlike the earlier factorial estimate, this proves det(M)^2 ≤ (m B²)^m
for EVERY integer matrix of size m ≤ 4 and arbitrary nonnegative entry
bound B. Multilinearity reduces the problem to the signed corners of the
entry box; the corners are checked using exact determinant formulas. -/

namespace Brent.PaperDetails.HadamardSmall
open Matrix

section Corners
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Change a single entry, leaving the other entries untouched. -/
def replaceEntry (M : Matrix n n ℤ) (i j : n) (t : ℤ) : Matrix n n ℤ :=
  M.updateRow i (Function.update (M i) j t)

theorem replaceEntry_apply (M : Matrix n n ℤ) (i j a b : n) (t : ℤ) :
    replaceEntry M i j t a b = if (a,b) = (i,j) then t else M a b := by
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j <;> simp [replaceEntry, hb]
  · simp [replaceEntry, ha]

/-- An affine determinant in one entry cannot have absolute value larger
than both endpoint determinants. No division or approximation is used. -/
theorem entry_endpoint (M : Matrix n n ℤ) (i j : n) (B : ℤ)
    (hB : 0 < B) (hx : |M i j| ≤ B) :
    |M.det| ≤ max |(replaceEntry M i j B).det| |(replaceEntry M i j (-B)).det| := by
  let u := B + M i j
  let v := B - M i j
  have hu : 0 ≤ u := by have h := (abs_le.mp hx).1; dsimp [u]; omega
  have hv : 0 ≤ v := by have h := (abs_le.mp hx).2; dsimp [v]; omega
  have huv : u + v = 2 * B := by dsimp [u,v]; ring
  have hrow : u • Function.update (M i) j B + v • Function.update (M i) j (-B) =
      (2 * B) • M i := by
    funext b
    by_cases h : b = j
    · subst b
      simp [u,v, Pi.smul_apply, smul_eq_mul]
      <;> ring
    · simp [h, u,v, Pi.smul_apply, smul_eq_mul]
      <;> ring
  have hdet : (2 * B) * M.det =
      u * (replaceEntry M i j B).det + v * (replaceEntry M i j (-B)).det := by
    calc
      _ = (M.updateRow i ((2 * B) • M i)).det := by
        rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
      _ = (M.updateRow i (u • Function.update (M i) j B +
          v • Function.update (M i) j (-B))).det := by rw [hrow]
      _ = _ := by rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
          Matrix.det_updateRow_smul] <;> rfl
  let C := max |(replaceEntry M i j B).det| |(replaceEntry M i j (-B)).det|
  have h₁ : u * |(replaceEntry M i j B).det| ≤ u * C :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hu
  have h₂ : v * |(replaceEntry M i j (-B)).det| ≤ v * C :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hv
  have hh := abs_add_le (u * (replaceEntry M i j B).det) (v * (replaceEntry M i j (-B)).det)
  rw [← hdet, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * B),
    abs_mul, abs_of_nonneg hu, abs_mul, abs_of_nonneg hv] at hh
  have hbnd : (2 * B) * |M.det| ≤ (2 * B) * C := by
    calc
      _ ≤ u * |(replaceEntry M i j B).det| + v * |(replaceEntry M i j (-B)).det| := hh
      _ ≤ u * C + v * C := add_le_add h₁ h₂
      _ = _ := by rw [← add_mul, huv]
  exact le_of_mul_le_mul_left hbnd (by positivity : 0 < 2 * B)

/-- Replacing all entries one by one yields a sign corner with at least as
large an absolute determinant. `S` is the set of entries not yet fixed. -/
theorem corner_dominates_aux (B : ℤ) (hB : 0 < B) (S : Finset (n × n))
    (M : Matrix n n ℤ) (hM : ∀ i j, |M i j| ≤ B)
    (hfixed : ∀ i j, (i,j) ∉ S → M i j = B ∨ M i j = -B) :
    ∃ N : Matrix n n ℤ, (∀ i j, N i j = B ∨ N i j = -B) ∧ |M.det| ≤ |N.det| := by
  induction S using Finset.induction_on generalizing M with
  | empty => exact ⟨M, fun i j => hfixed i j (by simp), le_rfl⟩
  | insert a S ha ih =>
    obtain ⟨i,j⟩ := a
    let P := replaceEntry M i j B
    let Q := replaceEntry M i j (-B)
    have h := entry_endpoint M i j B hB (hM i j)
    obtain ⟨t, ht, hd⟩ : ∃ t : ℤ, (t = B ∨ t = -B) ∧
        |M.det| ≤ |(replaceEntry M i j t).det| := by
      by_cases hPQ : |P.det| ≤ |Q.det|
      · exact ⟨-B, Or.inr rfl, h.trans_eq (max_eq_right hPQ)⟩
      · exact ⟨B, Or.inl rfl, h.trans_eq (max_eq_left (le_of_not_ge hPQ))⟩
    let T := replaceEntry M i j t
    have hT (a b : n) : |T a b| ≤ B := by
      rw [T, replaceEntry_apply]
      split_ifs
      · rcases ht with rfl | rfl <;> simp [abs_of_pos hB]
      · exact hM a b
    have hTF (a b : n) (hab : (a,b) ∉ S) : T a b = B ∨ T a b = -B := by
      rw [T, replaceEntry_apply]
      split_ifs with he
      · exact ht
      · exact hfixed a b (by simpa [he] using hab)
    obtain ⟨N,hN,hTN⟩ := ih T hT hTF
    exact ⟨N,hN,hd.trans hTN⟩

end Corners

/-- A computable sign, used only for the small finite endpoint certificates. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

def signMat {m : ℕ} (s : Fin m → Fin m → Bool) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => sign (s i j)

/-- The four-by-four integer determinant formula, tied to `Matrix.det`. -/
theorem det4_formula (A : Matrix (Fin 4) (Fin 4) ℤ) :
    A.det = Brent.Catalogue.det4 (fun i j => A (Fin.ofNat 4 i) (Fin.ofNat 4 j)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp (config := {decide := true}) only [Fin.succAbove, Fin.isValue, Fin.val_zero,
    Fin.val_one, Fin.val_two, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE, if_true, if_false]
  simp [Brent.Catalogue.det4, Brent.Catalogue.det3, Fin.ofNat]
  <;> ring

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sign_two_check : ∀ s : Fin 2 → Fin 2 → Bool,
    (sign (s 0 0) * sign (s 1 1) - sign (s 0 1) * sign (s 1 0))^2 ≤ (2 : ℤ)^2 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sign_three_check : ∀ s : Fin 3 → Fin 3 → Bool,
    (Brent.Catalogue.det3 (sign (s 0 0)) (sign (s 0 1)) (sign (s 0 2))
      (sign (s 1 0)) (sign (s 1 1)) (sign (s 1 2))
      (sign (s 2 0)) (sign (s 2 1)) (sign (s 2 2)))^2 ≤ (3 : ℤ)^3 := by
  decide +kernel

set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
/-- Exhaustive exact check on the 2^16 corners. It does not enumerate the
9^16 integer matrices or rely on an external determinant program. -/
theorem sign_four_check : ∀ s : Fin 4 → Fin 4 → Bool,
    (Brent.Catalogue.det4 (fun i j => sign (s (Fin.ofNat 4 i) (Fin.ofNat 4 j))))^2 ≤ (4 : ℤ)^4 := by
  decide +kernel

/-- Squared Hadamard inequality for sign matrices in the relevant sizes. -/
theorem sign_bound (m : ℕ) (hm : m ≤ 4) (s : Fin m → Fin m → Bool) :
    (signMat s).det^2 ≤ (m : ℤ)^m := by
  revert s
  interval_cases m <;> intro s
  · simp [Matrix.det_isEmpty]
  · rw [Matrix.det_fin_one]
    change (sign (s 0 0))^2 ≤ (1 : ℤ)^1
    cases h : s 0 0 <;> simp [sign, h]
  · simpa only [Matrix.det_fin_two, signMat] using sign_two_check s
  · simpa only [Matrix.det_fin_three, signMat, Brent.Catalogue.det3] using sign_three_check s
  · rw [det4_formula]
    exact sign_four_check s

/-- Exactly the bound used in §7, in an integer squared form. This statement
is uniform in the entry bound B and includes the empty minor. -/
theorem squared_hadamard_fin (m : ℕ) (hm : m ≤ 4) (M : Matrix (Fin m) (Fin m) ℤ)
    (B : ℤ) (hB : 0 ≤ B) (hM : ∀ i j, |M i j| ≤ B) :
    M.det^2 ≤ ((m : ℤ) * B^2)^m := by
  classical
  by_cases h0 : B = 0
  · have hM0 : M = 0 := by
      ext i j
      change M i j = 0
      have := hM i j
      rw [h0, abs_le] at this
      omega
    by_cases hm0 : m = 0
    · subst m; simp [Matrix.det_isEmpty]
    · haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm0⟩⟩
      rw [hM0, Matrix.det_zero inferInstance, h0]
      positivity
  · obtain ⟨N,hN,hd⟩ := corner_dominates_aux B (lt_of_le_of_ne hB (Ne.symm h0))
      (Finset.univ : Finset (Fin m × Fin m)) M hM (by simp)
    let s : Fin m → Fin m → Bool := fun i j => decide (N i j = B)
    have he : N = B • signMat s := by
      ext i j
      rcases hN i j with h | h
      · simp [signMat, sign, s, h, Matrix.smul_apply, smul_eq_mul]
      · have hn : N i j ≠ B := by omega
        simp [signMat, sign, s, hn, h, Matrix.smul_apply, smul_eq_mul]
    have hsq : M.det^2 ≤ N.det^2 := by
      have h := mul_le_mul hd hd (abs_nonneg _) (abs_nonneg _)
      simpa only [← pow_two, sq_abs] using h
    calc
      M.det^2 ≤ N.det^2 := hsq
      _ = (B^m)^2 * (signMat s).det^2 := by
        rw [he, Matrix.det_smul, Fintype.card_fin, mul_pow]
      _ ≤ (B^m)^2 * (m : ℤ)^m :=
        mul_le_mul_of_nonneg_left (sign_bound m hm s) (sq_nonneg _)
      _ = ((m : ℤ) * B^2)^m := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm m 2, mul_comm]

/-- The bound for an arbitrary finite index type of cardinality at most 4. -/
theorem squared_hadamard {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ)
    (hn : Fintype.card n ≤ 4) (B : ℤ) (hB : 0 ≤ B) (hM : ∀ i j, |M i j| ≤ B) :
    M.det^2 ≤ ((Fintype.card n : ℤ) * B^2)^Fintype.card n := by
  classical
  let e := (Fintype.equivFin n).symm
  simpa only [Matrix.det_submatrix_equiv_self] using
    squared_hadamard_fin (Fintype.card n) hn (M.submatrix e e) B hB (fun i j => hM (e i) (e j))

/-- The actual chosen prime exceeds the Hadamard estimate; hence its use in
all minors of the catalogue, even stacked matrices, is faithful. -/
theorem censusMinor_vanishing_iff_hadamard {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (hn : Fintype.card n ≤ 4) (hM : ∀ i j, |M i j| ≤ 4) :
    (M.map (Int.cast : ℤ → ZMod 65521)).det = 0 ↔ M.det = 0 := by
  have hsq := squared_hadamard M hn 4 (by norm_num) hM
  have hbound : ((Fintype.card n : ℤ) * 4^2)^Fintype.card n < (65521 : ℤ)^2 := by
    exact_mod_cast censusPrime_hadamard_expression ⟨Fintype.card n, by omega⟩
  have hlt : |M.det| < (65521 : ℤ) := by
    by_contra! h
    have hs := mul_le_mul h h (by norm_num : (0 : ℤ) ≤ 65521) (abs_nonneg _)
    have hs' : (65521 : ℤ)^2 ≤ M.det^2 := by
      simpa only [← pow_two, sq_abs] using hs
    exact (not_lt_of_ge hs') (hsq.trans_lt hbound)
  apply minor_vanishing_iff_mod_prime
  rw [← Int.natCast_natAbs] at hlt
  exact_mod_cast hlt

end Brent.PaperDetails.HadamardSmall
