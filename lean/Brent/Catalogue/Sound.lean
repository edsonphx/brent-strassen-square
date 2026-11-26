import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Brent.Catalogue.Defs

/-!
# Soundness of the kernel checks: ranks, profiles, rank bounds

* `certChk_sound`: a passing rank certificate pins `Matrix.rank` over any field of
  characteristic `q`;
* `rk_eq_of_matOK`: for a point whose `ranksOK` check passes, `rk ℚ` and `rk (ZMod 3)` are the
  certified ranks `rkC false` and `rkC true`;
* `profile_eq_full_iff`, `rankBounds_iff`: the profile and rank-bound predicates in terms of the
  certified ranks.
-/

namespace Brent.Catalogue

open Matrix

/-! ### Small computable helpers -/

theorem zq_iff {K : Type*} [Field K] (q : ℕ) [CharP K q] (x : ℤ) :
    zq q x = true ↔ (x : K) = 0 := by
  rw [CharP.intCast_eq_zero_iff K q x]
  cases q with
  | zero => simp [zq]
  | succ q => simp only [zq, beq_iff_eq]; rw [Int.dvd_iff_emod_eq_zero]

theorem zq_of_zq_zero (q : ℕ) (x : ℤ) (h : zq 0 x = true) : zq q x = true := by
  have hx : x = 0 := by simpa [zq] using h
  subst hx
  cases q <;> simp [zq]

theorem all16_iff (f : ℕ → ℕ → Bool) :
    all16 f = true ↔ ∀ i j : Fin 4, f i j = true := by
  constructor
  · intro h i j
    simp only [all16, Bool.and_eq_true] at h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    simp only [all16, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h 0 0, h 0 1⟩, h 0 2⟩, h 0 3⟩, h 1 0⟩, h 1 1⟩, h 1 2⟩, h 1 3⟩,
      h 2 0⟩, h 2 1⟩, h 2 2⟩, h 2 3⟩, h 3 0⟩, h 3 1⟩, h 3 2⟩, h 3 3⟩

theorem all16_mono {f g : ℕ → ℕ → Bool} (h : ∀ i j, f i j = true → g i j = true)
    (hf : all16 f = true) : all16 g = true :=
  (all16_iff g).2 fun i j => h i j ((all16_iff f).1 hf i j)

theorem allBelow_iff (n : ℕ) (f : ℕ → Bool) :
    allBelow n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

theorem cnt_eq (n : ℕ) (f : ℕ → Bool) :
    cnt n f = (Finset.univ.filter fun s : Fin n => f s.val = true).card := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [cnt, ih]
    simp only [Finset.card_filter, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
    rfl

/-! ### Ranks from Schur certificates -/

section Rank

variable {K : Type*} [Field K]

/-- A nonzero `r × r` minor `D = Mk[I, J]` with `det D • Mk = X * Mk[I, :]` pins the rank. -/
theorem rank_eq_of_schur {r : ℕ} (Mk : Matrix (Fin 4) (Fin 4) K) (I J : Fin r → Fin 4)
    (X : Matrix (Fin 4) (Fin r) K) (hδ : (Mk.submatrix I J).det ≠ 0)
    (hid : ∀ i j, (Mk.submatrix I J).det * Mk i j = ∑ a, X i a * Mk (I a) j) :
    Mk.rank = r := by
  set δ := (Mk.submatrix I J).det with hδdef
  apply le_antisymm
  · have hfac : Mk = (δ⁻¹ • X) * Mk.submatrix I id := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.submatrix_apply, id, smul_eq_mul]
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [← hid, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
    calc Mk.rank = ((δ⁻¹ • X) * Mk.submatrix I id).rank := by rw [← hfac]
      _ ≤ (δ⁻¹ • X).rank := Matrix.rank_mul_le_left _ _
      _ ≤ r := Matrix.rank_le_width _
  · set D := Mk.submatrix I J
    have hDu : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr hδ.isUnit
    have hrD : D.rank = r := by rw [Matrix.rank_of_isUnit D hDu, Fintype.card_fin]
    have hle : D.eRank ≤ Mk.eRank := Matrix.eRank_submatrix_le Mk I J
    rw [← hrD, ← Matrix.eRank_toNat_eq_rank, ← Matrix.eRank_toNat_eq_rank]
    have hfin : Mk.eRank ≠ ⊤ := ne_top_of_le_ne_top (by simp) (Matrix.eRank_le_card_width Mk)
    exact ENat.toNat_le_toNat hle hfin

/-- The matrix of a function on `ℕ × ℕ`, cast to `K`. -/
noncomputable abbrev matK (M : ℕ → ℕ → ℤ) : Matrix (Fin 4) (Fin 4) K :=
  (Matrix.of fun (i j : Fin 4) => M i j).map (Int.cast : ℤ → K)

variable (q : ℕ) [CharP K q]

theorem rank_zero_of (M : ℕ → ℕ → ℤ) (h : ∀ i j : Fin 4, zq q (M i j) = true) :
    (matK (K := K) M).rank = 0 := by
  have : matK (K := K) M = 0 := by
    ext i j; simpa using (zq_iff (K := K) q _).1 (h i j)
  rw [this, Matrix.rank_zero]

theorem rank_four_of (M : ℕ → ℕ → ℤ) (h : zq q (det4 M) = false) :
    (matK (K := K) M).rank = 4 := by
  have hdet : (matK (K := K) M).det = ((det4 M : ℤ) : K) := by
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.map_apply,
      Matrix.of_apply]
    simp (config := {decide := true}) only [Fin.succAbove, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE, if_true,
      if_false]
    simp [det4, det3]
    ring
  have hne : (matK (K := K) M).det ≠ 0 := by
    rw [hdet]; intro h0; rw [← zq_iff q] at h0; simp_all
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hne.isUnit), Fintype.card_fin]

theorem rank_one_of (M : ℕ → ℕ → ℤ) (i0 j0 : ℕ) (hi : i0 < 4) (hj : j0 < 4)
    (hd : zq q (M i0 j0) = false)
    (h : ∀ i j : Fin 4, zq q (M i0 j0 * M i j - M i j0 * M i0 j) = true) :
    (matK (K := K) M).rank = 1 := by
  refine rank_eq_of_schur _ ![⟨i0, hi⟩] ![⟨j0, hj⟩]
    (Matrix.of fun (i : Fin 4) (_ : Fin 1) => ((M i j0 : ℤ) : K)) ?_ ?_
  · rw [Matrix.det_fin_one]; simp only [Matrix.submatrix_apply, Matrix.cons_val_fin_one,
      Matrix.map_apply, Matrix.of_apply]
    intro h0; rw [← zq_iff q] at h0; simp_all
  · intro i j
    have := (zq_iff (K := K) q _).1 (h i j)
    rw [Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_fin_one, Matrix.map_apply,
      Matrix.of_apply, Fin.sum_univ_one]
    push_cast at this
    linear_combination this

theorem rank_two_of (M : ℕ → ℕ → ℤ) (i0 i1 j0 j1 : ℕ) (hi0 : i0 < 4) (hi1 : i1 < 4)
    (hj0 : j0 < 4) (hj1 : j1 < 4) (hd : zq q (del2 M i0 i1 j0 j1) = false)
    (h : ∀ i j : Fin 4, zq q (span2 M M i0 i1 j0 j1 i j) = true) :
    (matK (K := K) M).rank = 2 := by
  refine rank_eq_of_schur _ ![⟨i0, hi0⟩, ⟨i1, hi1⟩] ![⟨j0, hj0⟩, ⟨j1, hj1⟩]
    (Matrix.of fun (i : Fin 4) (a : Fin 2) =>
      ((if a = 0 then M i j0 * M i1 j1 - M i j1 * M i1 j0
        else M i j1 * M i0 j0 - M i j0 * M i0 j1 : ℤ) : K)) ?_ ?_
  · rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.map_apply, Matrix.of_apply]
    intro h0
    have : ((del2 M i0 i1 j0 j1 : ℤ) : K) = 0 := by simp only [del2]; push_cast; exact h0
    rw [← zq_iff q] at this; simp_all
  · intro i j
    have := (zq_iff (K := K) q _).1 (h i j)
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.map_apply, Matrix.of_apply, Fin.sum_univ_two, Fin.isValue, if_true,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, one_ne_zero]
    simp only [span2, del2] at this
    push_cast at this ⊢
    linear_combination this

theorem rank_three_of (M : ℕ → ℕ → ℤ) (i0 i1 i2 j0 j1 j2 : ℕ) (hi0 : i0 < 4) (hi1 : i1 < 4)
    (hi2 : i2 < 4) (hj0 : j0 < 4) (hj1 : j1 < 4) (hj2 : j2 < 4)
    (hd : zq q (del3 M i0 i1 i2 j0 j1 j2) = false)
    (h : ∀ i j : Fin 4, zq q (span3 M M i0 i1 i2 j0 j1 j2 i j) = true) :
    (matK (K := K) M).rank = 3 := by
  let C := cof3 M i0 i1 i2 j0 j1 j2
  let x := fun (i : Fin 4) (b : ℕ) => M i (if b = 0 then j0 else if b = 1 then j1 else j2)
  refine rank_eq_of_schur _ ![⟨i0, hi0⟩, ⟨i1, hi1⟩, ⟨i2, hi2⟩] ![⟨j0, hj0⟩, ⟨j1, hj1⟩, ⟨j2, hj2⟩]
    (Matrix.of fun (i : Fin 4) (a : Fin 3) =>
      ((C a 0 * x i 0 + C a 1 * x i 1 + C a 2 * x i 2 : ℤ) : K)) ?_ ?_
  · rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.map_apply, Matrix.of_apply, Matrix.vecHead, Matrix.vecTail,
      Function.comp, Matrix.cons_val_succ]
    intro h0
    have : ((del3 M i0 i1 i2 j0 j1 j2 : ℤ) : K) = 0 := by
      simp only [del3, cof3]; norm_num; push_cast; linear_combination h0
    rw [← zq_iff q] at this; simp_all
  · intro i j
    have := (zq_iff (K := K) q _).1 (h i j)
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.map_apply, Matrix.of_apply, Fin.sum_univ_three, C, x,
      Matrix.vecHead, Matrix.vecTail, Function.comp, Matrix.cons_val_succ]
    simp only [span3, del3, cof3] at this ⊢
    norm_num at this ⊢
    push_cast at this ⊢
    linear_combination this

/-- A passing rank certificate pins the rank over a field of characteristic `q`. -/
theorem certChk_sound (M : ℕ → ℕ → ℤ) (r i0 i1 i2 j0 j1 j2 : ℕ) (hi0 : i0 < 4)
    (hi1 : i1 < 4) (hi2 : i2 < 4) (hj0 : j0 < 4) (hj1 : j1 < 4) (hj2 : j2 < 4)
    (h : certChk q M r i0 i1 i2 j0 j1 j2 = true) : (matK (K := K) M).rank = r := by
  simp only [certChk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hr, hd⟩, hres⟩ := h
  rcases r with _ | _ | _ | _ | _ | r
  · simp only [residOK] at hres
    exact rank_zero_of q M ((all16_iff _).1 hres)
  · simp only [delta, residOK] at hd hres
    exact rank_one_of q M i0 j0 hi0 hj0 hd ((all16_iff _).1 hres)
  · simp only [delta, residOK] at hd hres
    exact rank_two_of q M i0 i1 j0 j1 hi0 hi1 hj0 hj1 hd ((all16_iff _).1 hres)
  · simp only [delta, residOK] at hd hres
    exact rank_three_of q M i0 i1 i2 j0 j1 j2 hi0 hi1 hi2 hj0 hj1 hj2 hd ((all16_iff _).1 hres)
  · simp only [delta] at hd
    exact rank_four_of q M hd
  · simp only [Nat.ble_eq] at hr; omega

end Rank

/-- An exact certificate with pivot determinant nonzero mod `q` also passes in characteristic
`q`. -/
theorem certChk_of_exact (q : ℕ) (M : ℕ → ℕ → ℤ) (r i0 i1 i2 j0 j1 j2 : ℕ)
    (h : certChk 0 M r i0 i1 i2 j0 j1 j2 = true)
    (hq : zq q (delta M r i0 i1 i2 j0 j1 j2) = false) :
    certChk q M r i0 i1 i2 j0 j1 j2 = true := by
  simp only [certChk, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  refine ⟨⟨h.1.1, hq⟩, ?_⟩
  have h2 := h.2
  unfold residOK at h2 ⊢
  split <;> first
    | rfl
    | exact all16_mono (fun i j hij => zq_of_zq_zero q _ hij) h2

/-! ### From the per-point check to `rk` -/

theorem chkCode_sound {K : Type*} [Field K] (q : ℕ) [CharP K q] (M : ℕ → ℕ → ℤ) (c : ℕ)
    (h : chkCode q M c = true) : (matK (K := K) M).rank = cR c :=
  certChk_sound q M _ _ _ _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) h

theorem code_low (c : ℕ) :
    cR (c % 65536) = cR c ∧ cI0 (c % 65536) = cI0 c ∧ cI1 (c % 65536) = cI1 c ∧
    cI2 (c % 65536) = cI2 c ∧ cJ0 (c % 65536) = cJ0 c ∧ cJ1 (c % 65536) = cJ1 c ∧
    cJ2 (c % 65536) = cJ2 c := by
  simp only [cR, cI0, cI1, cI2, cJ0, cJ1, cJ2, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem factor_map (K : Type) [Field K] (p : Fin 14236) (s : Fin 49) (m : Fin 3) :
    (factor p s m).map (Int.cast : ℤ → K) = matK (mat (pointNat p.val) s.val m.val) := rfl

/-- A passing `matOK` pins `rk ℚ` and `rk (ZMod 3)`. -/
theorem rk_eq_of_matOK (p : Fin 14236) (s : Fin 49) (m : Fin 3)
    (h : matOK (pointNat p.val) (certNat p.val) s.val m.val = true) :
    rk ℚ p s m = rkC false (certNat p.val) s.val m.val ∧
      rk (ZMod 3) p s m = rkC true (certNat p.val) s.val m.val := by
  simp only [matOK, Bool.and_eq_true] at h
  obtain ⟨hQ, hF⟩ := h
  set c := code (certNat p.val) s.val m.val
  set M := mat (pointNat p.val) s.val m.val
  refine ⟨?_, ?_⟩
  · rw [rk, factor_map, rkC]; exact chkCode_sound 0 M c hQ
  · rw [rk, factor_map, rkC, if_pos rfl]
    by_cases hs : cSame c = true
    · rw [if_pos hs] at hF
      have hF' : zq 3 (deltaCode M c) = false := by simpa using hF
      have hc : chkCode 3 M (c % 65536) = true := by
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := code_low c
        simp only [chkCode, h0, h1, h2, h3, h4, h5, h6]
        exact certChk_of_exact 3 M _ _ _ _ _ _ _ hQ hF'
      have := chkCode_sound (K := ZMod 3) 3 M _ hc
      rw [this, codeF, if_pos hs]
    · rw [if_neg hs] at hF
      have := chkCode_sound (K := ZMod 3) 3 M _ hF
      rw [this, codeF, if_neg hs, cF]

theorem matOK_of_ranksOK {N C : ℕ} (h : ranksOK N C = true) (s : ℕ) (hs : s < 49) (m : ℕ)
    (hm : m < 3) : matOK N C s m = true := by
  have := (allBelow_iff 49 _).1 h s hs
  simp only [Bool.and_eq_true] at this
  interval_cases m
  · exact this.1.1
  · exact this.1.2
  · exact this.2

/-! ### Profiles and rank bounds from certified ranks -/

theorem count_full_111 : Multiset.count ((1, 1, 1) : ℕ × ℕ × ℕ) fullProfile = 36 := by decide
theorem count_full_222 : Multiset.count ((2, 2, 2) : ℕ × ℕ × ℕ) fullProfile = 12 := by decide
theorem count_full_444 : Multiset.count ((4, 4, 4) : ℕ × ℕ × ℕ) fullProfile = 1 := by decide
theorem count_full_other (x : ℕ × ℕ × ℕ) (h1 : x ≠ (1, 1, 1)) (h2 : x ≠ (2, 2, 2))
    (h4 : x ≠ (4, 4, 4)) : Multiset.count x fullProfile = 0 := by
  rw [Multiset.count_eq_zero]
  simp only [fullProfile, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton]
  tauto

theorem map_eq_full_iff (g : Fin 49 → ℕ × ℕ × ℕ) :
    (Finset.univ : Finset (Fin 49)).val.map g = fullProfile ↔
      (Finset.univ.filter fun s => g s = (1, 1, 1)).card = 36 ∧
      (Finset.univ.filter fun s => g s = (2, 2, 2)).card = 12 ∧
      (Finset.univ.filter fun s => g s = (4, 4, 4)).card = 1 := by
  have hcount : ∀ x, Multiset.count x ((Finset.univ : Finset (Fin 49)).val.map g) =
      (Finset.univ.filter fun s => g s = x).card := by
    intro x
    rw [Multiset.count_map]
    simp only [Finset.card, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun a _ => eq_comm)
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← hcount, h, count_full_111]
    · rw [← hcount, h, count_full_222]
    · rw [← hcount, h, count_full_444]
  · rintro ⟨h1, h2, h3⟩
    symm
    apply Multiset.eq_of_le_of_card_le
    · rw [Multiset.le_iff_count]
      intro x
      rw [hcount]
      by_cases e1 : x = (1, 1, 1)
      · subst e1; rw [count_full_111, h1]
      by_cases e2 : x = (2, 2, 2)
      · subst e2; rw [count_full_222, h2]
      by_cases e4 : x = (4, 4, 4)
      · subst e4; rw [count_full_444, h3]
      rw [count_full_other x e1 e2 e4]; exact Nat.zero_le _
    · have : Multiset.card fullProfile = 49 := by decide
      rw [this, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
theorem triple_iff (f : Bool) (C : ℕ) (s : ℕ) (r : ℕ) :
    triple f C s r = true ↔ (rkC f C s 0, rkC f C s 1, rkC f C s 2) = (r, r, r) := by
  simp [triple, Prod.ext_iff, and_assoc]

/-- The profile in terms of certified ranks. -/
theorem profile_eq_full_iff (K : Type) [Field K] (p : Fin 14236) (f : Bool) (C : ℕ)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f C s.val m.val) :
    profile K p = fullProfile ↔ fullB f C = true := by
  have hg : ∀ s : Fin 49, (rk K p s 0, rk K p s 1, rk K p s 2) =
      (rkC f C s.val 0, rkC f C s.val 1, rkC f C s.val 2) := by
    intro s; simp only [hrk]; rfl
  rw [profile, map_eq_full_iff]
  simp only [fullB, Bool.and_eq_true, beq_iff_eq, cnt_eq, triple_iff, hg, and_assoc]

theorem exists_mode_iff (K : Type) [Field K] (p : Fin 14236) (f : Bool) (C : ℕ) (k : ℕ)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f C s.val m.val) (s : Fin 49) :
    (∃ m, k < rk K p s m) ↔
      (Nat.blt k (rkC f C s.val 0) || Nat.blt k (rkC f C s.val 1) ||
        Nat.blt k (rkC f C s.val 2)) = true := by
  simp only [hrk, Bool.or_eq_true, Nat.blt_eq]
  constructor
  · rintro ⟨m, hm⟩
    fin_cases m <;> simp_all
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

/-- The rank bounds in terms of certified ranks. -/
theorem rankBounds_iff (K : Type) [Field K] (p : Fin 14236) (f : Bool) (C : ℕ)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f C s.val m.val) :
    RankBounds K p ↔ rbB f C = true := by
  rw [RankBounds, rbB, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq, cnt_eq, cnt_eq]
  simp only [exists_mode_iff K p f C _ hrk]

end Brent.Catalogue