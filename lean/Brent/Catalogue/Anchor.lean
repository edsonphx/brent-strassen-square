import Brent.Catalogue.Sound

/-!
# Soundness of the anchor certificate

`anchorOK_sound`: if a point's rank certificates and anchor certificate pass, then
`AnchorTest K p` (with row and column spaces as spans) holds, for any field `K` of
characteristic `q` in which the certificates pass.

Containment of row spaces is certified by identities, not by search:
* the rank-one identity `d • T = T[:, j_T] ⊗ T[i_T, :]` (`d = T i_T j_T ≠ 0`) shows that every row
  of `T` is a multiple of its pivot row;
* `span2 T A … i_T j = 0` for all `j` shows `det D • T[i_T, :] = X₀ • A[i₀, :] + X₁ • A[i₁, :]`,
  with `det D ≠ 0` the pivot minor of `A`.
Columns are handled by the same lemma applied to transposes.
-/

namespace Brent.Catalogue

variable {K : Type*} [Field K]

/-- Row `i` of an `ℕ`-indexed integer matrix, as a vector in `K⁴`. -/
def rowK (T : ℕ → ℕ → ℤ) (i : Fin 4) : Fin 4 → K := fun j => (T i j : K)

theorem span_rows_le (T A : ℕ → ℕ → ℤ) (iT jT i0 i1 j0 j1 : ℕ) (hiT : iT < 4) (hi0 : i0 < 4)
    (hi1 : i1 < 4) (hdT : (T iT jT : K) ≠ 0)
    (hT : ∀ i j : Fin 4, (T iT jT : K) * T i j - T i jT * T iT j = 0)
    (hdA : ((del2 A i0 i1 j0 j1 : ℤ) : K) ≠ 0)
    (hrow : ∀ j : Fin 4, span2 T A i0 i1 j0 j1 iT j = 0) :
    Submodule.span K (Set.range (rowK (K := K) T)) ≤
      Submodule.span K (Set.range (rowK (K := K) A)) := by
  set S := Submodule.span K (Set.range (rowK (K := K) A))
  have hA : ∀ (i : ℕ) (hi : i < 4), rowK (K := K) A ⟨i, hi⟩ ∈ S :=
    fun i hi => Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  set δ : K := ((del2 A i0 i1 j0 j1 : ℤ) : K)
  set X0 : K := (T iT j0 : K) * A i1 j1 - (T iT j1 : K) * A i1 j0
  set X1 : K := (T iT j1 : K) * A i0 j0 - (T iT j0 : K) * A i0 j1
  have hpiv0 : δ • rowK (K := K) T ⟨iT, hiT⟩ =
      X0 • rowK (K := K) A ⟨i0, hi0⟩ + X1 • rowK (K := K) A ⟨i1, hi1⟩ := by
    funext j
    have h := congrArg (Int.cast : ℤ → K) (hrow j)
    simp only [span2, del2] at h
    push_cast at h
    simp only [rowK, Pi.smul_apply, Pi.add_apply, smul_eq_mul, X0, X1, δ, del2]
    push_cast
    linear_combination h
  have hpiv : rowK (K := K) T ⟨iT, hiT⟩ =
      δ⁻¹ • (X0 • rowK (K := K) A ⟨i0, hi0⟩ + X1 • rowK (K := K) A ⟨i1, hi1⟩) := by
    rw [← hpiv0, smul_smul, inv_mul_cancel₀ hdA, one_smul]
  have hpivS : rowK (K := K) T ⟨iT, hiT⟩ ∈ S := by
    rw [hpiv]
    exact S.smul_mem _ (S.add_mem (S.smul_mem _ (hA i0 hi0)) (S.smul_mem _ (hA i1 hi1)))
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hi0' : (T iT jT : K) • rowK (K := K) T i = (T i jT : K) • rowK (K := K) T ⟨iT, hiT⟩ := by
    funext j
    have h := hT i j
    simp only [rowK, Pi.smul_apply, smul_eq_mul]
    linear_combination h
  have hi : rowK (K := K) T i = (T iT jT : K)⁻¹ • ((T i jT : K) • rowK (K := K) T ⟨iT, hiT⟩) := by
    rw [← hi0', smul_smul, inv_mul_cancel₀ hdT, one_smul]
  rw [SetLike.mem_coe, hi]
  exact S.smul_mem _ (S.smul_mem _ hpivS)

/-- The rank-one pivot facts from a passing certificate. -/
theorem pivot_one (q : ℕ) [CharP K q] (M : ℕ → ℕ → ℤ) (c : ℕ) (hc : chkCode q M c = true)
    (hr : cR c = 1) :
    (M (cI0 c) (cJ0 c) : K) ≠ 0 ∧
      ∀ i j : Fin 4, (M (cI0 c) (cJ0 c) : K) * M i j - M i (cJ0 c) * M (cI0 c) j = 0 := by
  simp only [chkCode, certChk, hr, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨-, hd⟩, hres⟩ := hc
  simp only [delta, residOK] at hd hres
  refine ⟨?_, fun i j => ?_⟩
  · intro h0; rw [← zq_iff q] at h0; simp_all
  · have := (zq_iff (K := K) q _).1 ((all16_iff _).1 hres i j)
    push_cast at this; exact this

/-- The rank-two pivot fact from a passing certificate. -/
theorem pivot_two (q : ℕ) [CharP K q] (M : ℕ → ℕ → ℤ) (c : ℕ) (hc : chkCode q M c = true)
    (hr : cR c = 2) : ((del2 M (cI0 c) (cI1 c) (cJ0 c) (cJ1 c) : ℤ) : K) ≠ 0 := by
  simp only [chkCode, certChk, hr, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨-, hd⟩, -⟩ := hc
  simp only [delta] at hd
  intro h0; rw [← zq_iff q] at h0; simp_all

theorem rowSpace_eq (K : Type) [Field K] (p : Fin 14236) (s : Fin 49) (m : Fin 3) :
    rowSpace K (factor p s m) =
      Submodule.span K (Set.range (rowK (K := K) (mat (pointNat p.val) s.val m.val))) := rfl

theorem colSpace_eq (K : Type) [Field K] (p : Fin 14236) (s : Fin 49) (m : Fin 3) :
    colSpace K (factor p s m) =
      Submodule.span K (Set.range (rowK (K := K)
        (fun i j => mat (pointNat p.val) s.val m.val j i))) := rfl

theorem compat_mode (N C t a m : ℕ) (hm : m < 3) (h : compat N C t a = true) :
    (rowIn (mat N t m) (mat N a m) (cI0 (code C t m)) (cI0 (code C a m)) (cI1 (code C a m))
        (cJ0 (code C a m)) (cJ1 (code C a m)) &&
      rowIn (fun i j => mat N t m j i) (fun i j => mat N a m j i) (cJ0 (code C t m))
        (cJ0 (code C a m)) (cJ1 (code C a m)) (cI0 (code C a m)) (cI1 (code C a m))) = true := by
  simp only [compat, all3, Bool.and_eq_true] at h
  simp only [Bool.and_eq_true]
  interval_cases m
  · exact h.1.1
  · exact h.1.2
  · exact h.2

/-- A passing `compat` check gives `CanAnchor`, given the rank certificates of both summands. -/
theorem canAnchor_of_compat (K : Type) [Field K] (q : ℕ) [CharP K q] (p : Fin 14236)
    (t a : Fin 49)
    (hchk : ∀ m : Fin 3, chkCode q (mat (pointNat p.val) t.val m.val) (code (certNat p.val) t.val m.val) = true ∧
      chkCode q (mat (pointNat p.val) a.val m.val) (code (certNat p.val) a.val m.val) = true)
    (hrt : ∀ m : Fin 3, cR (code (certNat p.val) t.val m.val) = 1)
    (hra : ∀ m : Fin 3, cR (code (certNat p.val) a.val m.val) = 2)
    (h : compat (pointNat p.val) (certNat p.val) t.val a.val = true) : CanAnchor K p t a := by
  intro m
  set N := pointNat p.val
  set C := certNat p.val
  set ct := code C t.val m.val
  set ca := code C a.val m.val
  set T := mat N t.val m.val
  set A := mat N a.val m.val
  have hm := compat_mode N C t.val a.val m.val m.isLt h
  simp only [Bool.and_eq_true, rowIn, all4] at hm
  obtain ⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩⟩ := hm
  obtain ⟨hdT, hT⟩ := pivot_one (K := K) q T ct (hchk m).1 (hrt m)
  have hdA := pivot_two (K := K) q A ca (hchk m).2 (hra m)
  have lt4 : ∀ x : ℕ, x % 4 < 4 := fun x => Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [rowSpace_eq, rowSpace_eq]
    refine span_rows_le T A (cI0 ct) (cJ0 ct) (cI0 ca) (cI1 ca) (cJ0 ca) (cJ1 ca)
      (lt4 _) (lt4 _) (lt4 _) hdT hT hdA ?_
    intro j; fin_cases j
    · simpa using r0
    · simpa using r1
    · simpa using r2
    · simpa using r3
  · rw [colSpace_eq, colSpace_eq]
    refine span_rows_le (fun i j => T j i) (fun i j => A j i) (cJ0 ct) (cI0 ct) (cJ0 ca)
      (cJ1 ca) (cI0 ca) (cI1 ca) (lt4 _) (lt4 _) (lt4 _) hdT (fun i j => ?_) ?_ ?_
    · have := hT j i; linear_combination this
    · intro h0; apply hdA; simp only [del2] at h0 ⊢; push_cast at h0 ⊢; linear_combination h0
    · intro j; fin_cases j
      · simpa using c0
      · simpa using c1
      · simpa using c2
      · simpa using c3

end Brent.Catalogue
