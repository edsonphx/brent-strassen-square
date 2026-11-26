import Brent.Catalogue.Census
import Brent.Catalogue.NegCheck

/-!
# The anchor test fails at points 2445 and 5969 (over `ℚ` and over `ZMod 3`)

A witness vector `n` orthogonal to all rows of the anchor's matrix but not to a row of the
child's defines a linear functional vanishing on one row space and not on the other, so the
containment fails (`not_canAnchor_of_wit`). `negOK` then bounds the number of useful anchors by
five.
-/

namespace Brent.Catalogue

variable {K : Type*} [Field K]

/-- The witness vector. -/
def nvec (w : Wit) : Fin 4 → ℤ := ![w.n0, w.n1, w.n2, w.n3]

theorem not_span_le_of_wit (q : ℕ) [CharP K q] (T A : ℕ → ℕ → ℤ) (w : Wit)
    (hA : ∀ i : Fin 4, zq q (dotRow A i w) = true) (hr : w.row < 4)
    (hT : zq q (dotRow T w.row w) = false) :
    ¬ Submodule.span K (Set.range (rowK (K := K) T)) ≤
      Submodule.span K (Set.range (rowK (K := K) A)) := by
  intro hle
  let L : (Fin 4 → K) →ₗ[K] K := ∑ j : Fin 4, ((nvec w j : ℤ) : K) • LinearMap.proj j
  have hL : ∀ (M : ℕ → ℕ → ℤ) (i : ℕ), L (fun j : Fin 4 => (M i j : K)) = ((dotRow M i w : ℤ) : K) := by
    intro M i
    simp only [L, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, Fin.sum_univ_four, nvec, dotRow]
    simp
    ring
  have hker : Submodule.span K (Set.range (rowK (K := K) A)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show L (fun j : Fin 4 => (A i j : K)) = 0
    rw [hL, ← zq_iff q]
    exact hA i
  have hmem : rowK (K := K) T ⟨w.row, hr⟩ ∈ Submodule.span K (Set.range (rowK (K := K) T)) :=
    Submodule.subset_span ⟨_, rfl⟩
  have h0 := hker (hle hmem)
  rw [LinearMap.mem_ker] at h0
  have h1 : L (fun j : Fin 4 => (T w.row j : K)) = 0 := h0
  rw [hL, ← zq_iff q] at h1
  simp_all

theorem not_canAnchor_of_wit (K : Type) [Field K] (q : ℕ) [CharP K q] (p : Fin 14236) (w : Wit)
    (h : witOK q (pointNat p.val) w = true) (t a : Fin 49) (ht : t.val = w.t) (ha : a.val = w.a) :
    ¬ CanAnchor K p t a := by
  simp only [witOK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hm⟩, hr⟩, hA⟩, hT⟩ := h
  simp only [all4, Bool.and_eq_true] at hA
  have hA' : ∀ i : Fin 4, zq q (dotRow (sideMat (pointNat p.val) w.a w) i w) = true := by
    intro i; fin_cases i
    · exact hA.1.1.1
    · exact hA.1.1.2
    · exact hA.1.2
    · exact hA.2
  intro hcan
  obtain ⟨hrow, hcol⟩ := hcan ⟨w.m, hm⟩
  by_cases hs : (w.side == 0) = true
  · have eT : sideMat (pointNat p.val) w.t w = mat (pointNat p.val) w.t w.m := by
      simp [sideMat, hs]
    have eA : sideMat (pointNat p.val) w.a w = mat (pointNat p.val) w.a w.m := by
      simp [sideMat, hs]
    rw [rowSpace_eq, rowSpace_eq] at hrow
    rw [ht, ha] at hrow
    rw [eT] at hT; rw [eA] at hA'
    exact not_span_le_of_wit q _ _ w hA' hr hT hrow
  · have eT : sideMat (pointNat p.val) w.t w = fun i j => mat (pointNat p.val) w.t w.m j i := by
      simp [sideMat, hs]
    have eA : sideMat (pointNat p.val) w.a w = fun i j => mat (pointNat p.val) w.a w.m j i := by
      simp [sideMat, hs]
    rw [colSpace_eq, colSpace_eq] at hcol
    rw [ht, ha] at hcol
    rw [eT] at hT; rw [eA] at hA'
    exact not_span_le_of_wit q _ _ w hA' hr hT hcol

/-- A passing `negOK` refutes the anchor test. -/
theorem not_anchorTest_of_negOK (K : Type) [Field K] (q : ℕ) [CharP K q] (f : Bool)
    (p : Fin 14236) (ws : List Wit)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f (certNat p.val) s.val m.val)
    (h : negOK f q p.val ws = true) : ¬ AnchorTest K p := by
  classical
  set C := certNat p.val
  simp only [negOK, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq] at h
  obtain ⟨hws, hcnt⟩ := h
  rintro ⟨h6, -⟩
  rw [cnt_eq] at hcnt
  have hsub : (rankTwo K p).filter (Useful K p) ⊆
      Finset.univ.filter fun a : Fin 49 => (triple f C a.val 2 &&
        Nat.ble 6 (cnt 49 fun t => triple f C t 1 && !hasWit ws t a.val)) = true := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨ha2, -, hch⟩ := ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, Nat.ble_eq]
    refine ⟨(forall_mode_iff K p f C hrk a 2).1 (by simpa [rankTwo] using ha2), ?_⟩
    rw [cnt_eq]
    refine le_trans hch (Finset.card_le_card ?_)
    intro t htc
    simp only [children, Finset.mem_filter] at htc
    obtain ⟨ht1, hcan⟩ := htc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      Bool.not_eq_true']
    refine ⟨(forall_mode_iff K p f C hrk t 1).1 (by simpa [rankOne] using ht1), ?_⟩
    by_contra hw
    simp only [Bool.not_eq_false, hasWit, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨w, hw, hwt, hwa⟩ := hw
    exact not_canAnchor_of_wit K q p w (hws w hw) t a hwt.symm hwa.symm hcan
  have := (h6.trans (Finset.card_le_card hsub)).trans hcnt
  omega

end Brent.Catalogue
