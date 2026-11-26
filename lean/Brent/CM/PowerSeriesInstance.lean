import Brent.CM.Lemma41Gen
import Brent.CM.RegularCoprime
import Brent.Formal.PowerSeriesAdic
import Brent.Formal.PowerSeriesDimension
import Brent.Formal.PowerSeriesNoetherian

/-!
# Lemma 4.1 for `k⟦x, y⟧` and the 54 quadrics (roadmap lines 457–482, the instance)

DRAFT, NOT YET COMPILED.

`A = 𝔽₃⟦x₀..x₅₃, y₀..y₅₃⟧`, `m = (x, y)`, `fᵢ = qᵢ` (degree `dᵢ = 2`). The initial form of
`qᵢ` is `qᵢ` itself (it is a quadratic form), so the hypothesis `hreg` of Lemma 4.1 is the
regularity of the `qᵢ` in the graded ring `𝔽₃[x, y] = gr_m A`, which is `Brent.CM.q_regular`.

* `Hs N : A → 𝔽₃[x, y]`, the homogeneous component of degree `N` (`coeff_Hs`);
* `sub_Hs_mem`, `Hs_eq_zero`: `x ∈ mᴺ ⇒ x − Hs N x ∈ mᴺ⁺¹`, and `Hs N` kills `mᴺ⁺¹`;
* `Hs_mul`: `Hs (n + 2) (P z) = P · Hs n z` for a quadratic form `P` and `z ∈ mⁿ`;
* `Hs_relI`: the degree-`(n + 2)` component of an element of `relI i (n + 2)` lies in
  `(q_j : j < i)`;
* `hreg_q`: **the hypothesis `hreg` of Lemma 4.1 for the `qᵢ`**;
* `lemma41_q`: **`dim A ⧸ I ≤ 108 − 54 = 54` for every ideal `I` containing the `qᵢ`.**

To pad the sequence beyond `i = 54` we use `f i = 1`, `d i = 0`, for which `hreg` is trivial;
Lemma 4.1 only uses `f j ∈ I` for `j < s = 54`.
-/

namespace Brent.CM.PSInstance

open IsLocalRing Brent.Groebner.Paper

abbrev σ0 := Fin 54 ⊕ Fin 54

/-- `A = 𝔽₃⟦x, y⟧`. -/
abbrev Ak := MvPowerSeries σ0 (ZMod 3)

/-- `𝔽₃[x, y]`. -/
abbrev Pk := MvPolynomial σ0 (ZMod 3)

local notation "𝔪" => maximalIdeal Ak

/-! ### The maximal ideal -/

theorem maximalIdeal_eq : 𝔪 = Brent.Formal.mX σ0 (ZMod 3) := by
  refine le_antisymm (Brent.Formal.maximalIdeal_le_span_X (σ := σ0) (k := ZMod 3)) ?_
  rw [Brent.Formal.mX, Ideal.span_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem mem_pow_iff (N : ℕ) (x : Ak) : x ∈ 𝔪 ^ N ↔ Brent.Formal.LowZero N x := by
  rw [maximalIdeal_eq]
  exact Brent.Formal.mem_pow_iff_lowZero N x

/-- A homogeneous polynomial of degree `M` lies in `m^M`. -/
theorem homog_coe_mem {P : Pk} {M : ℕ} (hP : P.IsHomogeneous M) : (P : Ak) ∈ 𝔪 ^ M := by
  rw [mem_pow_iff]
  intro e he
  rw [MvPolynomial.coeff_coe]
  exact hP.coeff_eq_zero (by omega)

/-! ### Homogeneous components of power series -/

/-- The homogeneous component of degree `N` of a power series. -/
noncomputable def Hs (N : ℕ) : Ak →ₗ[ZMod 3] Pk :=
  (MvPolynomial.homogeneousComponent N).comp (MvPowerSeries.trunc' (ZMod 3) (Brent.Formal.box (N + 1)))

theorem coeff_Hs (N : ℕ) (x : Ak) (e : σ0 →₀ ℕ) :
    MvPolynomial.coeff e (Hs N x) = if e.degree = N then MvPowerSeries.coeff e x else 0 := by
  simp only [Hs, LinearMap.comp_apply, MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h
  · rw [MvPowerSeries.coeff_trunc', if_pos (Brent.Formal.le_box (by omega))]
  · rfl

theorem Hs_isHomog (N : ℕ) (x : Ak) : (Hs N x).IsHomogeneous N := by
  simp only [Hs, LinearMap.comp_apply]
  exact MvPolynomial.homogeneousComponent_isHomogeneous N _

theorem Hs_coe (N : ℕ) (P : Pk) : Hs N (P : Ak) = MvPolynomial.homogeneousComponent N P := by
  ext e
  rw [coeff_Hs, MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_coe]

theorem Hs_eq_zero {N : ℕ} {x : Ak} (hx : x ∈ 𝔪 ^ (N + 1)) : Hs N x = 0 := by
  ext e
  rw [coeff_Hs, MvPolynomial.coeff_zero]
  split_ifs with h
  · exact (mem_pow_iff _ _).mp hx e (by omega)
  · rfl

theorem sub_Hs_mem {N : ℕ} {x : Ak} (hx : x ∈ 𝔪 ^ N) : x - (Hs N x : Ak) ∈ 𝔪 ^ (N + 1) := by
  rw [mem_pow_iff]
  intro e he
  rw [map_sub, MvPolynomial.coeff_coe, coeff_Hs]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    exact (mem_pow_iff _ _).mp hx e (by omega)

/-- **`Hs (n + 2) (P z) = P · Hs n z`** for a quadratic form `P` and `z ∈ mⁿ`. -/
theorem Hs_mul {P : Pk} (hP : P.IsHomogeneous 2) {n : ℕ} {z : Ak} (hz : z ∈ 𝔪 ^ n) :
    Hs (n + 2) ((P : Ak) * z) = P * Hs n z := by
  have hz' := sub_Hs_mem hz
  have hsplit : (P : Ak) * z = ((P * Hs n z : Pk) : Ak) + (P : Ak) * (z - (Hs n z : Ak)) := by
    rw [MvPolynomial.coe_mul]
    ring
  have hhigh : (P : Ak) * (z - (Hs n z : Ak)) ∈ 𝔪 ^ (n + 2 + 1) := by
    have := Ideal.mul_mem_mul (homog_coe_mem hP) hz'
    rwa [← pow_add, show 2 + (n + 1) = n + 2 + 1 by omega] at this
  rw [hsplit, map_add, Hs_coe, Hs_eq_zero hhigh, add_zero,
    MvPolynomial.homogeneousComponent_of_mem (hP.mul (Hs_isHomog n z)), if_pos (by omega)]

/-- Multiplying by a quadratic form shifts homogeneous components by two. -/
theorem hc_mul {P : Pk} (hP : P.IsHomogeneous 2) (c : Pk) (N : ℕ) :
    MvPolynomial.homogeneousComponent N (c * P) =
      if 2 ≤ N then MvPolynomial.homogeneousComponent (N - 2) c * P else 0 := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent c]
  rw [Finset.sum_mul, map_sum]
  have hterm : ∀ m, MvPolynomial.homogeneousComponent N
      (MvPolynomial.homogeneousComponent m c * P) =
      if N = m + 2 then MvPolynomial.homogeneousComponent m c * P else 0 := fun m =>
    MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.homogeneousComponent_isHomogeneous m c).mul hP)
  simp_rw [hterm]
  split_ifs with hN
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega]
    simp_rw [Nat.add_right_cancel_iff]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · rw [MvPolynomial.homogeneousComponent_eq_zero, zero_mul]
      rw [Finset.mem_range] at hk
      omega
  · exact Finset.sum_eq_zero fun m _ => if_neg (by omega)

/-! ### The quadrics -/

theorem degree_e (i j : Fin 54) : (e i j).degree = 2 := by
  rw [e, map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- The `qᵢ` are quadratic forms. -/
theorem q_homog (l : Fin 54) : (q l).IsHomogeneous 2 := by
  rw [q_eq]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
  exact MvPolynomial.isHomogeneous_monomial _ (degree_e i j)

/-- The sequence `f` of Lemma 4.1: `qᵢ` for `i < 54`, then `1`. -/
noncomputable def fq (i : ℕ) : Ak := if h : i < 54 then ((q ⟨i, h⟩ : Pk) : Ak) else 1

/-- Their degrees: `2`, then `0`. -/
def dq (i : ℕ) : ℕ := if i < 54 then 2 else 0

theorem fq_of_lt {i : ℕ} (h : i < 54) : fq i = ((q ⟨i, h⟩ : Pk) : Ak) := dif_pos h

theorem dq_of_lt {i : ℕ} (h : i < 54) : dq i = 2 := if_pos h

theorem hf_q (i : ℕ) : fq i ∈ 𝔪 ^ dq i := by
  by_cases h : i < 54
  · rw [fq_of_lt h, dq_of_lt h]
    exact homog_coe_mem (q_homog _)
  · rw [fq, dif_neg h, dq, if_neg h, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/-- The polynomial ideal `(q_j : j < i)`. -/
noncomputable def Jp (i : ℕ) : Ideal Pk :=
  Ideal.span (Set.range fun j : {j : Fin 54 // (j : ℕ) < i} => q j)

theorem Jp_mono (i : ℕ) : Jp i ≤ Jp (i + 1) := by
  refine Ideal.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j.1, by have := j.2; omega⟩, rfl⟩

/-- **The degree-`(n + 2)` component of `relI i (n + 2)` lies in `(q_j : j < i)`.** -/
theorem Hs_relI : ∀ i, i ≤ 54 → ∀ (n : ℕ) (x : Ak), x ∈ relI fq dq i (n + 2) →
    Hs (n + 2) x ∈ Jp i
  | 0, _, n, x, hx => by
    have hx' : x ∈ 𝔪 ^ (n + 2 + 1) := hx
    rw [Hs_eq_zero hx']
    exact zero_mem _
  | i + 1, hi, n, x, hx => by
    have hi' : i < 54 := by omega
    have hx' : x ∈ relI fq dq i (n + 2) ⊔
        (if dq i ≤ n + 2 then Ideal.span {fq i} * 𝔪 ^ (n + 2 - dq i) else ⊥) := hx
    rw [dq_of_lt hi', if_pos (by omega), show n + 2 - 2 = n by omega, fq_of_lt hi'] at hx'
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.mp hw
    rw [map_add]
    refine add_mem (Jp_mono i (Hs_relI i (by omega) n y hy)) ?_
    rw [Hs_mul (q_homog _) hz]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨⟨⟨i, hi'⟩, by simp⟩, rfl⟩)

/-- A single generator term of `relI`. -/
theorem term_mem {f : ℕ → Ak} {d : ℕ → ℕ} {i j n : ℕ} (hj : j < i) (hd : d j ≤ n) {z : Ak}
    (hz : z ∈ 𝔪 ^ (n - d j)) : f j * z ∈ relI f d i n := by
  refine relI_mono (show j + 1 ≤ i by omega) n ?_
  show f j * z ∈ relI f d j n ⊔ (if d j ≤ n then Ideal.span {f j} * 𝔪 ^ (n - d j) else ⊥)
  refine Submodule.mem_sup_right ?_
  rw [if_pos hd]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz

/-- **The hypothesis `hreg` of Lemma 4.1 for the quadrics**: the initial forms `qᵢ` form a
regular sequence in `gr_m A = 𝔽₃[x, y]` (`q_regular`). -/
theorem hreg_q (i n : ℕ) (a : Ak) (ha : a ∈ 𝔪 ^ n)
    (h : fq i * a ∈ relI fq dq i (n + dq i)) : a ∈ relI fq dq i n := by
  by_cases hi : i < 54
  swap
  · rw [fq, dif_neg hi, one_mul, dq, if_neg hi, add_zero] at h
    exact h
  rw [fq_of_lt hi, dq_of_lt hi] at h
  have hJ := Hs_relI i hi.le n _ h
  rw [Hs_mul (q_homog _) ha] at hJ
  have hA0 : Hs n a ∈ Ideal.span (Set.range fun j : {j : Fin 54 // j < ⟨i, hi⟩} => q j) :=
    Brent.CM.q_regular ⟨i, hi⟩ hJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hA0
  have hsplit : a = (Hs n a : Ak) + (a - (Hs n a : Ak)) := by ring
  rw [hsplit]
  refine add_mem ?_ (pow_succ_le_relI i n (sub_Hs_mem ha))
  have hhc : Hs n a = MvPolynomial.homogeneousComponent n (Hs n a) := by
    rw [MvPolynomial.homogeneousComponent_of_mem (Hs_isHomog n a), if_pos rfl]
  rw [hhc, ← hc, map_sum, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, hc_mul (q_homog _)]
  split_ifs with hn
  · rw [MvPolynomial.coe_mul, mul_comm]
    have hj : ((j : Fin 54) : ℕ) < i := j.2
    have hfj : fq ((j : Fin 54) : ℕ) = ((q j : Pk) : Ak) := by
      rw [fq_of_lt (j : Fin 54).2]
    have hdj : dq ((j : Fin 54) : ℕ) = 2 := dq_of_lt (j : Fin 54).2
    have hz : ((MvPolynomial.homogeneousComponent (n - 2) (c j) : Pk) : Ak) ∈
        𝔪 ^ (n - dq ((j : Fin 54) : ℕ)) := by
      rw [hdj]
      exact homog_coe_mem (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
    have := term_mem (f := fq) (d := dq) hj (by rw [hdj]; exact hn) hz
    rwa [hfj] at this
  · rw [MvPolynomial.coe_zero]
    exact zero_mem _

/-! ### The generators of `m` and Lemma 4.1 -/

/-- An enumeration of the 108 variables. -/
noncomputable def eσ : Fin 108 ≃ σ0 :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_sum])).symm

/-- The 108 variables, generating `m`. -/
noncomputable def gens : Fin (107 + 1) → Ak := fun t => MvPowerSeries.X (eσ t)

theorem span_gens : Ideal.span (Set.range gens) = 𝔪 := by
  rw [maximalIdeal_eq, Brent.Formal.mX]
  congr 1
  exact eσ.surjective.range_comp _

/-- **Lemma 4.1 for the quadrics.** Every ideal of `𝔽₃⟦x, y⟧` containing `q₀, …, q₅₃` has
`dim A ⧸ I ≤ 108 − 54 = 54`. -/
theorem lemma41_q {I : Ideal Ak} (hI : ∀ l : Fin 54, ((q l : Pk) : Ak) ∈ I) :
    ringKrullDim (Ak ⧸ I) ≤ ((107 + 1 - 54 : ℕ) : WithBot ℕ∞) :=
  lemma41_of_span (s := 54) gens span_gens fq dq hf_q hreg_q fun j hj => by
    rw [fq_of_lt hj]
    exact hI _

end Brent.CM.PSInstance
