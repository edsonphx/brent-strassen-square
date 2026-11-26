import Brent.CM.HilbertSamuelPoly
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Lemma 4.1 (lines 440–466): the dimension bound from regular initial forms

DRAFT, NOT YET COMPILED.

Paper: *Let `A = k[[z₁, …, z_N]]` with maximal ideal `m`, and let `I ⊆ A`. For a nonzero
`f ∈ A`, write `f*` for its lowest nonzero homogeneous part. If `I` contains `f₁, …, f_s` with
`f₁*, …, f_s*` a regular sequence, then `dim (A/I) ≤ N − s`.*

The proof follows the paper. Work in a Noetherian local ring `(A, m)` whose associated graded
ring has the Hilbert function of `k[z₁, …, z_N]` (order `N`, hypothesis `hA`).

* `R i n = mⁿ ⧸ (m^(n+1) + Σ_{j<i} fⱼ m^(n − dⱼ))` is the degree-`n` piece of
  `gr_m A ⧸ (f₁*, …, f_i*)`, with `fⱼ ∈ m^(dⱼ)` and `fⱼ*` its class of degree `dⱼ`.
* `hreg` says that `f_i*` is a nonzerodivisor on `gr_m A ⧸ (f₁*, …, f_{i−1}*)`: the `f*` form a
  regular sequence.
* `length_R_succ`: the exact sequence `0 → R i n →f_i*→ R i (n + dᵢ) → R (i+1) (n + dᵢ) → 0`.
* `orderLE_R`: the Hilbert function of `R i` has order `≤ N − i` (the source has dimension
  `N − s`).
* `length_gr_le`: **the graded surjection** `R s n ↠ gr_n (A ⧸ I)` (the kernel of
  `gr A → gr (A/I)` contains the initial forms of elements of `I`).
* `lemma41_chain`, `lemma41`: **`dim (A ⧸ I) ≤ N − s`** (Hilbert–Samuel dimension theorem,
  `Brent.CM.chain_bound`).
-/

namespace Brent.CM

open IsLocalRing

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

local notation "𝔪" => maximalIdeal A

section Rel

variable (f : ℕ → A) (d : ℕ → ℕ)

/-- `m^(n+1) + Σ_{j<i} fⱼ m^(n − dⱼ)` (only the `j` with `dⱼ ≤ n`). -/
noncomputable def relI : ℕ → ℕ → Ideal A
  | 0, n => 𝔪 ^ (n + 1)
  | i + 1, n => relI i n ⊔ (if d i ≤ n then Ideal.span {f i} * 𝔪 ^ (n - d i) else ⊥)

variable {f d}

theorem relI_mono_succ (i n : ℕ) : relI f d i n ≤ relI f d (i + 1) n := le_sup_left

theorem relI_mono {i i' : ℕ} (h : i ≤ i') (n : ℕ) : relI f d i n ≤ relI f d i' n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (relI_mono_succ _ n)

theorem pow_succ_le_relI (i n : ℕ) : 𝔪 ^ (n + 1) ≤ relI f d i n :=
  relI_mono (Nat.zero_le i) n

variable (hf : ∀ i, f i ∈ 𝔪 ^ d i)

include hf in
theorem relI_le_pow (i n : ℕ) : relI f d i n ≤ 𝔪 ^ n := by
  induction i with
  | zero => exact Ideal.pow_le_pow_right (Nat.le_succ n)
  | succ i ih =>
    refine sup_le ih ?_
    split_ifs with h
    · calc Ideal.span {f i} * 𝔪 ^ (n - d i) ≤ 𝔪 ^ d i * 𝔪 ^ (n - d i) :=
            Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr (hf i))
        _ = 𝔪 ^ n := by rw [← pow_add, Nat.add_sub_of_le h]
    · exact bot_le

include hf in
theorem relI_le_of_mem {I : Ideal A} (hI : ∀ j, f j ∈ I) (i n : ℕ) :
    relI f d i n ≤ I ⊔ 𝔪 ^ (n + 1) := by
  induction i with
  | zero => exact le_sup_right
  | succ i ih =>
    refine sup_le ih ?_
    split_ifs
    · exact le_sup_of_le_left (Ideal.mul_le_right.trans
        ((Ideal.span_singleton_le_iff_mem _).mpr (hI i)))
    · exact bot_le

include hf in
/-- `f_i · relI i n ⊆ relI i (n + dᵢ)`. -/
theorem mul_relI_le (i k n : ℕ) {b : A} (hb : b ∈ relI f d i n) :
    f k * b ∈ relI f d i (n + d k) := by
  induction i generalizing b with
  | zero =>
    have h : f k * b ∈ 𝔪 ^ d k * 𝔪 ^ (n + 1) := Ideal.mul_mem_mul (hf k) hb
    rw [← pow_add, show d k + (n + 1) = n + d k + 1 by omega] at h
    exact h
  | succ i ih =>
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
    rw [mul_add]
    refine Submodule.add_mem_sup (ih hb₁) ?_
    by_cases h : d i ≤ n
    · rw [if_pos h] at hb₂
      rw [if_pos (by omega)]
      obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.mp hb₂
      refine Ideal.mem_span_singleton_mul.mpr ⟨f k * c, ?_, by ring⟩
      have h3 := Ideal.mul_mem_mul (hf k) hc
      rw [← pow_add, show d k + (n - d i) = n + d k - d i by omega] at h3
      exact h3
    · rw [if_neg h, Submodule.mem_bot] at hb₂
      rw [hb₂, mul_zero]
      exact Submodule.zero_mem _

end Rel

section Pieces

variable (f : ℕ → A) (d : ℕ → ℕ) (hf : ∀ i, f i ∈ 𝔪 ^ d i)

/-- `relI i n` inside `mⁿ`. -/
abbrev relSub (i n : ℕ) : Submodule A (𝔪 ^ n : Ideal A) :=
  (relI f d i n).comap (𝔪 ^ n : Ideal A).subtype

/-- The degree-`n` piece of `gr_m A ⧸ (f₁*, …, f_i*)`. -/
abbrev RPiece (i n : ℕ) : Type u := (𝔪 ^ n : Ideal A) ⧸ relSub f d i n

/-- Its Hilbert function. -/
noncomputable def hilbR (i : ℕ) : ℕ → ℤ := fun n => lenZ (A := A) (RPiece f d i n)

include hf in
/-- Multiplication by `f_i`, `mⁿ → m^(n + dᵢ)`. -/
noncomputable def mulPow (k n : ℕ) : (𝔪 ^ n : Ideal A) →ₗ[A] (𝔪 ^ (n + d k) : Ideal A) :=
  (LinearMap.mulLeft A (f k)).restrict fun b hb => by
    have h := Ideal.mul_mem_mul (hf k) hb
    rw [← pow_add, add_comm] at h
    exact h

include hf in
/-- Multiplication by `f_i*` on the pieces. -/
noncomputable def mulR (i k n : ℕ) : RPiece f d i n →ₗ[A] RPiece f d i (n + d k) :=
  Submodule.mapQ _ _ (mulPow f d hf k n) fun b hb => by
    show f k * (b : A) ∈ relI f d i (n + d k)
    exact mul_relI_le hf i k n hb

/-- The quotient map `R i n → R (i + 1) n`. -/
noncomputable def projR (i n : ℕ) : RPiece f d i n →ₗ[A] RPiece f d (i + 1) n :=
  Submodule.factor (Submodule.comap_mono (relI_mono_succ i n))

variable (hreg : ∀ (i n : ℕ) (a : A), a ∈ 𝔪 ^ n → f i * a ∈ relI f d i (n + d i) →
  a ∈ relI f d i n)

include hreg in
theorem mulR_injective (i n : ℕ) : Function.Injective (mulR f d hf i i n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H b =>
    rw [LinearMap.mem_ker, mulR, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hreg i n b b.2 hq

theorem mulR_exact (i n : ℕ) :
    Function.Exact (mulR f d hf i i n) (projR f d i (n + d i)) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H a =>
    rw [projR, Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
    show (a : A) ∈ relI f d (i + 1) (n + d i) ↔ _
    rw [relI, if_pos (by omega), Nat.add_sub_cancel]
    constructor
    · intro ha
      obtain ⟨r, hr, c, hc, hrc⟩ := Submodule.mem_sup.mp ha
      obtain ⟨b, hb, hbc⟩ := Ideal.mem_span_singleton_mul.mp hc
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      rw [mulR, Submodule.mapQ_apply, Submodule.Quotient.eq]
      show f i * b - (a : A) ∈ relI f d i (n + d i)
      have : f i * b - (a : A) = -r := by rw [← hrc, hbc]; ring
      rw [this]
      exact Submodule.neg_mem _ hr
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with
      | H b =>
        rw [mulR, Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
        have h1 : f i * (b : A) - (a : A) ∈ relI f d i (n + d i) := hq
        have h2 : f i * (b : A) ∈ Ideal.span {f i} * 𝔪 ^ n :=
          Ideal.mem_span_singleton_mul.mpr ⟨b, b.2, rfl⟩
        have : (a : A) = f i * b - (f i * b - a) := by ring
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)

/-- `R i n ↪ A ⧸ m^(n+1)`-type bound: `R i n` is a quotient of `R 0 n`. -/
noncomputable def incl0 (n : ℕ) : RPiece f d 0 n →ₗ[A] A ⧸ 𝔪 ^ (n + 1) :=
  Submodule.mapQ _ _ (𝔪 ^ n : Ideal A).subtype le_rfl

theorem incl0_injective (n : ℕ) : Function.Injective (incl0 f d n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H b =>
    rw [LinearMap.mem_ker, incl0, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq

theorem length_R_ne_top (i n : ℕ) : Module.length A (RPiece f d i n) ≠ ⊤ := by
  have h0 : Module.length A (RPiece f d 0 n) ≠ ⊤ :=
    ne_top_of_le_ne_top (length_quot_pow_ne_top (n + 1))
      (Module.length_le_of_injective _ (incl0_injective f d n))
  exact ne_top_of_le_ne_top h0 (Module.length_le_of_surjective
    (Submodule.factor (Submodule.comap_mono (relI_mono (Nat.zero_le i) n)))
    (Submodule.factor_surjective _))

include hf hreg in
/-- **The exact sequence** `0 → R i n → R i (n + dᵢ) → R (i+1) (n + dᵢ) → 0`. -/
theorem hilbR_succ (i n : ℕ) :
    hilbR f d (i + 1) (n + d i) = hilbR f d i (n + d i) - hilbR f d i n := by
  have e := Module.length_eq_add_of_exact (mulR f d hf i i n) (projR f d i (n + d i))
    (mulR_injective f d hf hreg i n) (Submodule.factor_surjective _) (mulR_exact f d hf i n)
  unfold hilbR lenZ
  rw [e, ENat.toNat_add (length_R_ne_top f d i n) (length_R_ne_top f d (i + 1) (n + d i))]
  push_cast
  ring

include hf hreg in
/-- **The Hilbert function of `gr A ⧸ (f₁*, …, f_i*)` has order `≤ N − i`.** -/
theorem orderLE_R {N : ℕ} (hA : OrderLE (hilbR f d 0) N) (i : ℕ) :
    OrderLE (hilbR f d i) (N - i) := by
  induction i with
  | zero => simpa using hA
  | succ i ih =>
    rcases Nat.lt_or_ge i N with hiN | hiN
    · obtain ⟨e, he⟩ : ∃ e, N - i = e + 1 := ⟨N - i - 1, by omega⟩
      rw [he] at ih
      have h := orderLE_of_sub_shift (n₁ := 0) (d := d i)
        (fun n _ => hilbR_succ f d hf hreg i n) ih
      rwa [show N - (i + 1) = e by omega]
    · rw [show N - i = 0 by omega] at ih
      rw [show N - (i + 1) = 0 by omega]
      obtain ⟨n₀, hn₀⟩ := ih
      refine ⟨n₀ + d i, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + d i := ⟨n - d i, by omega⟩
      show hilbR f d (i + 1) (m + d i) = 0
      rw [hilbR_succ f d hf hreg i m]
      have h1 : hilbR f d i (m + d i) = 0 := hn₀ _ (by omega)
      have h2 : hilbR f d i m = 0 := hn₀ _ (by omega)
      rw [h1, h2, sub_zero]

/-! ### The graded surjection onto `gr (A ⧸ I)` -/

variable {I : Ideal A} (hI : ∀ j, f j ∈ I)

include hf hI in
/-- `R s n ↠ gr_n (A ⧸ I)`. -/
noncomputable def toGr (s n : ℕ) : RPiece f d s n →ₗ[A] grFam I n :=
  Submodule.mapQ _ _
    ((Submodule.inclusion (le_sup_right : (𝔪 ^ n : Ideal A) ≤ I ⊔ 𝔪 ^ n)))
    fun b hb => by
      show (b : A) ∈ I ⊔ 𝔪 ^ (n + 1)
      exact relI_le_of_mem hf hI s n hb

theorem toGr_surjective (s n : ℕ) : Function.Surjective (toGr f d hf hI s n) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H b =>
    obtain ⟨j, hj, c, hc, hjc⟩ := Submodule.mem_sup.mp b.2
    refine ⟨Submodule.Quotient.mk ⟨c, hc⟩, ?_⟩
    rw [toGr, Submodule.mapQ_apply, Submodule.Quotient.eq]
    show c - (b : A) ∈ I ⊔ 𝔪 ^ (n + 1)
    have : c - (b : A) = -j := by rw [← hjc]; ring
    rw [this]
    exact Submodule.neg_mem _ (Submodule.mem_sup_left hj)

include hf hI in
theorem length_gr_le (s n : ℕ) :
    lenZ (A := A) (grFam I n) ≤ hilbR f d s n := by
  have h := Module.length_le_of_surjective _ (toGr_surjective f d hf hI s n)
  unfold hilbR lenZ
  exact_mod_cast toNat_le_toNat' (length_R_ne_top f d s n) h

end Pieces

/-! ### Lemma 4.1 -/

variable (f : ℕ → A) (d : ℕ → ℕ) (hf : ∀ i, f i ∈ 𝔪 ^ d i)
  (hreg : ∀ (i n : ℕ) (a : A), a ∈ 𝔪 ^ n → f i * a ∈ relI f d i (n + d i) →
    a ∈ relI f d i n)

include hf hreg in
/-- **Lemma 4.1, chain form.** If `gr_m A` has the Hilbert function of a polynomial ring in `N`
variables, `I` contains `f₁, …, f_s` whose initial forms are a regular sequence, then every chain
of primes containing `I` has length `≤ N − s`. -/
theorem lemma41_chain {N s : ℕ} (hA : OrderLE (hilbR f d 0) N) {I : Ideal A}
    (hI : ∀ j, f j ∈ I) (q : LTSeries (PrimeSpectrum A)) (hq : I ≤ (q 0).asIdeal) :
    q.length ≤ N - s := by
  have hR := orderLE_R f d hf hreg hA s
  -- `χ_I = Σ gr_j (A ⧸ I) ≤ Σ R_s`, of order `≤ N − s + 1`
  have hsum := orderLE_partialSum hR
  have hchi : OrderLE (chi I) (N - s + 1) := by
    refine orderLE_of_le hsum (orderLE_chi I) (chi_nonneg I) fun n => ?_
    rw [chi_eq_partialSum]
    exact Finset.sum_le_sum fun j _ => length_gr_le f d hf hI s j
  have h := chain_bound length_quot_pow_ne_top orderLE_chi q.length q rfl I hq _ hchi
  omega

include hf hreg in
/-- **Lemma 4.1.** `dim (A ⧸ I) ≤ N − s`. -/
theorem lemma41 {N s : ℕ} (hA : OrderLE (hilbR f d 0) N) {I : Ideal A}
    (hI : ∀ j, f j ∈ I) : ringKrullDim (A ⧸ I) ≤ ((N - s : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient]
  unfold Order.krullDim
  refine iSup_le fun q => ?_
  let q' := q.map Subtype.val (fun _ _ h => h)
  have hq0 : I ≤ (q' 0).asIdeal := by
    have := (PrimeSpectrum.mem_zeroLocus _ _).mp (q 0).2
    exact this
  have h := lemma41_chain (s := s) f d hf hreg hA hI q' hq0
  exact_mod_cast h

end Brent.CM
