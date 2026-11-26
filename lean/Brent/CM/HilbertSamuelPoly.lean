import Brent.CM.HilbertSerreFamily
import Brent.CM.Dimension
import Brent.CM.FiniteLength
import Mathlib.RingTheory.Filtration

/-!
# Hilbert–Samuel polynomiality and `dim A ≤ d(A)` (roadmap step B, conclusion)

DRAFT, NOT YET COMPILED.

For a Noetherian local ring `(A, m)` with `m = (x₁, …, x_s)` and an ideal `J`, put
`F n = J + mⁿ` and `G n = F n ⧸ F (n + 1)` (the associated graded module of `A ⧸ J`), with the
variables `X i : G n → G (n + 1)`, multiplication by `xᵢ`.

* `gnoeth_grFam`: the graded family `G` is Noetherian. A stable subfamily gives an
  `m`-filtration of `A ⧸ J` below the stable filtration `mⁿ (A ⧸ J)`, hence stable
  (`Ideal.Filtration.Stable.of_le`, Artin–Rees in Mathlib).
* `chi_eq_partialSum`: `χ_J(n) = length (A ⧸ (J + mⁿ)) = Σ_{j<n} length (G j)`.
* `orderLE_chi`: **Hilbert–Samuel.** `χ_J` has order `≤ s + 1`: it is eventually a polynomial
  (Hilbert–Serre, `orderLE_length_fam`, then summation).
* `ringKrullDim_le_of_orderLE_chi`: **`dim A ≤ d(A)`**, with no further hypothesis.
-/

namespace Brent.CM

open IsLocalRing

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

section Gr

variable (J : Ideal A)

/-- `F n = J + mⁿ`. -/
abbrev filt (n : ℕ) : Ideal A := J ⊔ maximalIdeal A ^ n

theorem filt_succ_le (n : ℕ) : filt J (n + 1) ≤ filt J n :=
  sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ n)) _

theorem mul_mem_filt {a : A} (ha : a ∈ maximalIdeal A) {n : ℕ} {b : A} (hb : b ∈ filt J n) :
    a * b ∈ filt J (n + 1) := by
  obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
  rw [mul_add]
  refine Submodule.add_mem_sup (Ideal.mul_mem_left _ a hj) ?_
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha hc

/-- `F (n + 1)` inside `F n`. -/
abbrev filtSub (n : ℕ) : Submodule A (filt J n) := (filt J (n + 1)).comap (filt J n).subtype

/-- The graded piece `G n = F n ⧸ F (n + 1)`. -/
abbrev grFam (n : ℕ) : Type u := filt J n ⧸ filtSub J n

/-- Multiplication by `a ∈ m`, from `F n` to `F (n + 1)`. -/
noncomputable def mulFilt {a : A} (ha : a ∈ maximalIdeal A) (n : ℕ) :
    filt J n →ₗ[A] filt J (n + 1) :=
  (LinearMap.mulLeft A a).restrict fun _ hb => mul_mem_filt J ha hb

theorem mulFilt_apply {a : A} (ha : a ∈ maximalIdeal A) (n : ℕ) (b : filt J n) :
    ((mulFilt J ha n b : filt J (n + 1)) : A) = a * b := rfl

/-- Multiplication by `a ∈ m` on the graded pieces. -/
noncomputable def mulGr {a : A} (ha : a ∈ maximalIdeal A) (n : ℕ) :
    grFam J n →ₗ[A] grFam J (n + 1) :=
  Submodule.mapQ _ _ (mulFilt J ha n) fun b hb => by
    show a * (b : A) ∈ filt J (n + 1 + 1)
    exact mul_mem_filt J ha hb

theorem mulGr_mk {a : A} (ha : a ∈ maximalIdeal A) (n : ℕ) (b : filt J n) :
    mulGr J ha n (Submodule.Quotient.mk b) = Submodule.Quotient.mk (mulFilt J ha n b) := rfl

variable {s : ℕ} (x : Fin s → A) (hx : ∀ i, x i ∈ maximalIdeal A)

/-- The variables of `gr_m (A ⧸ J)`. -/
noncomputable def grVars : Fin s → ∀ n, grFam J n →ₗ[A] grFam J (n + 1) :=
  fun i n => mulGr J (hx i) n

theorem grVars_commutes : Commutes (grVars J x hx) := by
  intro i j n
  apply Submodule.linearMap_qext
  ext b
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, grVars, mulGr_mk]
  congr 1
  apply Subtype.ext
  simp only [mulFilt_apply]
  ring

/-! ### Lengths -/

/-- `G n ↪ A ⧸ F (n + 1)`. -/
noncomputable def grIncl (n : ℕ) : grFam J n →ₗ[A] A ⧸ filt J (n + 1) :=
  Submodule.mapQ _ _ (filt J n).subtype le_rfl

theorem grIncl_injective (n : ℕ) : Function.Injective (grIncl J n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H b =>
    rw [LinearMap.mem_ker, grIncl, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq

theorem grIncl_exact (n : ℕ) :
    Function.Exact (grIncl J n) (Submodule.factor (filt_succ_le J n)) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H a =>
    rw [Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro ha
      exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, rfl⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with
      | H b =>
        rw [grIncl, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.Quotient.eq] at hq
        have h1 : (b : A) - a ∈ filt J n := filt_succ_le J n hq
        have h2 : a = (b : A) - ((b : A) - a) := by ring
        rw [h2]
        exact Submodule.sub_mem _ b.2 h1

theorem length_filt_ne_top (n : ℕ) : Module.length A (A ⧸ filt J n) ≠ ⊤ :=
  ne_top_of_le_ne_top (length_quot_pow_ne_top n)
    (Module.length_le_of_surjective (Submodule.factor (le_sup_right : maximalIdeal A ^ n ≤ _))
      (Submodule.factor_surjective _))

theorem length_grFam_ne_top (n : ℕ) : Module.length A (grFam J n) ≠ ⊤ :=
  ne_top_of_le_ne_top (length_filt_ne_top J (n + 1))
    (Module.length_le_of_injective _ (grIncl_injective J n))

theorem length_filt_succ (n : ℕ) :
    Module.length A (A ⧸ filt J (n + 1)) =
      Module.length A (grFam J n) + Module.length A (A ⧸ filt J n) :=
  Module.length_eq_add_of_exact _ _ (grIncl_injective J n) (Submodule.factor_surjective _)
    (grIncl_exact J n)

/-- **`χ_J(n) = Σ_{j<n} length (gr_j)`.** -/
theorem chi_eq_partialSum (n : ℕ) :
    chi J n = partialSum (fun j => lenZ (A := A) (grFam J j)) n := by
  induction n with
  | zero =>
    simp only [partialSum, Finset.range_zero, Finset.sum_empty]
    show ((Module.length A (A ⧸ (J ⊔ maximalIdeal A ^ 0))).toNat : ℤ) = 0
    haveI : Subsingleton (A ⧸ (J ⊔ maximalIdeal A ^ 0)) := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero_iff.mpr inferInstance]
    rfl
  | succ n ih =>
    rw [partialSum, Finset.sum_range_succ, ← partialSum, ← ih]
    show ((Module.length A (A ⧸ filt J (n + 1))).toNat : ℤ) =
      ((Module.length A (A ⧸ filt J n)).toNat : ℤ) + lenZ (A := A) (grFam J n)
    rw [length_filt_succ, ENat.toNat_add (length_grFam_ne_top J n) (length_filt_ne_top J n)]
    unfold lenZ
    push_cast
    ring

/-! ### The graded family is Noetherian -/

variable (hspan : Submodule.span A (Set.range x) = maximalIdeal A)

include hspan in
/-- Elements of `m` act like the variables: closure of a submodule of `A` under the `xᵢ`
gives closure under `m`. -/
theorem mul_mem_of_span {P Q : Submodule A A} (hPQ : ∀ i, ∀ t ∈ P, x i * t ∈ Q)
    {a : A} (ha : a ∈ maximalIdeal A) : ∀ t ∈ P, a * t ∈ Q := by
  rw [← hspan] at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hPQ i
  | zero => intro t _; rw [zero_mul]; exact Q.zero_mem
  | add y z _ _ hy hz =>
    intro t ht
    rw [add_mul]
    exact Q.add_mem (hy t ht) (hz t ht)
  | smul c y _ hy =>
    intro t ht
    rw [smul_eq_mul, mul_assoc]
    exact Q.smul_mem c (hy t ht)

include hspan in
/-- **`gr_m (A ⧸ J)` is a Noetherian graded family.** -/
theorem gnoeth_grFam : GNoeth (grVars J x hx) := by
  intro S hS
  -- the subfamily, lifted to submodules `T n` of `A` between `F (n + 1)` and `F n`
  let T : ∀ n, Submodule A A := fun n => ((S n).comap (filtSub J n).mkQ).map (filt J n).subtype
  have hTF : ∀ n, T n ≤ filt J n := fun n => by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hFT : ∀ n, filt J (n + 1) ≤ T n := fun n a ha => by
    refine ⟨⟨a, filt_succ_le J n ha⟩, ?_, rfl⟩
    show Submodule.Quotient.mk _ ∈ S n
    rw [(Submodule.Quotient.mk_eq_zero _).mpr ha]
    exact (S n).zero_mem
  have hTx : ∀ n i, ∀ t ∈ T n, x i * t ∈ T (n + 1) := by
    rintro n i _ ⟨b, hb, rfl⟩
    exact ⟨mulFilt J (hx i) n b, hS i n _ hb, rfl⟩
  have hTm : ∀ n, ∀ a ∈ maximalIdeal A, ∀ t ∈ T n, a * t ∈ T (n + 1) := fun n a ha =>
    mul_mem_of_span x hspan (hTx n) ha
  -- the induced `m`-filtration of `A ⧸ J`
  let Fl : (maximalIdeal A).Filtration (A ⧸ J) :=
    { N := fun n => (T n).map J.mkQ
      mono := fun n => Submodule.map_mono ((hTF (n + 1)).trans (hFT n))
      smul_le := fun n => by
        rw [Submodule.smul_le]
        rintro a ha _ ⟨t, ht, rfl⟩
        rw [← map_smul, smul_eq_mul]
        exact ⟨a * t, hTm n a ha t ht, rfl⟩ }
  have hle : Fl ≤ (maximalIdeal A).stableFiltration ⊤ := by
    intro n
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨j, hj, c, hc, hjc⟩ := Submodule.mem_sup.mp (hTF n ht)
    show J.mkQ t ∈ maximalIdeal A ^ n • (⊤ : Submodule A (A ⧸ J))
    have : J.mkQ t = c • J.mkQ 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, ← hjc, map_add,
        (Submodule.Quotient.mk_eq_zero J).mpr hj, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  obtain ⟨n₀, hn₀⟩ :=
    Ideal.Filtration.Stable.of_le ((maximalIdeal A).stableFiltration_stable ⊤) hle
  refine ⟨n₀, fun n hn => ?_⟩
  -- the target, lifted to `A`
  let W : Submodule A A :=
    ((⨆ i, (S n).map (grVars J x hx i n)).comap (filtSub J (n + 1)).mkQ).map
      (filt J (n + 1)).subtype
  have hWx : ∀ i, ∀ t ∈ T n, x i * t ∈ W := by
    rintro i _ ⟨b, hb, rfl⟩
    refine ⟨mulFilt J (hx i) n b, ?_, rfl⟩
    show Submodule.Quotient.mk _ ∈ _
    exact Submodule.mem_iSup_of_mem i ⟨Submodule.Quotient.mk b, hb, rfl⟩
  have hmW : maximalIdeal A • T n ≤ W := by
    rw [Submodule.smul_le]
    intro a ha t ht
    exact mul_mem_of_span x hspan hWx ha t ht
  have hJW : J ≤ W := fun a ha => by
    have hF : a ∈ filt J (n + 1 + 1) := Submodule.mem_sup_left ha
    refine ⟨⟨a, filt_succ_le J _ hF⟩, ?_, rfl⟩
    show Submodule.Quotient.mk _ ∈ _
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hF]
    exact Submodule.zero_mem _
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H b =>
    have hbT : (b : A) ∈ T (n + 1) := ⟨b, hq, rfl⟩
    have hb1 : J.mkQ b ∈ Fl.N (n + 1) := ⟨b, hbT, rfl⟩
    rw [← hn₀ n hn] at hb1
    have hb2 : J.mkQ b ∈ (maximalIdeal A • T n).map J.mkQ := by
      rwa [Submodule.map_smul'']
    obtain ⟨c, hc, hcb⟩ := hb2
    have hdiff : (b : A) - c ∈ J := by
      rw [← Submodule.Quotient.eq]
      exact hcb.symm
    have hbW : (b : A) ∈ W := by
      have : (b : A) = ((b : A) - c) + c := by ring
      rw [this]
      exact W.add_mem (hJW hdiff) (hmW hc)
    obtain ⟨b', hb', hbb⟩ := hbW
    rw [Submodule.subtype_apply] at hbb
    rw [← Subtype.ext hbb]
    exact hb'

end Gr

/-! ### Hilbert–Samuel and `dim A ≤ d(A)` -/

theorem exists_generators :
    ∃ (s : ℕ) (x : Fin s → A), Submodule.span A (Set.range x) = maximalIdeal A :=
  Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian _)

theorem generators_mem {s : ℕ} {x : Fin s → A}
    (hspan : Submodule.span A (Set.range x) = maximalIdeal A) (i : Fin s) :
    x i ∈ maximalIdeal A := by
  rw [← hspan]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- **Hilbert–Samuel.** For every ideal `J`, `n ↦ length (A ⧸ (J + mⁿ))` is eventually a
polynomial: it has order `≤ s + 1`, `s` the number of generators of `m`. -/
theorem orderLE_chi (J : Ideal A) : ∃ a, OrderLE (chi J) a := by
  obtain ⟨s, x, hspan⟩ := exists_generators (A := A)
  have hx := generators_mem hspan
  have hG := orderLE_length_fam s (grFam J) (grVars J x hx) (grVars_commutes J x hx)
    (gnoeth_grFam J x hx hspan) (length_grFam_ne_top J)
  refine ⟨s + 1, ?_⟩
  have hsum := orderLE_partialSum hG
  exact hsum.congr (n₁ := 0) fun n _ => (chi_eq_partialSum J n).symm

/-- **Dimension ≤ Hilbert–Samuel degree.** If `n ↦ length (A ⧸ mⁿ)` is eventually a polynomial
of degree `< e`, then `dim A ≤ e − 1`. -/
theorem ringKrullDim_le_of_orderLE_chi {e : ℕ} (he : OrderLE (chi (⊥ : Ideal A)) e) :
    ringKrullDim A ≤ ((e - 1 : ℕ) : WithBot ℕ∞) :=
  ringKrullDim_le_of_orderLE length_quot_pow_ne_top orderLE_chi he

end Brent.CM
