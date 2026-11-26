import Brent.CM.OrderDrop
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact
import Mathlib.Order.RelSeries

/-!
# `dim A ≤ d(A)` (roadmap step B, fourth part)

DRAFT, NOT YET COMPILED.

For a Noetherian local ring `(A, m)` and an ideal `J`, write
`χ_J(n) = length_A (A ⧸ (J + mⁿ))`. This file proves the half `dim A ≤ d(A)` of the dimension
theorem, by the induction on chains of primes used in the paper (Atiyah–Macdonald 11.14):

* `length_quot_add_le_rel`: for a prime `P` and `x ∉ P`,
  `χ_P(n − c) + χ_{P + (x)}(n) ≤ χ_P(n)` on a tail (Artin–Rees in `A ⧸ P`);
* `chain_bound`: a chain `q₀ < ⋯ < q_r` of primes over `J` and `χ_J` of order `≤ e` give
  `r + 1 ≤ e`;
* `ringKrullDim_le_of_orderLE`: if `χ_0` has order `≤ e` then `dim A ≤ e − 1`, i.e.
  `dim A ≤ deg χ_0 = d(A)`.

The hypotheses `hfin` (the lengths `length (A ⧸ mⁿ)` are finite) and `hpoly` (every `χ_J` is of
polynomial type) are the Hilbert–Samuel polynomiality statements, discharged in
`Brent.CM.HilbertSerreModule`.
-/

namespace Brent.CM

open Ideal IsLocalRing

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

/-! ### Artin–Rees relative to a prime -/

/-- **Artin–Rees in `A ⧸ P`.** For a prime `P` and `x ∉ P` there is `c` with
`x y ∈ P + mⁿ → y ∈ P + m^(n − c)` for all `n ≥ c`. -/
theorem exists_colon_pow_le_rel (m P : Ideal A) [hP : P.IsPrime] {x : A} (hx : x ∉ P) :
    ∃ c, ∀ n ≥ c, ∀ y : A, x * y ∈ P ⊔ m ^ n → y ∈ P ⊔ m ^ (n - c) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul m (M := A ⧸ P)
    (Submodule.span A {Submodule.mkQ P x})
  refine ⟨c, fun n hn y hy => ?_⟩
  obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hy
  have hq0 : Submodule.mkQ P p = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hp
  have hmem : Submodule.mkQ P (x * y) ∈
      (m ^ n • ⊤ ⊓ Submodule.span A {Submodule.mkQ P x} : Submodule A (A ⧸ P)) := by
    refine ⟨?_, ?_⟩
    · have : Submodule.mkQ P (x * y) = r • Submodule.mkQ P 1 := by
        rw [← map_smul, smul_eq_mul, mul_one, ← hpr, map_add, hq0, zero_add]
      rw [this]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [mul_comm, ← smul_eq_mul, map_smul]
      exact Submodule.smul_mem _ y (Submodule.mem_span_singleton_self _)
  rw [hc n hn] at hmem
  have hle : (m ^ (n - c) • (m ^ c • ⊤ ⊓ Submodule.span A {Submodule.mkQ P x}) :
      Submodule A (A ⧸ P)) ≤ m ^ (n - c) • Submodule.span A {Submodule.mkQ P x} :=
    Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_smul_span_singleton.mp (hle hmem)
  have hdiff : x * (y - z) ∈ P := by
    have h0 : Submodule.mkQ P (x * y - z * x) = 0 := by
      rw [map_sub, ← hzx, ← smul_eq_mul z x, map_smul, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    have : x * (y - z) = x * y - z * x := by ring
    rw [this]
    exact h0
  have hyz : y - z ∈ P := (hP.mem_or_mem hdiff).resolve_left hx
  have : y = (y - z) + z := by ring
  rw [this]
  exact Submodule.add_mem_sup hyz hz

/-! ### The exact sequence `A →·x→ ((x) + Q) ⧸ Q → 0` -/

theorem mul_mem_ker_factor_rel (Q : Ideal A) (x : A) (y : A) :
    ((Submodule.mkQ Q).comp (LinearMap.mulLeft A x)) y ∈
      LinearMap.ker (Submodule.factor (le_sup_right : Q ≤ span {x} ⊔ Q)) := by
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.factor_mk,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_sup_left (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))

/-- Multiplication by `x`, from `A` onto `((x) + Q) ⧸ Q`. -/
noncomputable def mulToKerRel (Q : Ideal A) (x : A) :
    A →ₗ[A] LinearMap.ker (Submodule.factor (le_sup_right : Q ≤ span {x} ⊔ Q)) :=
  LinearMap.codRestrict _ ((Submodule.mkQ Q).comp (LinearMap.mulLeft A x))
    (mul_mem_ker_factor_rel Q x)

theorem mulToKerRel_surjective (Q : Ideal A) (x : A) :
    Function.Surjective (mulToKerRel Q x) := by
  rintro ⟨q, hq⟩
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [LinearMap.mem_ker, Submodule.factor_mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_sup] at hq
  obtain ⟨u, hu, v, hv, rfl⟩ := hq
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  refine ⟨y, Subtype.ext ?_⟩
  simp only [mulToKerRel, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have : x * y - (y * x + v) = -v := by ring
  rw [this]
  exact Submodule.neg_mem _ hv

theorem ker_mulToKerRel_le (Q Q' : Ideal A) {x : A} (hc : ∀ y : A, x * y ∈ Q → y ∈ Q') :
    LinearMap.ker (mulToKerRel Q x) ≤ Q' := by
  intro y hy
  rw [mulToKerRel, LinearMap.ker_codRestrict, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  exact hc y hy

/-- **The Hilbert–Samuel function drops modulo a prime and a new element.** For a prime `P` and
`x ∉ P` there is `c` with, for all `n ≥ c`,
`length (A ⧸ (P + m^(n − c))) + length (A ⧸ ((x) + (P + mⁿ))) ≤ length (A ⧸ (P + mⁿ))`. -/
theorem length_quot_add_le_rel (m P : Ideal A) [P.IsPrime] {x : A} (hx : x ∉ P) :
    ∃ c, ∀ n ≥ c,
      Module.length A (A ⧸ (P ⊔ m ^ (n - c))) + Module.length A (A ⧸ (span {x} ⊔ (P ⊔ m ^ n)))
        ≤ Module.length A (A ⧸ (P ⊔ m ^ n)) := by
  obtain ⟨c, hc⟩ := exists_colon_pow_le_rel m P hx
  refine ⟨c, fun n hn => ?_⟩
  set g := Submodule.factor (le_sup_right : P ⊔ m ^ n ≤ span {x} ⊔ (P ⊔ m ^ n))
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _) (Submodule.factor_surjective _)
    (LinearMap.exact_subtype_ker_map g)]
  gcongr
  have e := (mulToKerRel (P ⊔ m ^ n) x).quotKerEquivOfSurjective
    (mulToKerRel_surjective (P ⊔ m ^ n) x)
  rw [← e.length_eq]
  exact Module.length_le_of_surjective
    (Submodule.factor (ker_mulToKerRel_le (P ⊔ m ^ n) (P ⊔ m ^ (n - c)) (hc n hn)))
    (Submodule.factor_surjective _)

/-! ### `ℕ∞` to `ℤ` -/

theorem toNat_add_le {a b c : ℕ∞} (hc : c ≠ ⊤) (h : a + b ≤ c) :
    a.toNat + b.toNat ≤ c.toNat := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hc (le_trans le_self_add h)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top hc (le_trans le_add_self h)
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift c to ℕ using hc
  simp only [ENat.toNat_coe]
  exact_mod_cast h

theorem toNat_le_toNat' {a c : ℕ∞} (hc : c ≠ ⊤) (h : a ≤ c) : a.toNat ≤ c.toNat := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hc h
  lift a to ℕ using ha
  lift c to ℕ using hc
  simp only [ENat.toNat_coe]
  exact_mod_cast h

/-! ### The Hilbert–Samuel functions `χ_J` -/

variable [IsLocalRing A]

/-- `χ_J(n) = length_A (A ⧸ (J + mⁿ))`, `m` the maximal ideal. -/
noncomputable def chi (J : Ideal A) : ℕ → ℤ :=
  fun n => ((Module.length A (A ⧸ (J ⊔ maximalIdeal A ^ n))).toNat : ℤ)

theorem chi_nonneg (J : Ideal A) (n : ℕ) : 0 ≤ chi J n := Int.natCast_nonneg _

theorem length_ne_top_of_le (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    {J J' : Ideal A} (n : ℕ) (h : J ⊔ maximalIdeal A ^ n ≤ J') :
    Module.length A (A ⧸ J') ≠ ⊤ := by
  have hle : maximalIdeal A ^ n ≤ J' := le_trans le_sup_right h
  exact ne_top_of_le_ne_top (hfin n)
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective _))

/-- `χ` is antitone in `J`. -/
theorem chi_anti (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    {J J' : Ideal A} (h : J ≤ J') (n : ℕ) : chi J' n ≤ chi J n := by
  have hle : J ⊔ maximalIdeal A ^ n ≤ J' ⊔ maximalIdeal A ^ n := sup_le_sup_right h _
  have := toNat_le_toNat' (length_ne_top_of_le hfin n le_rfl)
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective _))
  unfold chi
  exact_mod_cast this

/-- `χ_J(n) ≥ 1` for `J ≤ m` and `n ≥ 1`. -/
theorem one_le_chi (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    {J : Ideal A} (hJ : J ≤ maximalIdeal A) {n : ℕ} (hn : n ≠ 0) : 1 ≤ chi J n := by
  have hne : J ⊔ maximalIdeal A ^ n ≠ ⊤ := by
    intro htop
    have : J ⊔ maximalIdeal A ^ n ≤ maximalIdeal A := sup_le hJ (Ideal.pow_le_self hn)
    rw [htop] at this
    exact (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp this)
  haveI : Nontrivial (A ⧸ (J ⊔ maximalIdeal A ^ n)) := Submodule.Quotient.nontrivial_iff.mpr hne
  have hpos : 0 < Module.length A (A ⧸ (J ⊔ maximalIdeal A ^ n)) := Module.length_pos
  have hfin' := length_ne_top_of_le hfin n (J := J) le_rfl
  unfold chi
  have : 1 ≤ (Module.length A (A ⧸ (J ⊔ maximalIdeal A ^ n))).toNat := by
    lift (Module.length A (A ⧸ (J ⊔ maximalIdeal A ^ n))) to ℕ using hfin' with k hk
    simp only [ENat.toNat_coe]
    have : 0 < k := by exact_mod_cast hpos
    omega
  exact_mod_cast this

theorem not_orderLE_zero (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    {J : Ideal A} (hJ : J ≤ maximalIdeal A) : ¬ OrderLE (chi J) 0 := by
  rintro ⟨n₀, hn₀⟩
  have h1 := one_le_chi hfin hJ (n := n₀ + 1) (by omega)
  have h2 : chi J (n₀ + 1) = 0 := hn₀ (n₀ + 1) (by omega)
  omega

/-- A nonnegative function below one of order `≤ e`, and of polynomial type, has order `≤ e`. -/
theorem orderLE_of_le {f g : ℕ → ℤ} {e : ℕ} (hf : OrderLE f e) (hg : ∃ a, OrderLE g a)
    (hg0 : ∀ n, 0 ≤ g n) (hle : ∀ n, g n ≤ f n) : OrderLE g e := by
  cases e with
  | zero =>
    obtain ⟨n₀, hn₀⟩ := hf
    refine ⟨n₀, fun n hn => ?_⟩
    have h1 : f n = 0 := hn₀ n hn
    have h2 := hle n
    have h3 := hg0 n
    show g n = 0
    omega
  | succ b =>
    obtain ⟨Cb, n₂, hb⟩ := bound_of_orderLE hf
    obtain ⟨a, ha⟩ := hg
    refine orderLE_of_bound (n₁ := n₂) (Cb := Cb) ha fun n hn => ?_
    have h1 := hb n hn
    calc |(g n : ℝ)| = (g n : ℝ) := abs_of_nonneg (by exact_mod_cast hg0 n)
      _ ≤ (f n : ℝ) := by exact_mod_cast hle n
      _ ≤ |(f n : ℝ)| := le_abs_self _
      _ ≤ Cb * ((n : ℝ) + 1) ^ b := h1

/-- **The drop step.** For a prime `P ≤ m` and `x ∉ P`, if `χ_P` has order `≤ e + 1` then
`χ_{(x) + P}` has order `≤ e`. -/
theorem orderLE_chi_sup (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    (hpoly : ∀ J : Ideal A, ∃ a, OrderLE (chi J) a) (P : Ideal A) [P.IsPrime] {x : A}
    (hx : x ∉ P) {e : ℕ} (he : OrderLE (chi P) (e + 1)) :
    OrderLE (chi (span {x} ⊔ P)) e := by
  obtain ⟨c, hc⟩ := length_quot_add_le_rel (maximalIdeal A) P hx
  refine orderLE_of_le_sub_shift (n₁ := c) (c := c) he (hpoly _)
    (fun n _ => chi_nonneg _ n) fun n hn => ?_
  have h := toNat_add_le (length_ne_top_of_le hfin n (J := P) le_rfl) (hc n hn)
  unfold chi
  rw [sup_assoc]
  have : ((Module.length A (A ⧸ (span {x} ⊔ (P ⊔ maximalIdeal A ^ n)))).toNat : ℤ) ≤
      ((Module.length A (A ⧸ (P ⊔ maximalIdeal A ^ n))).toNat : ℤ) -
        ((Module.length A (A ⧸ (P ⊔ maximalIdeal A ^ (n - c)))).toNat : ℤ) := by
    have h' : ((Module.length A (A ⧸ (P ⊔ maximalIdeal A ^ (n - c)))).toNat : ℤ) +
        ((Module.length A (A ⧸ (span {x} ⊔ (P ⊔ maximalIdeal A ^ n)))).toNat : ℤ) ≤
        ((Module.length A (A ⧸ (P ⊔ maximalIdeal A ^ n))).toNat : ℤ) := by
      exact_mod_cast h
    linarith
  exact this

/-- **Chains of primes are shorter than the order of `χ`.** If `q₀ < ⋯ < q_r` is a chain of
primes with `J ≤ q₀` and `χ_J` has order `≤ e`, then `r + 1 ≤ e`. -/
theorem chain_bound (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    (hpoly : ∀ J : Ideal A, ∃ a, OrderLE (chi J) a) :
    ∀ (r : ℕ) (q : LTSeries (PrimeSpectrum A)), q.length = r →
      ∀ (J : Ideal A), J ≤ (q 0).asIdeal → ∀ e, OrderLE (chi J) e → r + 1 ≤ e := by
  intro r
  induction r with
  | zero =>
    intro q _ J hJ e he
    have hJm : J ≤ maximalIdeal A := le_trans hJ (le_maximalIdeal_of_isPrime _)
    by_contra hlt
    have he0 : e = 0 := by omega
    subst he0
    exact not_orderLE_zero hfin hJm he
  | succ r ih =>
    intro q hq J hJ e he
    have hlen : q.length ≠ 0 := by omega
    let i₀ : Fin q.length := ⟨0, Nat.pos_of_ne_zero hlen⟩
    have hlt : (q i₀.castSucc).asIdeal < (q i₀.succ).asIdeal :=
      (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr (q.step i₀)
    have h0 : q i₀.castSucc = q 0 := rfl
    have h1 : q i₀.succ = q 1 := by
      congr 1
      ext
      simp [i₀, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < q.length + 1)]
    rw [h0, h1] at hlt
    obtain ⟨x, hx1, hx0⟩ := SetLike.exists_of_lt hlt
    set P := (q 0).asIdeal
    have hPm : P ≤ maximalIdeal A := le_maximalIdeal_of_isPrime _
    -- `χ_P` has order `≤ e`
    have hP : OrderLE (chi P) e :=
      orderLE_of_le he (hpoly P) (chi_nonneg P) (chi_anti hfin hJ)
    -- `e ≠ 0`
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := by
      rcases e with _ | e'
      · exact absurd hP (not_orderLE_zero hfin hPm)
      · exact ⟨e', rfl⟩
    have hdrop := orderLE_chi_sup hfin hpoly P hx0 hP
    have hJ' : span {x} ⊔ P ≤ ((q.tail hlen) 0).asIdeal := by
      have : (q.tail hlen) 0 = q 1 := RelSeries.head_tail q hlen
      rw [this]
      refine sup_le ?_ (le_of_lt hlt)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hx1
    have := ih (q.tail hlen) (by simp [RelSeries.tail, hq]) _ hJ' e' hdrop
    omega

/-- **`dim A ≤ d(A)`.** If the Hilbert–Samuel function `n ↦ length (A ⧸ mⁿ)` has order `≤ e`
(eventually a polynomial of degree `< e`), then `dim A ≤ e − 1`. -/
theorem ringKrullDim_le_of_orderLE (hfin : ∀ n, Module.length A (A ⧸ maximalIdeal A ^ n) ≠ ⊤)
    (hpoly : ∀ J : Ideal A, ∃ a, OrderLE (chi J) a) {e : ℕ} (he : OrderLE (chi ⊥) e) :
    ringKrullDim A ≤ ((e - 1 : ℕ) : WithBot ℕ∞) := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun q => ?_
  have h := chain_bound hfin hpoly q.length q rfl ⊥ bot_le e he
  have : q.length ≤ e - 1 := by omega
  exact_mod_cast this

end Brent.CM
