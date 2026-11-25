import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Fin

/-!
# Triangular quadratic relations force a finite-order parameter certificate

Let `x₀,…,x_{r-1}` be elements of an ideal `𝔪` that generate `𝔪` modulo an ideal `I`.
Suppose that for every `ℓ`, the square `x_ℓ²` agrees with an element of `(x_a : a > ℓ)·𝔪`
modulo `𝔪³ + I`. Then `𝔪^(r+1) ⊆ I + 𝔪^(r+2)`.

Every monomial of degree `r+1` in the `x` contains a square. Rewriting that square moves
weight to strictly larger indices; a numerical weight shows that the rewriting terminates.
This is the elementary replacement for the Gröbner-basis argument of §4: the leading
monomials of the projected quadrics are pairwise coprime and triangular.
-/

open scoped BigOperators

namespace Brent

section Monomial

variable {A : Type*} [CommRing A] {r : ℕ} (x : Fin r → A)

/-- The monomial with exponent vector `α`. -/
def mono (α : Fin r → ℕ) : A := ∏ i, x i ^ α i

/-- Total degree. -/
def deg (α : Fin r → ℕ) : ℕ := ∑ i, α i

theorem prod_pow_single (a : Fin r) (n : ℕ) : ∏ i, x i ^ (Pi.single a n : Fin r → ℕ) i = x a ^ n := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem mono_add (α β : Fin r → ℕ) : mono x (α + β) = mono x α * mono x β := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

theorem mono_single (a : Fin r) : mono x (Pi.single a 1) = x a := by
  simp [mono, prod_pow_single]

theorem deg_add (α β : Fin r → ℕ) : deg (α + β) = deg α + deg β := by
  simp [deg, Finset.sum_add_distrib]

theorem deg_single (a : Fin r) (n : ℕ) : deg (Pi.single a n : Fin r → ℕ) = n := by
  simp [deg]

theorem mono_mem_pow {m : Ideal A} (hx : ∀ i, x i ∈ m) (α : Fin r → ℕ) :
    mono x α ∈ m ^ deg α := by
  unfold mono deg
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hx i) _

/-- Monomials of a fixed degree. -/
def monoSpan (D : ℕ) : Ideal A := Ideal.span {y | ∃ α, deg α = D ∧ mono x α = y}

theorem monoSpan_mul_le (D : ℕ) :
    monoSpan x D * Ideal.span (Set.range x) ≤ monoSpan x (D + 1) := by
  rw [monoSpan, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨y, ⟨α, hα, rfl⟩, z, ⟨i, rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨α + Pi.single i 1, ?_, ?_⟩
  · rw [deg_add, deg_single, hα]
  · rw [mono_add, mono_single]

theorem pow_le_monoSpan {m I : Ideal A} (hm : m ≤ Ideal.span (Set.range x) ⊔ I) (D : ℕ) :
    m ^ D ≤ monoSpan x D ⊔ I := by
  induction D with
  | zero =>
    have h1 : (1 : A) ∈ monoSpan x 0 :=
      Ideal.subset_span ⟨0, by simp [deg], by simp [mono]⟩
    rw [pow_zero, Ideal.one_eq_top, (Ideal.eq_top_iff_one _).mpr h1, top_sup_eq]
  | succ D ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih hm).trans ?_
    rw [Ideal.mul_le]
    intro a ha b hb
    obtain ⟨s, hs, i, hi, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨t, ht, j, hj, rfl⟩ := Submodule.mem_sup.mp hb
    have e : (s + i) * (t + j) = s * t + (s * j + i * (t + j)) := by ring
    rw [e]
    exact Submodule.add_mem_sup (monoSpan_mul_le x D (Ideal.mul_mem_mul hs ht))
      (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hj) (Ideal.mul_mem_right _ _ hi))

/-- A weight that increases when a square is moved to larger indices. -/
def weight (α : Fin r → ℕ) : ℕ := ∑ i, α i * (r + 2) ^ i.val

omit [CommRing A] in
theorem weight_add (α β : Fin r → ℕ) : weight (α + β) = weight α + weight β := by
  simp [weight, add_mul, Finset.sum_add_distrib]

omit [CommRing A] in
theorem weight_single (a : Fin r) (n : ℕ) :
    weight (Pi.single a n : Fin r → ℕ) = n * (r + 2) ^ a.val := by
  rw [weight, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

omit [CommRing A] in
theorem weight_le {α : Fin r → ℕ} (h : deg α = r + 1) :
    weight α ≤ (r + 1) * ∑ i : Fin r, (r + 2) ^ i.val := by
  rw [weight, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ ?_
  rw [← h]
  exact Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

omit [CommRing A] in
theorem exists_two_le {α : Fin r → ℕ} (h : deg α = r + 1) : ∃ ℓ, 2 ≤ α ℓ := by
  by_contra hc
  push Not at hc
  have : deg α ≤ r := by
    calc deg α = ∑ i, α i := rfl
      _ ≤ ∑ _i : Fin r, 1 := Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (hc i)
      _ = r := by simp
  omega

/-- **Triangular reduction.** -/
theorem pow_succ_le_of_triangular {m I : Ideal A} (hx : ∀ i, x i ∈ m)
    (hm : m ≤ Ideal.span (Set.range x) ⊔ I)
    (hsq : ∀ ℓ, ∃ w : Fin r → A, (∀ a, w a ∈ m) ∧
      x ℓ ^ 2 - ∑ a, (if ℓ < a then x a * w a else 0) ∈ m ^ 3 ⊔ I) :
    m ^ (r + 1) ≤ I ⊔ m ^ (r + 2) := by
  set K := (r + 1) * ∑ i : Fin r, (r + 2) ^ i.val
  have key : ∀ n, ∀ α : Fin r → ℕ, deg α = r + 1 → K - weight α = n →
      mono x α ∈ I ⊔ m ^ (r + 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro α hα hn
    obtain ⟨ℓ, hℓ⟩ := exists_two_le hα
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact ℓ.elim0
    let β : Fin r → ℕ := α - Pi.single ℓ 2
    have hαβ : α = β + Pi.single ℓ 2 := by
      funext i
      by_cases h : i = ℓ
      · subst h; simp [β]; omega
      · simp [β, h]
    have hdeg : deg β + 2 = r + 1 := by
      rw [← deg_single ℓ 2, ← deg_add, ← hαβ, hα]
    have hmono : mono x α = mono x β * x ℓ ^ 2 := by
      rw [hαβ, mono_add]
      simp [mono, prod_pow_single]
    obtain ⟨w, hw, hrel⟩ := hsq ℓ
    set t := x ℓ ^ 2 - ∑ a, (if ℓ < a then x a * w a else 0)
    have hsplit : mono x α = mono x β * t +
        ∑ a, (if ℓ < a then mono x β * x a * w a else 0) := by
      rw [hmono]
      simp only [t]
      rw [mul_sub, Finset.mul_sum]
      simp only [mul_ite, mul_zero, mul_assoc]
      ring
    have hβm : mono x β ∈ m ^ (r - 1) := by
      have := mono_mem_pow x hx β
      rwa [show deg β = r - 1 by omega] at this
    rw [hsplit]
    refine Ideal.add_mem _ ?_ (Submodule.sum_mem _ fun a _ => ?_)
    · obtain ⟨t1, ht1, t2, ht2, e⟩ := Submodule.mem_sup.mp hrel
      rw [← e, mul_add]
      refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ ht2))
      have := Ideal.mul_mem_mul hβm ht1
      rwa [← pow_add, show r - 1 + 3 = r + 2 by omega] at this
    · split_ifs with hla
      swap
      · exact Ideal.zero_mem _
      obtain ⟨s, hs, i, hi, e⟩ := Submodule.mem_sup.mp (hm (hw a))
      obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hs
      rw [← e, ← hc, mul_add, Finset.mul_sum]
      refine Ideal.add_mem _ (Submodule.sum_mem _ fun b _ => ?_)
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hi))
      let γ : Fin r → ℕ := β + Pi.single a 1 + Pi.single b 1
      have hγdeg : deg γ = r + 1 := by
        simp only [γ, deg_add, deg_single]; omega
      have hγmono : mono x β * x a * (c b * x b) = c b * mono x γ := by
        simp only [γ, mono_add, mono_single]; ring
      rw [hγmono]
      refine Ideal.mul_mem_left _ _ (ih (K - weight γ) ?_ γ hγdeg rfl)
      have hwγ : weight γ = weight β + (r + 2) ^ a.val + (r + 2) ^ b.val := by
        simp only [γ, weight_add, weight_single, one_mul]
      have hwα : weight α = weight β + 2 * (r + 2) ^ ℓ.val := by
        rw [hαβ, weight_add, weight_single]
      have hlt : (r + 2) ^ (ℓ.val + 1) ≤ (r + 2) ^ a.val :=
        Nat.pow_le_pow_right (by omega) (by exact hla)
      have h3 : 3 * (r + 2) ^ ℓ.val ≤ (r + 2) ^ (ℓ.val + 1) := by
        rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left ((r + 2) ^ ℓ.val) (show 3 ≤ r + 2 by omega)
      have hpos : 0 < (r + 2) ^ ℓ.val := Nat.pow_pos (by omega)
      have hle := weight_le hγdeg
      omega
  have hmono : monoSpan x (r + 1) ≤ I ⊔ m ^ (r + 2) := by
    rw [monoSpan, Ideal.span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact key _ α hα rfl
  exact (pow_le_monoSpan x hm (r + 1)).trans (sup_le hmono le_sup_left)

end Monomial

end Brent
