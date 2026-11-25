import Brent.MonomialReduction
import Brent.LocalDimension
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# A dimension bound from triangular mixed quadratic relations

Let `R` be a Noetherian local ring whose maximal ideal is generated, modulo `𝔪²`, by
elements `c₁,…,c_q`, `x₁,…,x_r`, `y₁,…,y_r`. Suppose that for each `ℓ` the mixed form
`Σ_{a,b} M_ℓ[a,b] x_a y_b` lies in `𝔪³`, where the tables `M_ℓ` are lexicographically
triangular with unit leading coefficient `M_ℓ[ℓ, π ℓ] = 1` for a bijection `π`. Then
`dim R ≤ q + r`.

The parameters are the `c_i` and `u_ℓ - x_ℓ`, with `u_ℓ = Σ_b M_ℓ[ℓ,b] y_b`. Each square
`x_ℓ²` reduces to strictly larger indices, so `𝔪^(r+1) ⊆ (parameters) + 𝔪^(r+2)`.
This is stated for an arbitrary ring to keep the algebra away from the heavy instances of
the concrete localization.
-/

open scoped BigOperators
open IsLocalRing

namespace Brent

theorem sum_comp_of_zero {M : Type*} [AddCommMonoid M] {n m : ℕ} (H : Fin n → M)
    (f : Fin m → Fin n) (hf : Function.Injective f) (h : ∀ i, (∀ a, f a ≠ i) → H i = 0) :
    ∑ i, H i = ∑ a, H (f a) := by
  have h1 := Finset.sum_map Finset.univ ⟨f, hf⟩ H
  simp only [Function.Embedding.coeFn_mk] at h1
  rw [← h1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => h i fun a ha => hi ?_).symm
  rw [← ha]
  exact Finset.mem_map_of_mem ⟨f, hf⟩ (Finset.mem_univ a)

theorem mem_sup_of_sub_mem {R : Type*} [CommRing R] {I J : Ideal R} {a b : R}
    (h : a - b ∈ J) (hb : b ∈ I) : a ∈ I ⊔ J := by
  have h' : a - b ∈ I ⊔ J := Ideal.mem_sup_right h
  have := Ideal.add_mem _ h' (Ideal.mem_sup_left hb)
  rwa [sub_add_cancel] at this

theorem triangular_dim_le {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {q r : ℕ} (c : Fin q → R) (xs ys : Fin r → R) (Mc : Fin r → Fin r → Fin r → R)
    (π : Fin r → Fin r) (hπ : Function.Surjective π)
    (hc : ∀ i, c i ∈ maximalIdeal R) (hx : ∀ a, xs a ∈ maximalIdeal R)
    (hy : ∀ b, ys b ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span (Set.range c) ⊔ Ideal.span (Set.range xs) ⊔
      Ideal.span (Set.range ys) ⊔ maximalIdeal R ^ 2)
    (hrel : ∀ ell, ∑ a, ∑ b, xs a * ys b * Mc ell a b ∈ maximalIdeal R ^ 3)
    (hlead : ∀ ell, Mc ell ell (π ell) = 1)
    (hzero : ∀ ell a b, r * a.val + b.val < r * ell.val + (π ell).val → Mc ell a b = 0) :
    ringKrullDim R ≤ ((q + r : ℕ) : WithBot ℕ∞) := by
  set m := maximalIdeal R with hm
  let L : Fin r → Fin r → R := fun ell a => ∑ b, Mc ell a b * ys b
  have L_zero : ∀ ell a, a < ell → L ell a = 0 := fun ell a h =>
    Finset.sum_eq_zero fun b _ => by
      have h1 : a.val < ell.val := h
      have h2 := b.isLt
      have h3 : r * (a.val + 1) ≤ r * ell.val := Nat.mul_le_mul_left _ h1
      rw [Nat.mul_add, Nat.mul_one] at h3
      rw [hzero ell a b (by omega), zero_mul]
  have L_mem : ∀ ell a, L ell a ∈ m := fun ell a =>
    Submodule.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b)
  have lead : ∀ ell, xs ell * L ell ell + ∑ a, (if ell < a then xs a * L ell a else 0) ∈ m ^ 3 := by
    intro ell
    have h := hrel ell
    have e : ∑ a, ∑ b, xs a * ys b * Mc ell a b = ∑ a, xs a * L ell a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have split : ∀ a, xs a * L ell a = (if a = ell then xs a * L ell a else 0) +
        (if ell < a then xs a * L ell a else 0) := by
      intro a
      rcases lt_trichotomy a ell with hl | hl | hl
      · rw [L_zero ell a hl, mul_zero]; simp
      · subst hl; simp
      · simp [hl, ne_of_gt hl]
    rw [e, Finset.sum_congr rfl fun a _ => split a, Finset.sum_add_distrib] at h
    simpa using h
  let par : Fin (q + r) → R := Fin.append c (fun ell => L ell ell - xs ell)
  let Ip : Ideal R := Ideal.span (Set.range par)
  have c_mem : ∀ i, c i ∈ Ip := fun i => Ideal.subset_span ⟨Fin.castAdd r i, by simp [par]⟩
  have d_mem : ∀ ell, L ell ell - xs ell ∈ Ip := fun ell =>
    Ideal.subset_span ⟨Fin.natAdd q ell, by simp [par]⟩
  have par_mem : ∀ i, par i ∈ m := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun ell => ?_) i
    · simp only [par, Fin.append_left]; exact hc i
    · simp only [par, Fin.append_right]; exact Ideal.sub_mem _ (L_mem _ _) (hx _)
  let N : Ideal R := Ideal.span (Set.range xs) ⊔ Ip
  have xs_N : ∀ a, xs a ∈ N := fun a => Ideal.mem_sup_left (Ideal.subset_span ⟨a, rfl⟩)
  have u_N : ∀ ell, L ell ell ∈ N := fun ell => by
    have := Ideal.add_mem _ (Ideal.mem_sup_right (d_mem ell)) (xs_N ell)
    rwa [sub_add_cancel] at this
  have ys_N : ∀ b, ys b ∈ N := by
    suffices key : ∀ n, ∀ b : Fin r, r - b.val = n → ys b ∈ N from fun b => key _ b rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro b hb
    obtain ⟨ell, hell⟩ := hπ b
    have split : ∀ b', Mc ell ell b' * ys b' = (if b' = b then ys b' else 0) +
        (if b < b' then Mc ell ell b' * ys b' else 0) := by
      intro b'
      rcases lt_trichotomy b' b with hl | hl | hl
      · have h1 : b'.val < b.val := hl
        rw [hzero ell ell b' (by rw [hell]; omega), zero_mul]
        simp [ne_of_lt hl, not_lt_of_gt hl]
      · subst hl
        rw [← hell, hlead]
        simp
      · simp [hl, ne_of_gt hl]
    have e : L ell ell = ys b + ∑ b', (if b < b' then Mc ell ell b' * ys b' else 0) := by
      simp only [L]
      rw [Finset.sum_congr rfl fun b' _ => split b', Finset.sum_add_distrib]
      simp
    have hsum : ∑ b', (if b < b' then Mc ell ell b' * ys b' else 0) ∈ N := by
      refine Submodule.sum_mem _ fun b' _ => ?_
      split_ifs with hlt
      · have h1 : b.val < b'.val := hlt
        have := b'.isLt
        exact Ideal.mul_mem_left _ _ (ih (r - b'.val) (by omega) b' rfl)
      · exact Ideal.zero_mem _
    have := Ideal.sub_mem _ (u_N ell) hsum
    rwa [e, add_sub_cancel_right] at this
  have hsq : m ≤ N ⊔ m ^ 2 := by
    refine hgen.trans (sup_le_sup_right (sup_le (sup_le ?_ ?_) ?_) _)
    · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact Ideal.mem_sup_right (c_mem i)
    · rw [Ideal.span_le]; rintro _ ⟨a, rfl⟩; exact xs_N a
    · rw [Ideal.span_le]; rintro _ ⟨b, rfl⟩; exact ys_N b
  have hmN : m ≤ N := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian m) (I := m) (N := N) (N' := m)
    · rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rw [Ideal.smul_eq_mul, ← pow_two]; exact hsq
  have hpow : m ^ (r + 1) ≤ Ip ⊔ m ^ (r + 2) := by
    refine pow_succ_le_of_triangular xs hx hmN fun ell =>
      ⟨fun a => -L ell a, fun a => (Ideal.neg_mem_iff _).mpr (L_mem ell a), ?_⟩
    have hneg : ∑ a, (if ell < a then xs a * -L ell a else 0) =
        -∑ a, (if ell < a then xs a * L ell a else 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
    have e : xs ell ^ 2 - ∑ a, (if ell < a then xs a * -L ell a else 0) =
        (xs ell * L ell ell + ∑ a, (if ell < a then xs a * L ell a else 0)) -
          xs ell * (L ell ell - xs ell) := by
      rw [hneg]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (lead ell))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (d_mem ell)))
  exact localDimension_le_of_power_le_span_sup_pow par par_mem (d := r + 1) (by omega) hpow

end Brent
