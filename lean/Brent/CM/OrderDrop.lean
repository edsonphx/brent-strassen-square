import Brent.CM.PolyType

/-!
# The order drop behind `dim A ≤ d(A)` (roadmap step B, third part)

DRAFT, NOT YET COMPILED.

`Brent.CM.length_quot_add_le` gives, for `x` regular on `B`,
`χ_{B/x}(n) ≤ χ_B(n) − χ_B(n − c)` on a tail. If `χ_B` has order `≤ e + 1` and `χ_{B/x}` is of
polynomial type and nonnegative, then `χ_{B/x}` has order `≤ e`
(`orderLE_of_le_sub_shift`). This is the step of the induction on chains of primes in the
proof of `dim A ≤ d(A)`.

Imports `Brent.CM.PolyType` only.
-/

namespace Brent.CM

/-- **Order drop.** If `0 ≤ g n ≤ f n − f (n − c)` on a tail, `f` has order `≤ e + 1` and `g` is
of polynomial type, then `g` has order `≤ e`. -/
theorem orderLE_of_le_sub_shift {f g : ℕ → ℤ} {c e n₁ : ℕ} (hf : OrderLE f (e + 1))
    (hg : ∃ a, OrderLE g a) (hg0 : ∀ n ≥ n₁, 0 ≤ g n)
    (hle : ∀ n ≥ n₁, g n ≤ f n - f (n - c)) : OrderLE g e := by
  set h : ℕ → ℤ := fun n => f n - f (n - c) with hdef
  have hh : OrderLE h e :=
    orderLE_of_sub_shift (n₁ := 0) (d := c) (fun n _ => by simp [hdef]) hf
  cases e with
  | zero =>
    obtain ⟨n₀, hn₀⟩ := hh
    refine ⟨max n₀ n₁, fun n hn => ?_⟩
    have h1 : h n = 0 := hn₀ n (by omega)
    have h2 := hle n (by omega)
    have h3 := hg0 n (by omega)
    show g n = 0
    simp only [hdef] at h1
    omega
  | succ b =>
    obtain ⟨Cb, n₂, hb⟩ := bound_of_orderLE hh
    obtain ⟨a, ha⟩ := hg
    refine orderLE_of_bound (n₁ := max n₁ n₂) (Cb := Cb) ha fun n hn => ?_
    have h1 := hb n (by omega)
    have h2 : g n ≤ h n := hle n (by omega)
    have h3 := hg0 n (by omega)
    calc |(g n : ℝ)| = (g n : ℝ) := abs_of_nonneg (by exact_mod_cast h3)
      _ ≤ (h n : ℝ) := by exact_mod_cast h2
      _ ≤ |(h n : ℝ)| := le_abs_self _
      _ ≤ Cb * ((n : ℝ) + 1) ^ b := h1

end Brent.CM
