import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DefEqTransformations

/-!
# Hilbert functions of polynomial type (roadmap step A)

DRAFT, NOT YET COMPILED.

A Hilbert function `H : ℕ → ℤ` has *order `≤ e`* when its `e`-th forward difference eventually
vanishes, i.e. `H` is eventually a polynomial of degree `< e`. This is the numerical side of the
Hilbert–Serre theorem used in §4 (lines 457–482):

* `orderLE_of_sub_shift`: if `H'(n + d) = H(n + d) − H(n)` on a tail (the exact sequence
  `0 → gr(-d) →·f*→ gr → gr/(f*) → 0` for a regular form `f*` of degree `d ≥ 1`), the order drops
  by one;
* `orderLE_choose`: the Hilbert function `n ↦ C(n + N, N)` of `k[z₀, …, z_N]` has order
  `≤ N + 1`;
* `orderLE_partialSum`: summing a Hilbert function (`length(A/mⁿ) = Σ_{j<n} H(j)`) raises the
  order by one.

Imports Mathlib only.
-/

namespace Brent.CM

open Finset

/-- Forward difference. -/
def diff (h : ℕ → ℤ) : ℕ → ℤ := fun n => h (n + 1) - h n

/-- Iterated forward difference. -/
def diffPow : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, h => h
  | e + 1, h => diff (diffPow e h)

theorem diffPow_zero (h : ℕ → ℤ) : diffPow 0 h = h := rfl

theorem diffPow_succ (e : ℕ) (h : ℕ → ℤ) : diffPow (e + 1) h = diff (diffPow e h) := rfl

theorem diffPow_succ' (e : ℕ) (h : ℕ → ℤ) : diffPow (e + 1) h = diffPow e (diff h) := by
  induction e with
  | zero => rfl
  | succ e ih => rw [diffPow_succ, ih, ← diffPow_succ]

theorem diffPow_add (a b : ℕ) (h : ℕ → ℤ) : diffPow (a + b) h = diffPow a (diffPow b h) := by
  induction a with
  | zero => rw [Nat.zero_add, diffPow_zero]
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega, diffPow_succ, ih, diffPow_succ]

theorem diffPow_const_zero (e : ℕ) : diffPow e (fun _ => (0 : ℤ)) = fun _ => 0 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [diffPow_succ, ih]
    funext n
    simp [diff]

/-- `diffPow e f n` only depends on the values of `f` from `n` on. -/
theorem diffPow_congr (e : ℕ) {f g : ℕ → ℤ} {n₀ : ℕ} (hfg : ∀ n ≥ n₀, f n = g n) :
    ∀ n ≥ n₀, diffPow e f n = diffPow e g n := by
  induction e with
  | zero => exact hfg
  | succ e ih =>
    intro n hn
    rw [diffPow_succ, diffPow_succ]
    simp only [diff]
    rw [ih n hn, ih (n + 1) (by omega)]

theorem diffPow_sum (e : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℤ) (n : ℕ) :
    diffPow e (fun m => ∑ i ∈ s, f i m) n = ∑ i ∈ s, diffPow e (f i) n := by
  induction e generalizing n with
  | zero => rfl
  | succ e ih =>
    rw [diffPow_succ]
    simp only [diff, diffPow_succ]
    rw [ih, ih, ← Finset.sum_sub_distrib]

theorem diffPow_shift (e c : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    diffPow e (fun m => f (m + c)) n = diffPow e f (n + c) := by
  induction e generalizing n with
  | zero => rfl
  | succ e ih =>
    rw [diffPow_succ, diffPow_succ]
    simp only [diff]
    rw [ih, ih, show n + 1 + c = n + c + 1 by omega]

/-- Telescoping: `f (n + d) − f n = Σ_{j<d} Δf (n + j)`. -/
theorem sub_eq_sum_diff (f : ℕ → ℤ) (n d : ℕ) :
    f (n + d) - f n = ∑ j ∈ range d, diff f (n + j) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [diff]
    rw [← add_assoc]
    ring

/-- `f` has order `≤ e`: its `e`-th difference vanishes from some point on (eventually a
polynomial of degree `< e`). -/
def OrderLE (f : ℕ → ℤ) (e : ℕ) : Prop := ∃ n₀, ∀ n ≥ n₀, diffPow e f n = 0

theorem OrderLE.mono {f : ℕ → ℤ} {e e' : ℕ} (h : OrderLE f e) (hee : e ≤ e') :
    OrderLE f e' := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hee
  rw [add_comm e c, diffPow_add]
  have hz : ∀ m ≥ n₀, diffPow e f m = (fun _ => (0 : ℤ)) m := hn₀
  rw [diffPow_congr c hz n hn, diffPow_const_zero]

theorem OrderLE.congr {f g : ℕ → ℤ} {e n₁ : ℕ} (h : OrderLE f e) (hfg : ∀ n ≥ n₁, f n = g n) :
    OrderLE g e := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨max n₀ n₁, fun n hn => ?_⟩
  rw [← diffPow_congr e hfg n (by omega)]
  exact hn₀ n (by omega)

/-- **A regular form of degree `d` lowers the order by one.** If on a tail
`g (n + d) = f (n + d) − f n` and `f` has order `≤ e + 1`, then `g` has order `≤ e`. -/
theorem orderLE_of_sub_shift {f g : ℕ → ℤ} {d e n₁ : ℕ}
    (hg : ∀ n ≥ n₁, g (n + d) = f (n + d) - f n) (hf : OrderLE f (e + 1)) : OrderLE g e := by
  obtain ⟨n₀, hn₀⟩ := hf
  have hsum : ∀ n ≥ n₁, (fun m => g (m + d)) n =
      (fun m => ∑ j ∈ range d, diff f (m + j)) n := by
    intro n hn
    show g (n + d) = ∑ j ∈ range d, diff f (n + j)
    rw [hg n hn, sub_eq_sum_diff]
  refine ⟨max n₀ n₁ + d, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
  rw [← diffPow_shift, diffPow_congr e hsum m (by omega),
    diffPow_sum e (range d) (fun j m => diff f (m + j))]
  refine Finset.sum_eq_zero fun j _ => ?_
  beta_reduce
  rw [diffPow_shift e j (diff f) m, ← diffPow_succ']
  exact hn₀ _ (by omega)

/-- The Hilbert function `n ↦ C(n + N, N)` of the polynomial ring in `N + 1` variables. -/
def polyHilbert (N : ℕ) : ℕ → ℤ := fun n => ((n + N).choose N : ℤ)

theorem diff_polyHilbert_succ (N : ℕ) :
    diff (polyHilbert (N + 1)) = fun n => polyHilbert N (n + 1) := by
  funext n
  simp only [diff, polyHilbert]
  rw [show n + 1 + (N + 1) = (n + N + 1) + 1 by omega, Nat.choose_succ_succ',
    show n + (N + 1) = n + N + 1 by omega, show n + 1 + N = n + N + 1 by omega]
  push_cast
  ring

/-- **The polynomial ring in `N + 1` variables has Hilbert function of order `≤ N + 1`**
(a polynomial of degree `N`). -/
theorem orderLE_polyHilbert (N : ℕ) : OrderLE (polyHilbert N) (N + 1) := by
  induction N with
  | zero =>
    refine ⟨0, fun n _ => ?_⟩
    simp [diffPow, diff, polyHilbert]
  | succ N ih =>
    obtain ⟨n₀, hn₀⟩ := ih
    refine ⟨n₀, fun n hn => ?_⟩
    rw [diffPow_succ', diff_polyHilbert_succ, diffPow_shift]
    exact hn₀ _ (by omega)

/-- Partial sums: `S(n) = Σ_{j<n} H(j)` (the Hilbert–Samuel function `length(A/mⁿ)` from the
Hilbert function `H(j) = length(mʲ/mʲ⁺¹)`). -/
def partialSum (H : ℕ → ℤ) : ℕ → ℤ := fun n => ∑ j ∈ range n, H j

theorem diff_partialSum (H : ℕ → ℤ) : diff (partialSum H) = H := by
  funext n
  simp [diff, partialSum, Finset.sum_range_succ]

/-- **Summation raises the order by one.** -/
theorem orderLE_partialSum {H : ℕ → ℤ} {e : ℕ} (h : OrderLE H e) :
    OrderLE (partialSum H) (e + 1) := by
  obtain ⟨n₀, hn₀⟩ := h
  exact ⟨n₀, fun n hn => by rw [diffPow_succ', diff_partialSum]; exact hn₀ n hn⟩

end Brent.CM
