import Brent.DeformationJets
import Mathlib.RingTheory.Ideal.Operations

/-!
# Bilinear expansion of the quadratic Brent term

`bilinearEntry p x y` is a (non-symmetric) bilinear form with `bilinearEntry p x x` the
quadratic term at `p` and `bilinearEntry p x y + bilinearEntry p y x` its polarization.
We expand it on linear combinations of directions, and bound the effect of perturbing a
direction by an element of `𝔪²`.
-/

open scoped BigOperators

namespace Brent.Decomposition

variable {R α ι : Type*} [CommRing R] [Fintype ι]

def bilinearEntry (p x y : Decomposition R α ι) (a b c : α × α) : R :=
  ∑ s, (x.u s a * y.v s b * p.w s c + x.u s a * p.v s b * y.w s c +
    p.u s a * x.v s b * y.w s c)

theorem quadraticEntry_eq_bilinear (p x : Decomposition R α ι) (a b c : α × α) :
    p.quadraticEntry x a b c = p.bilinearEntry x x a b c := rfl

theorem polarizedEntry_eq_bilinear (p x y : Decomposition R α ι) (a b c : α × α) :
    p.polarizedEntry x y a b c = p.bilinearEntry x y a b c + p.bilinearEntry y x a b c := by
  simp only [polarizedEntry, bilinearEntry, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem bilinearEntry_map {S : Type*} [CommRing S] (f : R →+* S) (p x y : Decomposition R α ι)
    (a b c : α × α) :
    (p.map f).bilinearEntry (x.map f) (y.map f) a b c = f (p.bilinearEntry x y a b c) := by
  simp [bilinearEntry, map, map_sum, map_add, map_mul]

/-- A linear combination of directions with coefficients in the ring. -/
def lc {n : ℕ} (z : Fin n → R) (V : Fin n → Decomposition R α ι) : Decomposition R α ι where
  u s a := ∑ i, z i * (V i).u s a
  v s a := ∑ i, z i * (V i).v s a
  w s a := ∑ i, z i * (V i).w s a

theorem bilinearEntry_lc_left {n : ℕ} (p y : Decomposition R α ι) (z : Fin n → R)
    (V : Fin n → Decomposition R α ι) (a b c : α × α) :
    p.bilinearEntry (lc z V) y a b c = ∑ i, z i * p.bilinearEntry (V i) y a b c := by
  simp only [bilinearEntry, lc, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bilinearEntry_lc_right {n : ℕ} (p x : Decomposition R α ι) (z : Fin n → R)
    (V : Fin n → Decomposition R α ι) (a b c : α × α) :
    p.bilinearEntry x (lc z V) a b c = ∑ i, z i * p.bilinearEntry x (V i) a b c := by
  simp only [bilinearEntry, lc, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticEntry_lc {n : ℕ} (p : Decomposition R α ι) (z : Fin n → R)
    (V : Fin n → Decomposition R α ι) (a b c : α × α) :
    p.quadraticEntry (lc z V) a b c =
      ∑ i, ∑ j, z i * z j * p.bilinearEntry (V i) (V j) a b c := by
  rw [quadraticEntry_eq_bilinear, bilinearEntry_lc_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [bilinearEntry_lc_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Perturbing a direction in `𝔪` by elements of `𝔪²` changes the quadratic term only
modulo `𝔪³`. -/
theorem quadraticEntry_sub_mem (m : Ideal R) (p x y : Decomposition R α ι)
    (hx : ∀ s a, x.u s a ∈ m ∧ x.v s a ∈ m ∧ x.w s a ∈ m)
    (hy : ∀ s a, y.u s a ∈ m ∧ y.v s a ∈ m ∧ y.w s a ∈ m)
    (hxy : ∀ s a, x.u s a - y.u s a ∈ m ^ 2 ∧ x.v s a - y.v s a ∈ m ^ 2 ∧
      x.w s a - y.w s a ∈ m ^ 2) (a b c : α × α) :
    p.quadraticEntry x a b c - p.quadraticEntry y a b c ∈ m ^ 3 := by
  have prod : ∀ {f g f' g' : R}, f ∈ m → g ∈ m → f' ∈ m → g' ∈ m →
      f - f' ∈ m ^ 2 → g - g' ∈ m ^ 2 → f * g - f' * g' ∈ m ^ 3 := by
    intro f g f' g' hf hg hf' hg' hff hgg
    have e : f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
    rw [e, pow_succ]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hff hg)
      (by rw [show f' * (g - g') = (g - g') * f' from mul_comm _ _]; exact Ideal.mul_mem_mul hgg hf')
  simp only [quadraticEntry, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun s _ => ?_
  have e : x.u s a * x.v s b * p.w s c + x.u s a * p.v s b * x.w s c +
      p.u s a * x.v s b * x.w s c -
      (y.u s a * y.v s b * p.w s c + y.u s a * p.v s b * y.w s c +
      p.u s a * y.v s b * y.w s c) =
      (x.u s a * x.v s b - y.u s a * y.v s b) * p.w s c +
      (x.u s a * x.w s c - y.u s a * y.w s c) * p.v s b +
      (x.v s b * x.w s c - y.v s b * y.w s c) * p.u s a := by ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;> refine Ideal.mul_mem_right _ _ ?_
  · exact prod (hx s a).1 (hx s b).2.1 (hy s a).1 (hy s b).2.1 (hxy s a).1 (hxy s b).2.1
  · exact prod (hx s a).1 (hx s c).2.2 (hy s a).1 (hy s c).2.2 (hxy s a).1 (hxy s c).2.2
  · exact prod (hx s b).2.1 (hx s c).2.2 (hy s b).2.1 (hy s c).2.2 (hxy s b).2.1 (hxy s c).2.2

end Brent.Decomposition

namespace Brent

/-- Split a double sum into its diagonal and its strictly ordered pairs. -/
theorem sum_sum_eq_ordered {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → Fin n → R) :
    ∑ i, ∑ j, f i j = ∑ i, ∑ j,
      (if i < j then f i j + f j i else if i = j then f i i else 0) := by
  have split : ∀ i j, f i j = (if i < j then f i j else 0) + (if i = j then f i i else 0) +
      (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, ne_of_gt h, not_lt_of_gt h]
  have swap : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f j i else 0) :=
    Finset.sum_comm
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if i = j then f i i else 0) +
          (if j < i then f i j else 0)) := by simp only [← split]
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if i = j then f i i else 0) +
          ∑ i, ∑ j, (if j < i then f i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if i = j then f i i else 0) +
          ∑ i, ∑ j, (if i < j then f j i else 0) := by rw [swap]
    _ = _ := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rcases lt_trichotomy i j with h | h | h
        · simp [h, ne_of_lt h]
        · subst h; simp
        · simp [not_lt_of_gt h, ne_of_gt h]

end Brent
