import Brent.Differential
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Second-order lifting (`paper.tex` lines 392–399)

DRAFT, NOT YET COMPILED.

"Substitute `p + t v + t² h` into the Brent map and work modulo `t³`. The coefficients of `t` and
`t²` are `J v` and `J h + Q₂(v)`. Thus `v ∈ ker J` lifts to order two precisely when `Q₂(v)` maps
to zero in `coker J`."

Over every commutative ring `R`: `jet p v h` is `p + X v + X² h` over `R[X]`;
`second_order_expansion` is the expansion with an explicit remainder in `X³`, and
`liftsToOrderTwo_iff` is the lifting criterion.
-/

open scoped BigOperators
open Polynomial

namespace Brent.Decomposition

variable {R α ι : Type*} [CommRing R] [Fintype ι]

/-- The Jacobian is linear in the direction. -/
theorem jacobianEntry_add (p d e : Decomposition R α ι) (a b c : α × α) :
    p.jacobianEntry ⟨d.u + e.u, d.v + e.v, d.w + e.w⟩ a b c =
      p.jacobianEntry d a b c + p.jacobianEntry e a b c := by
  unfold jacobianEntry
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.add_apply]
  ring

theorem jacobianEntry_neg (p d : Decomposition R α ι) (a b c : α × α) :
    p.jacobianEntry ⟨-d.u, -d.v, -d.w⟩ a b c = -p.jacobianEntry d a b c := by
  unfold jacobianEntry
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.neg_apply]
  ring

/-- The terms of degree at least three in `t` of one product of three quadratic jets. -/
def cubicTail (t a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) : R :=
  (a1 * b1 * c1 + a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b2 * c0 + a2 * b0 * c1 +
      a2 * b1 * c0) +
    t * (a0 * b2 * c2 + a2 * b0 * c2 + a2 * b2 * c0 + a1 * b1 * c2 + a1 * b2 * c1 +
      a2 * b1 * c1) +
    t ^ 2 * (a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1) + t ^ 3 * (a2 * b2 * c2)

theorem cubic_jet (t a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) :
    (a0 + t * a1 + t ^ 2 * a2) * (b0 + t * b1 + t ^ 2 * b2) * (c0 + t * c1 + t ^ 2 * c2) =
      a0 * b0 * c0 + t * (a1 * b0 * c0 + a0 * b1 * c0 + a0 * b0 * c1) +
        t ^ 2 * ((a2 * b0 * c0 + a0 * b2 * c0 + a0 * b0 * c2) +
          (a1 * b1 * c0 + a1 * b0 * c1 + a0 * b1 * c1)) +
        t ^ 3 * cubicTail t a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  unfold cubicTail
  ring

/-- `p + t v + t² h` for a scalar `t`. -/
def quadJet (p v h : Decomposition R α ι) (t : R) : Decomposition R α ι where
  u s a := p.u s a + t * v.u s a + t ^ 2 * h.u s a
  v s a := p.v s a + t * v.v s a + t ^ 2 * h.v s a
  w s a := p.w s a + t * v.w s a + t ^ 2 * h.w s a

/-- The remainder of the second-order expansion. -/
def tail (p v h : Decomposition R α ι) (t : R) (a b c : α × α) : R :=
  ∑ s, cubicTail t (p.u s a) (v.u s a) (h.u s a) (p.v s b) (v.v s b) (h.v s b)
    (p.w s c) (v.w s c) (h.w s c)

/-- Lines 394–396: the coefficients of `t` and `t²` are `J v` and `J h + Q₂(v)`. -/
theorem second_order_expansion (p v h : Decomposition R α ι) (t : R) (a b c : α × α) :
    (p.quadJet v h t).entry a b c =
      p.entry a b c + t * p.jacobianEntry v a b c +
        t ^ 2 * (p.jacobianEntry h a b c + p.quadraticEntry v a b c) +
        t ^ 3 * p.tail v h t a b c := by
  unfold entry jacobianEntry quadraticEntry tail quadJet
  simp only [cubic_jet, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- Constant coefficients over `R[X]`. -/
def constX (d : Decomposition R α ι) : Decomposition R[X] α ι :=
  ⟨fun s a => C (d.u s a), fun s a => C (d.v s a), fun s a => C (d.w s a)⟩

/-- `p + X v + X² h` over `R[X]`. -/
def jet (p v h : Decomposition R α ι) : Decomposition R[X] α ι :=
  (constX p).quadJet (constX v) (constX h) X

theorem entry_constX (d : Decomposition R α ι) (a b c : α × α) :
    (constX d).entry a b c = C (d.entry a b c) := by
  simp [entry, constX, map_sum, map_mul]

theorem jacobianEntry_constX (p d : Decomposition R α ι) (a b c : α × α) :
    (constX p).jacobianEntry (constX d) a b c = C (p.jacobianEntry d a b c) := by
  simp [jacobianEntry, constX, map_sum, map_mul, map_add]

theorem quadraticEntry_constX (p d : Decomposition R α ι) (a b c : α × α) :
    (constX p).quadraticEntry (constX d) a b c = C (p.quadraticEntry d a b c) := by
  simp [quadraticEntry, constX, map_sum, map_mul, map_add]

variable [DecidableEq α]

/-- `v` lifts to order two: some `h` makes `p + X v + X² h` a solution modulo `X³`. -/
def LiftsToOrderTwo (p v : Decomposition R α ι) : Prop :=
  ∃ h : Decomposition R α ι, ∀ a b c,
    X ^ 3 ∣ (jet p v h).entry a b c - C (matrixMultiplicationEntry R a b c)

/-- `Q₂(v)` lies in the image of `J`. -/
def QuadraticInImage (p v : Decomposition R α ι) : Prop :=
  ∃ h : Decomposition R α ι, ∀ a b c, p.jacobianEntry h a b c = p.quadraticEntry v a b c

private theorem coeff_two_of_dvd {c : R} {q : R[X]} (h : X ^ 3 ∣ X ^ 2 * C c + X ^ 3 * q) :
    c = 0 := by
  obtain ⟨r, hr⟩ := h
  have := congrArg (fun f : R[X] => f.coeff 2) hr
  simpa [coeff_X_pow_mul'] using this

/-- Lines 396–397: for a solution `p` and `v ∈ ker J`, `v` lifts to order two precisely when
`Q₂(v)` maps to zero in `coker J`. -/
theorem liftsToOrderTwo_iff {p v : Decomposition R α ι} (hp : p.Solves)
    (hv : ∀ a b c, p.jacobianEntry v a b c = 0) :
    p.LiftsToOrderTwo v ↔ p.QuadraticInImage v := by
  have key : ∀ h : Decomposition R α ι, ∀ a b c,
      (jet p v h).entry a b c - C (matrixMultiplicationEntry R a b c) =
        X ^ 2 * C (p.jacobianEntry h a b c + p.quadraticEntry v a b c) +
          X ^ 3 * (constX p).tail (constX v) (constX h) X a b c := by
    intro h a b c
    rw [jet, second_order_expansion, entry_constX, jacobianEntry_constX, jacobianEntry_constX,
      quadraticEntry_constX, hp, hv, map_zero, mul_zero, add_zero, map_add]
    ring
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨-h.u, -h.v, -h.w⟩, fun a b c => ?_⟩
    have h3 := hh a b c
    rw [key] at h3
    have := coeff_two_of_dvd h3
    rw [jacobianEntry_neg]
    linear_combination -this
  · rintro ⟨h, hh⟩
    refine ⟨⟨-h.u, -h.v, -h.w⟩, fun a b c => ?_⟩
    rw [key, jacobianEntry_neg, hh, neg_add_cancel, map_zero, mul_zero, zero_add]
    exact dvd_mul_right _ _

end Brent.Decomposition
