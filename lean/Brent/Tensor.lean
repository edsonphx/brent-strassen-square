import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Brent

/-- The three factors are in input, input, output order. The output is not transposed. -/
structure Decomposition (R : Type*) (α : Type*) (ι : Type*) where
  u : ι → (α × α) → R
  v : ι → (α × α) → R
  w : ι → (α × α) → R

/-- Coordinates of the matrix multiplication tensor in row-major matrix coordinates. -/
def matrixMultiplicationEntry (R : Type*) [DecidableEq α] [Zero R] [One R]
    (a b c : α × α) : R :=
  if a.2 = b.1 ∧ a.1 = c.1 ∧ b.2 = c.2 then 1 else 0

namespace Decomposition

variable {R α β ι κ : Type*}

def entry [CommRing R] [Fintype ι] (d : Decomposition R α ι) (a b c : α × α) : R :=
  ∑ s, d.u s a * d.v s b * d.w s c

def Solves [CommRing R] [DecidableEq α] [Fintype ι] (d : Decomposition R α ι) : Prop :=
  ∀ a b c, d.entry a b c = matrixMultiplicationEntry R a b c

/-- Split the row and column indices of a Kronecker product matrix. -/
def outer (a : (α × β) × (α × β)) : α × α := (a.1.1, a.2.1)

def inner (a : (α × β) × (α × β)) : β × β := (a.1.2, a.2.2)

/-- With a fixed outer summand, the inner decomposition may vary independently. -/
def recursiveLeft [Mul R] (d : Decomposition R α ι) (e : ι → Decomposition R β κ) :
    Decomposition R (α × β) (ι × κ) where
  u s a := d.u s.1 (outer a) * (e s.1).u s.2 (inner a)
  v s a := d.v s.1 (outer a) * (e s.1).v s.2 (inner a)
  w s a := d.w s.1 (outer a) * (e s.1).w s.2 (inner a)

/-- With a fixed inner summand, the outer decomposition may vary independently. -/
def recursiveRight [Mul R] (d : κ → Decomposition R α ι) (e : Decomposition R β κ) :
    Decomposition R (α × β) (ι × κ) where
  u s a := (d s.2).u s.1 (outer a) * e.u s.2 (inner a)
  v s a := (d s.2).v s.1 (outer a) * e.v s.2 (inner a)
  w s a := (d s.2).w s.1 (outer a) * e.w s.2 (inner a)

theorem matrixMultiplicationEntry_prod [CommRing R] [DecidableEq α] [DecidableEq β]
    (a b c : (α × β) × (α × β)) :
    matrixMultiplicationEntry R a b c =
      matrixMultiplicationEntry R (outer a) (outer b) (outer c) *
      matrixMultiplicationEntry R (inner a) (inner b) (inner c) := by
  unfold matrixMultiplicationEntry outer inner
  simp only [Prod.ext_iff]
  split_ifs <;> simp_all [and_assoc, and_left_comm, and_comm]

theorem solves_recursiveLeft [CommRing R] [DecidableEq α] [DecidableEq β]
    [Fintype ι] [Fintype κ] {d : Decomposition R α ι} {e : ι → Decomposition R β κ}
    (hd : d.Solves) (he : ∀ i, (e i).Solves) : (d.recursiveLeft e).Solves := by
  intro a b c
  rw [matrixMultiplicationEntry_prod]
  unfold entry
  rw [Fintype.sum_prod_type]
  simp only [recursiveLeft]
  simp_rw [show ∀ (p q r x y z : R), p*x*(q*y)*(r*z) = (p*q*r)*(x*y*z) by
    intros; ring, ← Finset.mul_sum]
  change (∑ i, d.u i (outer a) * d.v i (outer b) * d.w i (outer c) *
    (e i).entry (inner a) (inner b) (inner c)) = _
  simp_rw [show ∀ i, (e i).entry (inner a) (inner b) (inner c) =
    matrixMultiplicationEntry R (inner a) (inner b) (inner c) from
      fun i => he i (inner a) (inner b) (inner c), ← Finset.sum_mul]
  exact congrArg (· * matrixMultiplicationEntry R (inner a) (inner b) (inner c))
    (hd (outer a) (outer b) (outer c))

theorem solves_recursiveRight [CommRing R] [DecidableEq α] [DecidableEq β]
    [Fintype ι] [Fintype κ] {d : κ → Decomposition R α ι} {e : Decomposition R β κ}
    (hd : ∀ j, (d j).Solves) (he : e.Solves) : (recursiveRight d e).Solves := by
  intro a b c
  rw [matrixMultiplicationEntry_prod]
  unfold entry
  rw [Fintype.sum_prod_type_right]
  simp only [recursiveRight]
  simp_rw [show ∀ (p q r x y z : R), p*x*(q*y)*(r*z) = (p*q*r)*(x*y*z) by
    intros; ring, ← Finset.sum_mul]
  change (∑ j, (d j).entry (outer a) (outer b) (outer c) *
    (e.u j (inner a) * e.v j (inner b) * e.w j (inner c))) = _
  simp_rw [show ∀ j, (d j).entry (outer a) (outer b) (outer c) =
    matrixMultiplicationEntry R (outer a) (outer b) (outer c) from
      fun j => hd j (outer a) (outer b) (outer c), ← Finset.mul_sum]
  exact congrArg (matrixMultiplicationEntry R (outer a) (outer b) (outer c) * ·)
    (he (inner a) (inner b) (inner c))

/-- Map a decomposition along a coefficient ring homomorphism. -/
def map {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (d : Decomposition R α ι) :
    Decomposition S α ι where
  u s a := f (d.u s a)
  v s a := f (d.v s a)
  w s a := f (d.w s a)

theorem solves_map {S : Type*} [CommRing R] [CommRing S] [DecidableEq α] [Fintype ι]
    (f : R →+* S) {d : Decomposition R α ι} (h : d.Solves) : (d.map f).Solves := by
  intro a b c
  have eq := congrArg f (h a b c)
  simp only [entry, map_sum, map_mul] at eq
  simpa only [entry, map, matrixMultiplicationEntry, apply_ite f, map_zero, map_one] using eq

end Decomposition
end Brent
