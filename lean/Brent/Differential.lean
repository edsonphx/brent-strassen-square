import Brent.CoordinateRing

open scoped BigOperators

namespace Brent.Decomposition

variable {R α ι : Type*} [CommRing R] [Fintype ι]

/-- Coefficient of the first-order perturbation of a Brent entry. -/
def jacobianEntry (p d : Decomposition R α ι) (a b c : α × α) : R :=
  ∑ s, (d.u s a * p.v s b * p.w s c +
    p.u s a * d.v s b * p.w s c +
    p.u s a * p.v s b * d.w s c)

/-- Quadratic term in the translated Brent equations at `p`. -/
def quadraticEntry (p d : Decomposition R α ι) (a b c : α × α) : R :=
  ∑ s, (d.u s a * d.v s b * p.w s c +
    d.u s a * p.v s b * d.w s c +
    p.u s a * d.v s b * d.w s c)

def line (p d : Decomposition R α ι) (t : R) : Decomposition R α ι where
  u s a := p.u s a + t * d.u s a
  v s a := p.v s a + t * d.v s a
  w s a := p.w s a + t * d.w s a

/-- The exact cubic expansion that determines both the Jacobian and the quadratic obstruction. -/
theorem entry_line (p d : Decomposition R α ι) (t : R) (a b c : α × α) :
    (p.line d t).entry a b c = p.entry a b c + t * p.jacobianEntry d a b c +
      t ^ 2 * p.quadraticEntry d a b c + t ^ 3 * d.entry a b c := by
  unfold entry jacobianEntry quadraticEntry
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, line]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- A standard basis perturbation in a single variable. -/
def coordinateDirection [DecidableEq α] [DecidableEq ι]
    (x : Variable α ι) : Decomposition R α ι where
  u s a := if x = (s, .u, a) then 1 else 0
  v s a := if x = (s, .v, a) then 1 else 0
  w s a := if x = (s, .w, a) then 1 else 0

/-- Columns are in the order fixed by `Variable`. Each is evaluated by changing one factor. -/
def jacobianColumn [DecidableEq α] [DecidableEq ι] (p : Decomposition R α ι)
    (x : Variable α ι) (a b c : α × α) : R :=
  p.jacobianEntry (coordinateDirection x) a b c

theorem jacobianColumn_eq [DecidableEq α] [DecidableEq ι] (p : Decomposition R α ι)
    (s : ι) (m : Mode) (x a b c : α × α) :
    p.jacobianColumn (s, m, x) a b c =
      match m with
      | .u => if x = a then p.v s b * p.w s c else 0
      | .v => if x = b then p.u s a * p.w s c else 0
      | .w => if x = c then p.u s a * p.v s b else 0 := by
  cases m <;>
    simp [jacobianColumn, jacobianEntry, coordinateDirection, Prod.mk.injEq,
      ite_and, ite_mul, mul_ite, Finset.sum_ite_eq]

end Brent.Decomposition
