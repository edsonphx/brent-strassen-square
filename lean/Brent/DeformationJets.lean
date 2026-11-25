import Brent.Deformations
import Brent.Differential
import Mathlib.Data.Matrix.DualNumber

open scoped BigOperators
open TrivSqZeroExt

namespace Brent.Decomposition

variable {R α ι : Type*} [CommRing R]

/-- The specialization of a dual-number family at its base point. -/
def constantPart (d : Decomposition (DualNumber R) α ι) : Decomposition R α ι :=
  ⟨fun s a => (d.u s a).fst, fun s b => (d.v s b).fst, fun s c => (d.w s c).fst⟩

/-- Its first-order factor variation. -/
def tangentPart (d : Decomposition (DualNumber R) α ι) : Decomposition R α ι :=
  ⟨fun s a => (d.u s a).snd, fun s b => (d.v s b).snd, fun s c => (d.w s c).snd⟩

variable [Fintype ι]

theorem snd_entry (d : Decomposition (DualNumber R) α ι) (a b c : α × α) :
    (d.entry a b c).snd = d.constantPart.jacobianEntry d.tangentPart a b c := by
  simp only [entry, snd_sum, jacobianEntry, constantPart, tangentPart, DualNumber.snd_mul, fst_mul]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem tangent_satisfies_differential [DecidableEq α]
    (d : Decomposition (DualNumber R) α ι) (hs : d.Solves) (a b c : α × α) :
    d.constantPart.jacobianEntry d.tangentPart a b c = 0 := by
  rw [← snd_entry, hs a b c]
  unfold matrixMultiplicationEntry
  split_ifs <;> rfl

/-- The cross term of the quadratic part of a Brent equation. -/
def polarizedEntry (p x y : Decomposition R α ι) (a b c : α × α) : R :=
  ∑ s, (x.u s a * y.v s b * p.w s c + y.u s a * x.v s b * p.w s c +
    x.u s a * p.v s b * y.w s c + y.u s a * p.v s b * x.w s c +
    p.u s a * x.v s b * y.w s c + p.u s a * y.v s b * x.w s c)

theorem mixed_entry (d : Decomposition (DualNumber (DualNumber R)) α ι) (a b c : α × α) :
    (d.entry a b c).snd.snd =
      d.constantPart.constantPart.jacobianEntry d.tangentPart.tangentPart a b c +
      d.constantPart.constantPart.polarizedEntry d.tangentPart.constantPart
        d.constantPart.tangentPart a b c := by
  simp only [entry, snd_sum, jacobianEntry, polarizedEntry, constantPart, tangentPart,
    DualNumber.snd_mul, fst_mul, snd_add, fst_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- On an exact family with two independent dual-number parameters, the polar
quadratic term is the negative of a linearized term. -/
theorem mixed_entry_of_solution [DecidableEq α]
    (d : Decomposition (DualNumber (DualNumber R)) α ι) (hs : d.Solves) (a b c : α × α) :
    d.constantPart.constantPart.jacobianEntry d.tangentPart.tangentPart a b c +
      d.constantPart.constantPart.polarizedEntry d.tangentPart.constantPart
        d.constantPart.tangentPart a b c = 0 := by
  rw [← mixed_entry, hs a b c]
  unfold matrixMultiplicationEntry
  split_ifs <;> rfl

end Brent.Decomposition

namespace Brent

variable {R α : Type} [CommRing R] [Fintype α] [DecidableEq α]

/-- Every matrix direction gives a genuine invertible first-order change of basis. -/
def matrixJet (E : Matrix α α R) : (Matrix α α (DualNumber R))ˣ :=
  Units.map (Matrix.dualNumberEquiv (R := R) (n := α)).symm.toMonoidHom
    ⟨⟨1, E⟩, ⟨1, -E⟩, by ext <;> simp, by ext <;> simp⟩

@[simp]
theorem matrixJet_val (E : Matrix α α R) (i j : α) :
    (matrixJet E).val i j = ⟨(1 : Matrix α α R) i j, E i j⟩ := rfl

@[simp]
theorem matrixJet_inv (E : Matrix α α R) (i j : α) :
    (matrixJet E).inv i j = ⟨(1 : Matrix α α R) i j, (-E) i j⟩ := rfl

end Brent
