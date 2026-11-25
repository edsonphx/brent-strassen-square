import Brent.Formal.SmoothFamily
import Brent.SmoothL

/-!
# The left `t = 1` point as an integer block point

`pqInt` has identity global changes and scalings, and the blocks of §7 at `t = 1`:
`P₄ = I + E₁₂, R₄ = I + E₂₁, P₅ = I + E₂₁, R₅ = I + E₁₂`, all other blocks the identity.
Its left value is the stored point `SmoothL.pointDec`.
-/

namespace Brent.Formal

open Brent.SmoothL

def E12 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
def E12i : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]
def E21 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]
def E21i : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -1, 1]

def U12 : (Matrix (Fin 2) (Fin 2) ℤ)ˣ := ⟨E12, E12i, by decide, by decide⟩
def U21 : (Matrix (Fin 2) (Fin 2) ℤ)ˣ := ⟨E21, E21i, by decide, by decide⟩

/-- The block changes at `t = 1`. -/
def blockAtOne (l : Fin 7) (g : Fin 3) : (Matrix (Fin 2) (Fin 2) ℤ)ˣ :=
  if g = 0 then (if l = 4 then U12 else if l = 5 then U21 else 1)
  else if g = 2 then (if l = 4 then U21 else if l = 5 then U12 else 1)
  else 1

/-- The block point at `t = 1`. -/
def pqInt : FamilyParameters ℤ := ⟨fun _ => 1, blockAtOne, fun _ _ => 1⟩

theorem pqInt_global : pqInt.global = fun _ => 1 := rfl
theorem pqInt_scale : pqInt.scale = fun _ _ => 1 := rfl

theorem pqInt_left_u : ∀ s a, (FamilyParameters.blockFamily true pqInt.block).u s a = pointDec.u s a := by
  decide +kernel

theorem pqInt_left_v : ∀ s a, (FamilyParameters.blockFamily true pqInt.block).v s a = pointDec.v s a := by
  decide +kernel

theorem pqInt_left_w : ∀ s a, (FamilyParameters.blockFamily true pqInt.block).w s a = pointDec.w s a := by
  decide +kernel

/-- The left value at `t = 1` is the stored point. -/
theorem pqInt_value_left : pqInt.value true = pointDec := by
  rw [FamilyParameters.value_of_trivial true pqInt pqInt_global pqInt_scale]
  exact Decomposition.eq_of_components (funext fun s => funext (pqInt_left_u s))
    (funext fun s => funext (pqInt_left_v s)) (funext fun s => funext (pqInt_left_w s))

/-- Tangents at the left `t = 1` point, evaluated quickly from the stored point. -/
def tanLeft : GrpIdx → Var → ℤ
  | .inl (.inl (g, i, j)), (s, m, (a, b)) => pointDec.vertexUnitCoefficient g i j s m a b
  | .inl (.inr (s₀, c)), (s, m, (a, b)) =>
      FamilyParameters.termUnitCoefficient pointDec s₀ (decide (c = 1)) s m a b
  | .inr (l, g, i, j), (s, m, (a, b)) =>
      FamilyParameters.blockUnitCoefficientAt pqInt true l g i j s m a b

theorem qTangent_pqInt_left (w : GrpIdx) (x : Var) : qTangent pqInt true w x = tanLeft w x := by
  obtain ⟨s, m, a, b⟩ := x
  rcases w with (⟨g, i, j⟩ | ⟨s₀, c⟩) | ⟨l, g, i, j⟩ <;>
    simp only [qTangent, tanLeft, pqInt_value_left]

end Brent.Formal
