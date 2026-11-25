import Brent.Formal.SmoothLeftData

/-!
# The one-parameter curves from the recursive point to the smooth points (§7, lines 621–636)

Over any commutative ring `R` and for any `t : R`, the matrices `I + tE₁₂` and `I + tE₂₁` have
determinant one and inverses `I − tE₁₂`, `I − tE₂₁`. Using them in blocks 4 and 5 (and the
identity elsewhere) gives block parameters `curve t`. At `t = 0` both orientations give the
recursive point `p`. At `t = 1` they give the points `q_L`, `q_R` of `pqInt`.
-/

namespace Brent.Formal

variable {R : Type} [CommRing R]

/-- `I + tE₁₂`. -/
def e12 (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, t; 0, 1]

/-- `I + tE₂₁`. -/
def e21 (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; t, 1]

theorem det_e12 (t : R) : (e12 t).det = 1 := by simp [e12, Matrix.det_fin_two]

theorem det_e21 (t : R) : (e21 t).det = 1 := by simp [e21, Matrix.det_fin_two]

theorem e12_mul_neg (t : R) : e12 t * e12 (-t) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e12, Matrix.mul_apply, Fin.sum_univ_two]

theorem e12_neg_mul (t : R) : e12 (-t) * e12 t = 1 := by
  simpa using e12_mul_neg (-t)

theorem e21_mul_neg (t : R) : e21 t * e21 (-t) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e21, Matrix.mul_apply, Fin.sum_univ_two]

theorem e21_neg_mul (t : R) : e21 (-t) * e21 t = 1 := by
  simpa using e21_mul_neg (-t)

/-- `I + tE₁₂` as a unit, with inverse `I − tE₁₂`. -/
def u12 (t : R) : (Matrix (Fin 2) (Fin 2) R)ˣ := ⟨e12 t, e12 (-t), e12_mul_neg t, e12_neg_mul t⟩

/-- `I + tE₂₁` as a unit, with inverse `I − tE₂₁`. -/
def u21 (t : R) : (Matrix (Fin 2) (Fin 2) R)ˣ := ⟨e21 t, e21 (-t), e21_mul_neg t, e21_neg_mul t⟩

/-- The block changes of the curve (table on lines 626–631). -/
def curveBlock (t : R) (l : Fin 7) (g : Fin 3) : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  if g = 0 then (if l = 4 then u12 t else if l = 5 then u21 t else 1)
  else if g = 2 then (if l = 4 then u21 t else if l = 5 then u12 t else 1)
  else 1

/-- The curve in parameter space: identity global action and scalings. -/
def curve (t : R) : FamilyParameters R := ⟨fun _ => 1, curveBlock t, fun _ _ => 1⟩

theorem u12_zero : u12 (0 : R) = 1 := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem u21_zero : u21 (0 : R) = 1 := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem curve_zero : curve (0 : R) = FamilyParameters.one R := by
  simp only [curve, FamilyParameters.one, FamilyParameters.mk.injEq, true_and, and_true]
  funext l g
  simp [curveBlock, u12_zero, u21_zero]

/-- **At `t = 0` both curves pass through the recursive point.** -/
theorem curve_value_zero (left : Bool) : (curve (0 : R)).value left = strassenSquare R := by
  rw [curve_zero, FamilyParameters.value_one]

/-- **At `t = 1` the curve is the block point `pqInt` (mapped to `R`).** -/
theorem curve_one : curve (1 : R) = pqInt.map (Int.castRingHom R) := by
  simp only [curve, pqInt, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; exact (map_one _).symm
  · funext l g
    apply Units.ext
    ext i j
    simp only [curveBlock, blockAtOne]
    split_ifs <;> fin_cases i <;> fin_cases j <;>
      simp [u12, u21, U12, U21, e12, e21, E12, E21, Units.coe_map]
  · funext s c; exact (map_one _).symm

/-- Every point of the curve is a solution, in both orientations. -/
theorem curve_solves (left : Bool) (t : R) : ((curve t).value left).Solves :=
  FamilyParameters.value_solves left (curve t)

end Brent.Formal
