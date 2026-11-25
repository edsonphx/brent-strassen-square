import Brent.FamilyTangents
import Brent.Formal.CoordinateChange
import Brent.Formal.FormalDimension
import Brent.Formal.PowerSeriesDimension
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The group orbit has dimension 143 (§3)

The isotropy group `GL₄³` of the 4×4 matrix multiplication tensor together with the 98 term
rescalings acts on the Strassen-square point. Centered at the identity, this gives the
146-parameter orbit map `Φ_orb : (k^146, 0) → (V, p)`, whose comorphism is a `k`-algebra map
`Â → k⟦146⟧`. It factors through `A` and `Â` because the orbit consists of solutions.

* **Upper bound.** The three central scalings `K₃` lie in the kernel of `dΦ_orb(0)`, so
  `rank dΦ_orb(0) ≤ 143`.
* **Lower bound.** Gauge-fix the three coordinates `(g, (1,1), (1,1))`. The resulting
  `143 × 143` Jacobian minor is upper triangular with diagonal `±1`; the kernel checks this over
  `ℤ`, so it is invertible over every field. By the formal inverse function theorem the
  gauge-fixed orbit map `Â → k⟦c⟧` (143 variables) is surjective. It is the restriction of the
  146-parameter orbit map to the gauge slice.

Hence `rank dΦ_orb(0) = 143`.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries

set_option linter.unusedSectionVars false

/-- The orbit parameters: matrix units of the three global factors and the two compensated
rescalings of each of the 49 terms (`48 + 98 = 146`). -/
abbrev GIdx := (Fin 3 × SquareVertex × SquareVertex) ⊕ (SquareSummand × Fin 2)

theorem card_GIdx : Fintype.card GIdx = 146 := rfl

/-! ### The Jacobian rows -/

/-- The derivative of the orbit map along a parameter, for a decomposition `d`. -/
def jacRow {R : Type} [CommRing R] (d : Decomposition R SquareVertex SquareSummand) :
    GIdx → Var → R
  | .inl (g, i, j), (s, m, (a, b)) => d.vertexUnitCoefficient g i j s m a b
  | .inr (t, c), (s, m, (a, b)) => FamilyParameters.termUnitCoefficient d t (decide (c = 1)) s m a b

theorem jacRow_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (d : Decomposition R SquareVertex SquareSummand) (w : GIdx) (x : Var) :
    jacRow (d.map f) w x = f (jacRow d w x) := by
  obtain ⟨s, m, a, b⟩ := x
  rcases w with ⟨g, i, j⟩ | ⟨t, c⟩
  · cases m <;> simp [jacRow, Decomposition.vertexUnitCoefficient, Decomposition.map, apply_ite f]
  · cases m <;> simp [jacRow, FamilyParameters.termUnitCoefficient, Decomposition.map, apply_ite f]

theorem jacRow_cast (k : Type) [Field k] (w : GIdx) (x : Var) :
    jacRow (strassenSquare k) w x = ((jacRow strassenSquareInt w x : ℤ) : k) :=
  jacRow_map (Int.castRingHom k) strassenSquareInt w x

/-! ### The certified minor -/

def minorRows : List GIdx := [
  .inl (0, (0, 0), (0, 1)),
  .inl (0, (0, 0), (1, 0)),
  .inl (0, (0, 0), (1, 1)),
  .inl (0, (0, 1), (0, 0)),
  .inl (0, (0, 1), (1, 0)),
  .inl (0, (0, 1), (1, 1)),
  .inl (0, (1, 0), (0, 0)),
  .inl (0, (1, 0), (0, 1)),
  .inl (0, (1, 0), (1, 1)),
  .inl (0, (1, 1), (0, 0)),
  .inl (0, (1, 1), (0, 1)),
  .inl (0, (1, 1), (1, 0)),
  .inl (1, (0, 0), (0, 1)),
  .inl (1, (0, 0), (1, 0)),
  .inl (1, (0, 0), (1, 1)),
  .inl (1, (0, 1), (0, 0)),
  .inl (1, (0, 1), (1, 0)),
  .inl (1, (0, 1), (1, 1)),
  .inl (1, (1, 0), (0, 0)),
  .inl (1, (1, 0), (0, 1)),
  .inl (1, (1, 0), (1, 1)),
  .inl (1, (1, 1), (0, 0)),
  .inl (1, (1, 1), (0, 1)),
  .inl (1, (1, 1), (1, 0)),
  .inl (2, (0, 0), (0, 1)),
  .inl (2, (0, 0), (1, 0)),
  .inl (2, (0, 0), (1, 1)),
  .inl (2, (0, 1), (0, 0)),
  .inl (2, (0, 1), (1, 0)),
  .inl (2, (0, 1), (1, 1)),
  .inl (2, (1, 0), (0, 0)),
  .inl (2, (1, 0), (0, 1)),
  .inl (2, (1, 0), (1, 1)),
  .inl (2, (1, 1), (0, 0)),
  .inl (2, (1, 1), (0, 1)),
  .inl (2, (1, 1), (1, 0)),
  .inr ((0, 0), 0),
  .inr ((0, 0), 1),
  .inr ((0, 1), 0),
  .inl (2, (1, 0), (1, 0)),
  .inl (0, (1, 0), (1, 0)),
  .inl (1, (1, 0), (1, 0)),
  .inr ((0, 1), 1),
  .inr ((0, 2), 0),
  .inr ((0, 2), 1),
  .inr ((0, 3), 0),
  .inr ((0, 3), 1),
  .inr ((0, 4), 0),
  .inr ((0, 4), 1),
  .inr ((0, 5), 0),
  .inr ((0, 5), 1),
  .inr ((0, 6), 0),
  .inr ((0, 6), 1),
  .inr ((1, 0), 0),
  .inl (2, (0, 0), (0, 0)),
  .inl (0, (0, 0), (0, 0)),
  .inl (0, (0, 1), (0, 1)),
  .inl (1, (0, 0), (0, 0)),
  .inl (1, (0, 1), (0, 1)),
  .inl (2, (0, 1), (0, 1)),
  .inr ((1, 0), 1),
  .inr ((1, 1), 0),
  .inr ((1, 1), 1),
  .inr ((1, 2), 0),
  .inr ((1, 2), 1),
  .inr ((1, 3), 0),
  .inr ((1, 3), 1),
  .inr ((1, 4), 0),
  .inr ((1, 4), 1),
  .inr ((1, 5), 0),
  .inr ((1, 5), 1),
  .inr ((1, 6), 0),
  .inr ((1, 6), 1),
  .inr ((2, 0), 0),
  .inr ((2, 0), 1),
  .inr ((2, 1), 0),
  .inr ((2, 1), 1),
  .inr ((2, 2), 0),
  .inr ((2, 2), 1),
  .inr ((2, 3), 0),
  .inr ((2, 3), 1),
  .inr ((2, 4), 0),
  .inr ((2, 4), 1),
  .inr ((2, 5), 0),
  .inr ((2, 5), 1),
  .inr ((2, 6), 0),
  .inr ((2, 6), 1),
  .inr ((3, 0), 0),
  .inr ((3, 0), 1),
  .inr ((3, 1), 0),
  .inr ((3, 1), 1),
  .inr ((3, 2), 0),
  .inr ((3, 2), 1),
  .inr ((3, 3), 0),
  .inr ((3, 3), 1),
  .inr ((3, 4), 0),
  .inr ((3, 4), 1),
  .inr ((3, 5), 0),
  .inr ((3, 5), 1),
  .inr ((3, 6), 0),
  .inr ((3, 6), 1),
  .inr ((4, 0), 0),
  .inr ((4, 0), 1),
  .inr ((4, 1), 0),
  .inr ((4, 1), 1),
  .inr ((4, 2), 0),
  .inr ((4, 2), 1),
  .inr ((4, 3), 0),
  .inr ((4, 3), 1),
  .inr ((4, 4), 0),
  .inr ((4, 4), 1),
  .inr ((4, 5), 0),
  .inr ((4, 5), 1),
  .inr ((4, 6), 0),
  .inr ((4, 6), 1),
  .inr ((5, 0), 0),
  .inr ((5, 0), 1),
  .inr ((5, 1), 0),
  .inr ((5, 1), 1),
  .inr ((5, 2), 0),
  .inr ((5, 2), 1),
  .inr ((5, 3), 0),
  .inr ((5, 3), 1),
  .inr ((5, 4), 0),
  .inr ((5, 4), 1),
  .inr ((5, 5), 0),
  .inr ((5, 5), 1),
  .inr ((5, 6), 0),
  .inr ((5, 6), 1),
  .inr ((6, 0), 0),
  .inr ((6, 0), 1),
  .inr ((6, 1), 0),
  .inr ((6, 1), 1),
  .inr ((6, 2), 0),
  .inr ((6, 2), 1),
  .inr ((6, 3), 0),
  .inr ((6, 3), 1),
  .inr ((6, 4), 0),
  .inr ((6, 4), 1),
  .inr ((6, 5), 0),
  .inr ((6, 5), 1),
  .inr ((6, 6), 0),
  .inr ((6, 6), 1)]

def minorCols : List Var := [
  ((0, 1), .w, ((0, 0), (0, 0))),
  ((1, 0), .w, ((0, 0), (0, 0))),
  ((0, 1), .w, ((0, 0), (1, 0))),
  ((0, 1), .u, ((0, 0), (0, 0))),
  ((0, 1), .u, ((1, 0), (0, 0))),
  ((1, 0), .w, ((0, 1), (0, 1))),
  ((1, 0), .u, ((0, 0), (0, 0))),
  ((0, 1), .w, ((1, 0), (0, 0))),
  ((0, 1), .w, ((1, 0), (1, 0))),
  ((0, 1), .u, ((0, 0), (1, 0))),
  ((1, 0), .u, ((0, 1), (0, 1))),
  ((0, 1), .u, ((1, 0), (1, 0))),
  ((0, 0), .u, ((0, 1), (0, 0))),
  ((0, 0), .u, ((1, 0), (0, 0))),
  ((0, 0), .u, ((1, 1), (0, 0))),
  ((0, 0), .u, ((0, 0), (0, 1))),
  ((0, 0), .u, ((1, 0), (0, 1))),
  ((0, 0), .u, ((1, 1), (0, 1))),
  ((0, 0), .u, ((0, 0), (1, 0))),
  ((0, 0), .u, ((0, 1), (1, 0))),
  ((0, 0), .u, ((1, 1), (1, 0))),
  ((0, 0), .u, ((0, 0), (1, 1))),
  ((0, 0), .u, ((0, 1), (1, 1))),
  ((0, 0), .u, ((1, 0), (1, 1))),
  ((0, 0), .v, ((0, 1), (0, 0))),
  ((0, 0), .v, ((1, 0), (0, 0))),
  ((0, 0), .v, ((1, 1), (0, 0))),
  ((0, 0), .v, ((0, 0), (0, 1))),
  ((0, 0), .v, ((1, 0), (0, 1))),
  ((0, 0), .v, ((1, 1), (0, 1))),
  ((0, 0), .v, ((0, 0), (1, 0))),
  ((0, 0), .v, ((0, 1), (1, 0))),
  ((0, 0), .v, ((1, 1), (1, 0))),
  ((0, 0), .v, ((0, 0), (1, 1))),
  ((0, 0), .v, ((0, 1), (1, 1))),
  ((0, 0), .v, ((1, 0), (1, 1))),
  ((0, 0), .w, ((1, 1), (1, 1))),
  ((0, 0), .u, ((1, 1), (1, 1))),
  ((0, 1), .w, ((1, 1), (1, 1))),
  ((0, 1), .w, ((1, 1), (1, 0))),
  ((0, 0), .w, ((1, 0), (1, 0))),
  ((0, 0), .u, ((1, 0), (1, 0))),
  ((0, 1), .u, ((1, 1), (1, 0))),
  ((0, 2), .w, ((1, 0), (1, 1))),
  ((0, 2), .u, ((1, 0), (1, 0))),
  ((0, 3), .w, ((1, 0), (1, 0))),
  ((0, 3), .u, ((1, 1), (1, 1))),
  ((0, 4), .w, ((1, 0), (1, 0))),
  ((0, 4), .u, ((1, 0), (1, 0))),
  ((0, 5), .w, ((1, 1), (1, 1))),
  ((0, 5), .u, ((1, 0), (1, 0))),
  ((0, 6), .w, ((1, 0), (1, 0))),
  ((0, 6), .u, ((1, 0), (1, 1))),
  ((1, 0), .w, ((1, 0), (1, 0))),
  ((1, 0), .w, ((1, 0), (0, 0))),
  ((0, 0), .w, ((0, 0), (0, 0))),
  ((0, 1), .w, ((0, 1), (0, 0))),
  ((0, 0), .u, ((0, 0), (0, 0))),
  ((0, 0), .u, ((0, 1), (0, 1))),
  ((0, 0), .v, ((0, 1), (0, 1))),
  ((1, 0), .u, ((1, 0), (0, 0))),
  ((1, 1), .w, ((1, 1), (0, 0))),
  ((1, 1), .u, ((1, 1), (0, 0))),
  ((1, 2), .w, ((1, 0), (0, 1))),
  ((1, 2), .u, ((1, 0), (0, 0))),
  ((1, 3), .w, ((1, 0), (0, 0))),
  ((1, 3), .u, ((1, 1), (0, 1))),
  ((1, 4), .w, ((1, 0), (0, 0))),
  ((1, 4), .u, ((1, 0), (0, 0))),
  ((1, 5), .w, ((1, 1), (0, 1))),
  ((1, 5), .u, ((1, 0), (0, 0))),
  ((1, 6), .w, ((1, 0), (0, 0))),
  ((1, 6), .u, ((1, 0), (0, 1))),
  ((2, 0), .w, ((0, 0), (1, 0))),
  ((2, 0), .u, ((0, 0), (0, 0))),
  ((2, 1), .w, ((0, 1), (1, 0))),
  ((2, 1), .u, ((0, 1), (0, 0))),
  ((2, 2), .w, ((0, 0), (1, 1))),
  ((2, 2), .u, ((0, 0), (0, 0))),
  ((2, 3), .w, ((0, 0), (1, 0))),
  ((2, 3), .u, ((0, 1), (0, 1))),
  ((2, 4), .w, ((0, 0), (1, 0))),
  ((2, 4), .u, ((0, 0), (0, 0))),
  ((2, 5), .w, ((0, 1), (1, 1))),
  ((2, 5), .u, ((0, 0), (0, 0))),
  ((2, 6), .w, ((0, 0), (1, 0))),
  ((2, 6), .u, ((0, 0), (0, 1))),
  ((3, 0), .w, ((0, 0), (0, 0))),
  ((3, 0), .u, ((1, 0), (1, 0))),
  ((3, 1), .w, ((0, 1), (0, 0))),
  ((3, 1), .u, ((1, 1), (1, 0))),
  ((3, 2), .w, ((0, 0), (0, 1))),
  ((3, 2), .u, ((1, 0), (1, 0))),
  ((3, 3), .w, ((0, 0), (0, 0))),
  ((3, 3), .u, ((1, 1), (1, 1))),
  ((3, 4), .w, ((0, 0), (0, 0))),
  ((3, 4), .u, ((1, 0), (1, 0))),
  ((3, 5), .w, ((0, 1), (0, 1))),
  ((3, 5), .u, ((1, 0), (1, 0))),
  ((3, 6), .w, ((0, 0), (0, 0))),
  ((3, 6), .u, ((1, 0), (1, 1))),
  ((4, 0), .w, ((0, 0), (0, 0))),
  ((4, 0), .u, ((0, 0), (0, 0))),
  ((4, 1), .w, ((0, 1), (0, 0))),
  ((4, 1), .u, ((0, 1), (0, 0))),
  ((4, 2), .w, ((0, 0), (0, 1))),
  ((4, 2), .u, ((0, 0), (0, 0))),
  ((4, 3), .w, ((0, 0), (0, 0))),
  ((4, 3), .u, ((0, 1), (0, 1))),
  ((4, 4), .w, ((0, 0), (0, 0))),
  ((4, 4), .u, ((0, 0), (0, 0))),
  ((4, 5), .w, ((0, 1), (0, 1))),
  ((4, 5), .u, ((0, 0), (0, 0))),
  ((4, 6), .w, ((0, 0), (0, 0))),
  ((4, 6), .u, ((0, 0), (0, 1))),
  ((5, 0), .w, ((1, 0), (1, 0))),
  ((5, 0), .u, ((0, 0), (0, 0))),
  ((5, 1), .w, ((1, 1), (1, 0))),
  ((5, 1), .u, ((0, 1), (0, 0))),
  ((5, 2), .w, ((1, 0), (1, 1))),
  ((5, 2), .u, ((0, 0), (0, 0))),
  ((5, 3), .w, ((1, 0), (1, 0))),
  ((5, 3), .u, ((0, 1), (0, 1))),
  ((5, 4), .w, ((1, 0), (1, 0))),
  ((5, 4), .u, ((0, 0), (0, 0))),
  ((5, 5), .w, ((1, 1), (1, 1))),
  ((5, 5), .u, ((0, 0), (0, 0))),
  ((5, 6), .w, ((1, 0), (1, 0))),
  ((5, 6), .u, ((0, 0), (0, 1))),
  ((6, 0), .w, ((0, 0), (0, 0))),
  ((6, 0), .u, ((0, 0), (1, 0))),
  ((6, 1), .w, ((0, 1), (0, 0))),
  ((6, 1), .u, ((0, 1), (1, 0))),
  ((6, 2), .w, ((0, 0), (0, 1))),
  ((6, 2), .u, ((0, 0), (1, 0))),
  ((6, 3), .w, ((0, 0), (0, 0))),
  ((6, 3), .u, ((0, 1), (1, 1))),
  ((6, 4), .w, ((0, 0), (0, 0))),
  ((6, 4), .u, ((0, 0), (1, 0))),
  ((6, 5), .w, ((0, 1), (0, 1))),
  ((6, 5), .u, ((0, 0), (1, 0))),
  ((6, 6), .w, ((0, 0), (0, 0))),
  ((6, 6), .u, ((0, 0), (1, 1)))]

/-- The 143 gauge-fixed parameters, in pivot order. -/
def rowsA (i : Fin 143) : GIdx := minorRows.getD i.val (.inr ((0, 0), 0))

/-- The 143 Brent coordinates of the minor, in pivot order. -/
def colsA (i : Fin 143) : Var := minorCols.getD i.val ((0, 0), .u, ((0, 0), (0, 0)))

set_option maxRecDepth 100000 in
/-- **The minor is upper triangular** (checked by the kernel over `ℤ`). -/
theorem minor_upper : ∀ i j : Fin 143, j < i → jacRow strassenSquareInt (rowsA i) (colsA j) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Its diagonal is `±1`**, a unit in every characteristic. -/
theorem minor_diag : ∀ i : Fin 143, jacRow strassenSquareInt (rowsA i) (colsA i) = 1 ∨
    jacRow strassenSquareInt (rowsA i) (colsA i) = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rowsA_inj : ∀ i j : Fin 143, rowsA i = rowsA j → i = j := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The gauge fixing drops exactly the three parameters `(g, (1,1), (1,1))`. -/
theorem rowsA_ne_gauge : ∀ i : Fin 143, ∀ g : Fin 3, rowsA i ≠ .inl (g, (1, 1), (1, 1)) := by
  decide +kernel

/-- The minor over `k`. -/
noncomputable def minor (k : Type) [Field k] : Matrix (Fin 143) (Fin 143) k :=
  Matrix.of fun i j => jacRow (strassenSquare k) (rowsA i) (colsA j)

theorem det_minor_ne_zero (k : Type) [Field k] : (minor k).det ≠ 0 := by
  have hT : (minor k).BlockTriangular id := by
    intro i j hij
    simp only [minor, Matrix.of_apply, jacRow_cast, minor_upper i j hij, Int.cast_zero]
  rw [Matrix.det_of_upperTriangular hT, Finset.prod_ne_zero_iff]
  intro i _
  simp only [minor, Matrix.of_apply, jacRow_cast]
  rcases minor_diag i with h | h <;> rw [h] <;> simp

/-! ### The orbit parameters -/

section Orbit

variable {k : Type} [Field k] {W : Type}

/-- The global factor `1 + (t_{g,a,b})`. -/
noncomputable def orbMat (t : GIdx → MvPowerSeries W k) (g : Fin 3) :
    Matrix SquareVertex SquareVertex (MvPowerSeries W k) :=
  1 + Matrix.of fun a b => t (.inl (g, a, b))

/-- The term scalings `λ = 1 + t_{s,0} + t_{s,1}` and `μ = 1 − t_{s,1}`. -/
noncomputable def orbScal (t : GIdx → MvPowerSeries W k) (s : SquareSummand) (c : Fin 2) :
    MvPowerSeries W k :=
  if c = 0 then 1 + t (.inr (s, 0)) + t (.inr (s, 1)) else 1 - t (.inr (s, 1))

/-- Parameters with zero constant term. -/
def Centered (t : GIdx → MvPowerSeries W k) : Prop := ∀ w, constantCoeff (t w) = 0

theorem map_constantCoeff_orbMat {t : GIdx → MvPowerSeries W k} (ht : Centered t) (g : Fin 3) :
    (orbMat t g).map constantCoeff = 1 := by
  ext a b
  simp [orbMat, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply, apply_ite constantCoeff]

theorem isUnit_orbMat {t : GIdx → MvPowerSeries W k} (ht : Centered t) (g : Fin 3) :
    IsUnit (orbMat t g) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
    RingHom.mapMatrix_apply, map_constantCoeff_orbMat ht, Matrix.det_one]
  exact isUnit_one

theorem constantCoeff_orbScal {t : GIdx → MvPowerSeries W k} (ht : Centered t)
    (s : SquareSummand) (c : Fin 2) : constantCoeff (orbScal t s c) = 1 := by
  unfold orbScal; split_ifs <;> simp [show ∀ w, constantCoeff (t w) = 0 from ht]

theorem isUnit_orbScal {t : GIdx → MvPowerSeries W k} (ht : Centered t) (s : SquareSummand)
    (c : Fin 2) : IsUnit (orbScal t s c) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_orbScal ht]; exact isUnit_one

/-- The group element with parameters `t`: global factors `orbMat`, trivial blocks, term
scalings `orbScal`. -/
noncomputable def orbParams (t : GIdx → MvPowerSeries W k) (ht : Centered t) :
    FamilyParameters (MvPowerSeries W k) :=
  ⟨fun g => (isUnit_orbMat ht g).unit, fun _ _ => 1, fun s c => (isUnit_orbScal ht s c).unit⟩

theorem orbParams_congr {t t' : GIdx → MvPowerSeries W k} (h : t = t') (ht : Centered t)
    (ht' : Centered t') : orbParams t ht = orbParams t' ht' := by
  subst h; rfl

theorem orbParams_constantCoeff {t : GIdx → MvPowerSeries W k} (ht : Centered t) :
    (orbParams t ht).map constantCoeff = FamilyParameters.one k := by
  simp only [orbParams, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; exact map_constantCoeff_orbMat ht g
  · funext s g; exact map_one _
  · funext s c; apply Units.ext; exact constantCoeff_orbScal ht s c

theorem orbParams_map {W' : Type} {t : GIdx → MvPowerSeries W k} (ht : Centered t)
    (φ : MvPowerSeries W k →+* MvPowerSeries W' k) (hφ : Centered fun w => φ (t w)) :
    (orbParams t ht).map φ = orbParams (fun w => φ (t w)) hφ := by
  simp only [orbParams, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change φ (orbMat t g a b) = orbMat (fun w => φ (t w)) g a b
    by_cases h : a = b <;> simp [orbMat, h]
  · funext s g; exact map_one _
  · funext s c; apply Units.ext
    change φ (orbScal t s c) = orbScal (fun w => φ (t w)) s c
    unfold orbScal; split_ifs <;> simp

/-- The tangent generator of a parameter. -/
noncomputable def unitParams : GIdx → FamilyParameters (DualNumber k)
  | .inl (g, i, j) => FamilyParameters.globalUnit g i j
  | .inr (s, c) => FamilyParameters.termUnit s (decide (c = 1))

/-- **First-order jets of the orbit parameters.** -/
theorem orbParams_jet [DecidableEq W] {t : GIdx → MvPowerSeries W k} (ht : Centered t) (v : W)
    (w₀ : GIdx) (h : ∀ w, jetAt v (t w) = if w = w₀ then DualNumber.eps else 0) :
    (orbParams t ht).map (jetAt v) = unitParams w₀ := by
  have hM : ∀ g a b, jetAt v (orbMat t g a b) =
      TrivSqZeroExt.inl ((1 : Matrix SquareVertex SquareVertex k) a b) +
        (if (.inl (g, a, b) : GIdx) = w₀ then DualNumber.eps else 0) := by
    intro g a b
    rw [orbMat, Matrix.add_apply, map_add, Matrix.of_apply, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  have hS : ∀ s c, jetAt v (orbScal t s c) =
      if c = 0 then 1 + (if (.inr (s, 0) : GIdx) = w₀ then DualNumber.eps else 0) +
        (if (.inr (s, 1) : GIdx) = w₀ then DualNumber.eps else 0)
      else 1 - (if (.inr (s, 1) : GIdx) = w₀ then DualNumber.eps else 0) := by
    intro s c
    unfold orbScal
    by_cases hc : c = 0
    · rw [if_pos hc, if_pos hc, map_add, map_add, map_one, h, h]
    · rw [if_neg hc, if_neg hc, map_sub, map_one, h]
  rcases w₀ with ⟨g, i, j⟩ | ⟨s₀, c₀⟩
  · simp only [orbParams, FamilyParameters.map, unitParams, FamilyParameters.globalUnit,
      FamilyParameters.one, FamilyParameters.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext h'; apply Units.ext; refine Matrix.ext fun a b => ?_
      change jetAt v (orbMat t h' a b) = _
      rw [hM, matrixJet_val]
      apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl]
        split_ifs <;> simp
      · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, Decomposition.vertexUnit]
        by_cases hh : g = h'
        · subst hh
          rw [if_pos rfl, Matrix.single_apply]
          by_cases hab : i = a ∧ j = b
          · obtain ⟨rfl, rfl⟩ := hab
            simp
          · rw [if_neg hab, if_neg]
            · simp
            · intro hc
              simp only [Sum.inl.injEq, Prod.mk.injEq] at hc
              exact hab ⟨hc.2.1.symm, hc.2.2.symm⟩
        · rw [if_neg hh, if_neg]
          · simp
          · intro hc
            simp only [Sum.inl.injEq, Prod.mk.injEq] at hc
            exact hh hc.1.symm
    · funext s g; exact map_one _
    · funext s c; apply Units.ext
      change jetAt v (orbScal t s c) = 1
      rw [hS]; simp
  · simp only [orbParams, FamilyParameters.map, unitParams, FamilyParameters.termUnit,
      FamilyParameters.one, FamilyParameters.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext h'; apply Units.ext; refine Matrix.ext fun a b => ?_
      change jetAt v (orbMat t h' a b) = _
      rw [hM]
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    · funext s g; exact map_one _
    · funext s c; apply Units.ext
      change jetAt v (orbScal t s c) = _
      rw [hS]
      apply TrivSqZeroExt.ext
      · fin_cases c <;> by_cases hs : s = s₀ <;> fin_cases c₀ <;> simp [Jets.scalarJet, hs]
      · fin_cases c <;> by_cases hs : s = s₀ <;> fin_cases c₀ <;> simp [Jets.scalarJet, hs]

end Orbit

/-! ### The centered orbit map and its comorphism -/

section Pull

variable {k : Type} [Field k] {W : Type}

theorem constantCoeff_orbValue {t : GIdx → MvPowerSeries W k} (ht : Centered t) (x : Var) :
    constantCoeff (((orbParams t ht).value false).coordinates x) = pt k x := by
  rw [← LowerBound.coordinates_map, FamilyParameters.value_map, orbParams_constantCoeff,
    FamilyParameters.value_one]
  rfl

/-- The centered orbit map `g ↦ g·p − p`. -/
noncomputable def orbArg (t : GIdx → MvPowerSeries W k) (ht : Centered t) (x : Var) :
    MvPowerSeries W k :=
  ((orbParams t ht).value false).coordinates x - C (pt k x)

theorem constantCoeff_orbArg {t : GIdx → MvPowerSeries W k} (ht : Centered t) (x : Var) :
    constantCoeff (orbArg t ht x) = 0 := by
  rw [orbArg, map_sub, constantCoeff_orbValue, constantCoeff_C, sub_self]

theorem hasSubst_orbArg {t : GIdx → MvPowerSeries W k} (ht : Centered t) :
    HasSubst (orbArg t ht) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_orbArg ht)

/-- The comorphism of the orbit map on `k⟦z⟧`. -/
noncomputable def orbPull (t : GIdx → MvPowerSeries W k) (ht : Centered t) :
    MvPowerSeries Var k →ₐ[k] MvPowerSeries W k :=
  substAlgHom (hasSubst_orbArg ht)

theorem orbPull_apply {t : GIdx → MvPowerSeries W k} (ht : Centered t) (f : MvPowerSeries Var k) :
    orbPull t ht f = subst (orbArg t ht) f := by
  rw [orbPull, substAlgHom_apply]

/-- The orbit consists of solutions: every centered Brent equation pulls back to zero. -/
theorem orbPull_eqPS {t : GIdx → MvPowerSeries W k} (ht : Centered t)
    (abc : EquationIndex SquareVertex) : orbPull t ht (eqPS k abc) = 0 := by
  rw [orbPull_apply, subst_eqPS (hasSubst_orbArg ht)]
  exact centered_zero _ (FamilyParameters.value_solves _ _) _ (fun x => rfl) abc

theorem brentPS_le_ker_orbPull {t : GIdx → MvPowerSeries W k} (ht : Centered t) :
    brentPS k ≤ RingHom.ker (orbPull t ht) := by
  rw [brentPS, Ideal.span_le]
  rintro _ ⟨abc, rfl⟩
  exact orbPull_eqPS ht abc

/-- The comorphism factors through `Â`. -/
noncomputable def orbHat (t : GIdx → MvPowerSeries W k) (ht : Centered t) :
    Ahat k →ₐ[k] MvPowerSeries W k :=
  Ideal.Quotient.liftₐ (brentPS k) (orbPull t ht) fun _ ha => brentPS_le_ker_orbPull ht ha

theorem orbHat_mk {t : GIdx → MvPowerSeries W k} (ht : Centered t) (f : MvPowerSeries Var k) :
    orbHat t ht (Ideal.Quotient.mk _ f) = orbPull t ht f := rfl

/-- ... and through the algebraic local ring `A`. -/
noncomputable def orbA (t : GIdx → MvPowerSeries W k) (ht : Centered t) :
    Aalg k →+* MvPowerSeries W k :=
  (orbHat t ht).toRingHom.comp (ψ k)

theorem coeff_C_single [DecidableEq W] (v : W) (r : k) :
    coeff (Finsupp.single v 1) (C r : MvPowerSeries W k) = 0 := by
  rw [coeff_C, if_neg]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

/-- **The linear part of an orbit map**: along a parameter whose jet is the generator `w₀`, it is
the Jacobian row of `w₀`. -/
theorem coeff_orbArg [DecidableEq W] {t : GIdx → MvPowerSeries W k} (ht : Centered t) (v : W)
    (w₀ : GIdx) (h : ∀ w, jetAt v (t w) = if w = w₀ then DualNumber.eps else 0) (x : Var) :
    coeff (Finsupp.single v 1) (orbArg t ht x) = jacRow (strassenSquare k) w₀ x := by
  rw [orbArg, map_sub, coeff_C_single, sub_zero, ← jetAt_snd, ← LowerBound.coordinates_map,
    FamilyParameters.value_map, orbParams_jet ht v w₀ h]
  obtain ⟨s, m, a, b⟩ := x
  rcases w₀ with ⟨g, i, j⟩ | ⟨s₀, c₀⟩
  · rw [jacRow, ← FamilyParameters.globalUnit_tangent false g i j s m a b]
    cases m <;> rfl
  · rw [jacRow, ← FamilyParameters.termUnit_tangent false s₀ (decide (c₀ = 1)) s m a b]
    cases m <;> rfl

end Pull

/-! ### The 146-parameter orbit map -/

section Full

variable (k : Type) [Field k]

/-- The universal parameters `t_w = w`. -/
noncomputable def tΓ : GIdx → MvPowerSeries GIdx k := fun w => X w

theorem centered_tΓ : Centered (tΓ k) := fun w => constantCoeff_X w

/-- **The orbit family** `Γ = g(t)·p` over `k⟦146⟧`. -/
noncomputable def orbitFamily : Decomposition (MvPowerSeries GIdx k) SquareVertex SquareSummand :=
  (orbParams (tΓ k) (centered_tΓ k)).value false

theorem orbitFamily_solves : (orbitFamily k).Solves := FamilyParameters.value_solves _ _

/-- **`Φ_orb^*` on `k⟦z⟧`.** -/
noncomputable abbrev orbitPull : MvPowerSeries Var k →ₐ[k] MvPowerSeries GIdx k :=
  orbPull (tΓ k) (centered_tΓ k)

/-- **`Φ_orb^*` on `Â`.** -/
noncomputable abbrev orbitHat : Ahat k →ₐ[k] MvPowerSeries GIdx k := orbHat (tΓ k) (centered_tΓ k)

/-- **`Φ_orb^*` on `A`.** -/
noncomputable abbrev orbitA : Aalg k →+* MvPowerSeries GIdx k := orbA (tΓ k) (centered_tΓ k)

theorem orbitA_eq : orbitA k = (orbitHat k).toRingHom.comp (ψ k) := rfl

theorem jetAt_tΓ (v w : GIdx) :
    jetAt v (tΓ k w) = if w = v then DualNumber.eps else 0 := jetAt_X v w

/-- **The Jacobian of `Φ_orb` at `0`** is the matrix of rows `jacRow`. -/
theorem coeff_orbitPull_X (w : GIdx) (x : Var) :
    coeff (Finsupp.single w 1) (orbitPull k (X x)) = jacRow (strassenSquare k) w x := by
  rw [orbPull_apply, subst_X (hasSubst_orbArg _)]
  exact coeff_orbArg _ w w (jetAt_tΓ k w) x

/-- `dΦ_orb(0) : k^146 → k^2352`. -/
noncomputable def dOrbit : (GIdx → k) →ₗ[k] (Var → k) :=
  Matrix.vecMulLinear (Matrix.of (jacRow (strassenSquare k)))

theorem dOrbit_single (w : GIdx) : dOrbit k (Pi.single w 1) = jacRow (strassenSquare k) w := by
  rw [dOrbit, Matrix.vecMulLinear_apply, Matrix.single_vecMul, one_smul]
  rfl

end Full

/-! ### Upper bound: the central scalings `K₃` -/

section Upper

variable (k : Type) [Field k]

/-- The three central scalings. `K₀ = Σₐ e(0,a,a) − Σₛ e(s,0)`, `K₁ = Σₐ e(1,a,a) + Σₛ e(s,1)`,
`K₂ = Σₐ e(2,a,a) + Σₛ (e(s,0) − e(s,1))`. -/
noncomputable def kerVec : Fin 3 → GIdx → k :=
  ![∑ a : SquareVertex, Pi.single (.inl (0, a, a)) 1 - ∑ s : SquareSummand, Pi.single (.inr (s, 0)) 1,
    ∑ a : SquareVertex, Pi.single (.inl (1, a, a)) 1 + ∑ s : SquareSummand, Pi.single (.inr (s, 1)) 1,
    ∑ a : SquareVertex, Pi.single (.inl (2, a, a)) 1 +
      ∑ s : SquareSummand, (Pi.single (.inr (s, 0)) 1 - Pi.single (.inr (s, 1)) 1)]

variable {k}

theorem central_zero (d : Decomposition k SquareVertex SquareSummand) (x : Var) :
    ∑ a : SquareVertex, jacRow d (.inl (0, a, a)) x - ∑ s : SquareSummand, jacRow d (.inr (s, 0)) x
      = 0 := by
  obtain ⟨s, m, a, b⟩ := x
  cases m <;> simp [jacRow, Decomposition.vertexUnitCoefficient,
    FamilyParameters.termUnitCoefficient, Finset.sum_ite_eq]

theorem central_one (d : Decomposition k SquareVertex SquareSummand) (x : Var) :
    ∑ a : SquareVertex, jacRow d (.inl (1, a, a)) x + ∑ s : SquareSummand, jacRow d (.inr (s, 1)) x
      = 0 := by
  obtain ⟨s, m, a, b⟩ := x
  cases m <;> simp [jacRow, Decomposition.vertexUnitCoefficient,
    FamilyParameters.termUnitCoefficient, Finset.sum_ite_eq]

theorem central_two (d : Decomposition k SquareVertex SquareSummand) (x : Var) :
    ∑ a : SquareVertex, jacRow d (.inl (2, a, a)) x +
      ∑ s : SquareSummand, (jacRow d (.inr (s, 0)) x - jacRow d (.inr (s, 1)) x) = 0 := by
  obtain ⟨s, m, a, b⟩ := x
  cases m <;> simp [jacRow, Decomposition.vertexUnitCoefficient,
    FamilyParameters.termUnitCoefficient, Finset.sum_ite_eq]

variable (k)

/-- **`K₃` lies in the kernel of `dΦ_orb(0)`.** -/
theorem dOrbit_kerVec (g : Fin 3) : dOrbit k (kerVec k g) = 0 := by
  funext x
  fin_cases g <;>
    simp only [kerVec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, map_sum, map_sub,
      map_add, dOrbit_single, Finset.sum_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
  · exact central_zero _ x
  · exact central_one _ x
  · exact central_two _ x

theorem kerVec_apply (g h : Fin 3) :
    kerVec k g (.inl (h, 0, 0)) = if g = h then 1 else 0 := by
  fin_cases g <;> fin_cases h <;>
    simp [kerVec, Finset.sum_apply, Pi.single_apply]

theorem kerVec_independent : LinearIndependent k (kerVec k) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc h
  have := congrFun hc (.inl (h, 0, 0))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kerVec_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
  exact this

theorem three_le_finrank_ker : 3 ≤ Module.finrank k (LinearMap.ker (dOrbit k)) := by
  have hle : Submodule.span k (Set.range (kerVec k)) ≤ LinearMap.ker (dOrbit k) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact dOrbit_kerVec k g
  have h3 := finrank_span_eq_card (kerVec_independent k)
  rw [Fintype.card_fin] at h3
  rw [← h3]
  exact Submodule.finrank_mono hle

/-- **Upper bound:** `rank dΦ_orb(0) ≤ 146 − 3 = 143`. -/
theorem finrank_range_dOrbit_le : Module.finrank k (LinearMap.range (dOrbit k)) ≤ 143 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dOrbit k)
  rw [Module.finrank_fintype_fun_eq_card, card_GIdx] at h
  have := three_le_finrank_ker k
  omega

end Upper

/-! ### Lower bound: the gauge-fixed slice -/

section Lower

variable (k : Type) [Field k]

/-- **The 143 gauge-fixed rows are independent** (the minor has `det ≠ 0`). -/
theorem rows_independent :
    LinearIndependent k fun i : Fin 143 => jacRow (strassenSquare k) (rowsA i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : Matrix.vecMul c (minor k) = 0 := by
    funext j
    have := congrFun hc (colsA j)
    simpa [Matrix.vecMul, dotProduct, minor, Finset.sum_apply] using this
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero (det_minor_ne_zero k) hv)

/-- **Lower bound:** `rank dΦ_orb(0) ≥ 143`. -/
theorem le_finrank_range_dOrbit : 143 ≤ Module.finrank k (LinearMap.range (dOrbit k)) := by
  have hle : Submodule.span k (Set.range fun i : Fin 143 => jacRow (strassenSquare k) (rowsA i)) ≤
      LinearMap.range (dOrbit k) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, dOrbit_single k (rowsA i)⟩
  have h := finrank_span_eq_card (rows_independent k)
  rw [Fintype.card_fin] at h
  rw [← h]
  exact Submodule.finrank_mono hle

/-- **The orbit has dimension 143**: `rank dΦ_orb(0) = 143`. -/
theorem finrank_range_dOrbit : Module.finrank k (LinearMap.range (dOrbit k)) = 143 :=
  le_antisymm (finrank_range_dOrbit_le k) (le_finrank_range_dOrbit k)

/-- `K₃` is the whole kernel. -/
theorem finrank_ker_dOrbit : Module.finrank k (LinearMap.ker (dOrbit k)) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dOrbit k)
  rw [Module.finrank_fintype_fun_eq_card, card_GIdx, finrank_range_dOrbit] at h
  omega

/-- The slot of a parameter in the gauge slice. -/
def slot (w : GIdx) : Option (Fin 143) := (List.finRange 143).find? fun i => decide (rowsA i = w)

theorem slot_some {w : GIdx} {i : Fin 143} (h : slot w = some i) : rowsA i = w := by
  have := List.find?_some h
  simpa using this

theorem slot_rowsA (i : Fin 143) : ∃ j, slot (rowsA i) = some j := by
  cases h : slot (rowsA i) with
  | some j => exact ⟨j, rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp h i (List.mem_finRange i)
    simp at this

/-- **Gauge fixing**: the parameters on the slice `k⟦c⟧`, `c` the 143 kept coordinates, with
`(g, (1,1), (1,1))` set to zero. -/
noncomputable def tS : GIdx → MvPowerSeries (Fin 143) k := fun w =>
  match slot w with
  | some i => X i
  | none => 0

theorem centered_tS : Centered (tS k) := by
  intro w
  unfold tS
  cases slot w <;> simp

theorem jetAt_tS (v : Fin 143) (w : GIdx) :
    jetAt v (tS k w) = if w = rowsA v then DualNumber.eps else 0 := by
  unfold tS
  cases h : slot w with
  | none =>
    rw [map_zero, if_neg]
    rintro rfl
    obtain ⟨j, hj⟩ := slot_rowsA v
    rw [h] at hj
    cases hj
  | some j =>
    have hj := slot_some h
    dsimp only
    rw [jetAt_X]
    by_cases hjv : j = v
    · subst hjv; rw [if_pos rfl, if_pos hj.symm]
    · rw [if_neg hjv, if_neg]
      intro hw
      exact hjv (rowsA_inj _ _ (hj.trans hw))

theorem tS_gauge (g : Fin 3) : tS k (.inl (g, (1, 1), (1, 1))) = 0 := by
  unfold tS
  cases h : slot (.inl (g, (1, 1), (1, 1))) with
  | none => rfl
  | some j => exact absurd (slot_some h) (rowsA_ne_gauge j g)

theorem tS_rowsA (i : Fin 143) : tS k (rowsA i) = X i := by
  unfold tS
  obtain ⟨j, hj⟩ := slot_rowsA i
  rw [hj]
  dsimp only
  rw [rowsA_inj _ _ (slot_some hj)]

theorem hasSubst_tS : HasSubst (tS k) := hasSubst_of_constantCoeff_zero (centered_tS k)

/-- Restriction of `k⟦146⟧` to the gauge slice `k⟦c⟧`. -/
noncomputable def gaugeRestrict : MvPowerSeries GIdx k →ₐ[k] MvPowerSeries (Fin 143) k :=
  substAlgHom (hasSubst_tS k)

/-- The gauge-fixed orbit map `k⟦z⟧ → k⟦c⟧`. -/
noncomputable abbrev slicePull : MvPowerSeries Var k →ₐ[k] MvPowerSeries (Fin 143) k :=
  orbPull (tS k) (centered_tS k)

/-- **The gauge-fixed orbit map on `Â`.** -/
noncomputable abbrev sliceHat : Ahat k →ₐ[k] MvPowerSeries (Fin 143) k :=
  orbHat (tS k) (centered_tS k)

/-- **The gauge-fixed orbit map is the 146-parameter orbit map restricted to the slice.** -/
theorem slicePull_eq : slicePull k = (gaugeRestrict k).comp (orbitPull k) := by
  have hcen : Centered fun w => gaugeRestrict k (tΓ k w) := by
    intro w
    show constantCoeff (gaugeRestrict k (X w)) = 0
    rw [gaugeRestrict, substAlgHom_X]
    exact centered_tS k w
  have harg : ∀ x, gaugeRestrict k (orbArg (tΓ k) (centered_tΓ k) x) = orbArg (tS k) (centered_tS k) x := by
    intro x
    rw [orbArg, orbArg, map_sub, algHom_C]
    congr 1
    change (gaugeRestrict k).toRingHom _ = _
    rw [← LowerBound.coordinates_map, FamilyParameters.value_map, orbParams_map _ _ hcen]
    congr 3
    funext w
    change substAlgHom (hasSubst_tS k) (X w) = _
    rw [substAlgHom_X]
  ext1 f
  rw [AlgHom.comp_apply, orbPull_apply, orbPull_apply]
  rw [gaugeRestrict, substAlgHom_apply, subst_comp_subst_apply (hasSubst_orbArg _) (hasSubst_tS k)]
  congr 1
  funext x
  rw [← substAlgHom_apply (hasSubst_tS k)]
  exact (harg x).symm

theorem sliceHat_eq : sliceHat k = (gaugeRestrict k).comp (orbitHat k) := by
  apply Ideal.Quotient.algHom_ext
  ext1 f
  change slicePull k f = gaugeRestrict k (orbitPull k f)
  rw [slicePull_eq]
  rfl

/-- The jets of the slice parameters. -/
theorem coeff_orbArg_tS (v : Fin 143) (x : Var) :
    coeff (Finsupp.single v 1) (orbArg (tS k) (centered_tS k) x) = jacRow (strassenSquare k) (rowsA v) x :=
  coeff_orbArg _ v (rowsA v) (jetAt_tS k v) x

/-- **Formal inverse function theorem on the minor.** -/
theorem slicePull_surjective : Function.Surjective (slicePull k) := by
  classical
  let b : Fin 143 → MvPowerSeries (Fin 143) k := fun i => orbArg (tS k) (centered_tS k) (colsA i)
  have hb0 : ∀ i, constantCoeff (b i) = 0 := fun i => constantCoeff_orbArg _ _
  have hM : (Matrix.of fun x v => coeff (Finsupp.single ((Equiv.refl (Fin 143)).symm v) 1) (b x)) =
      (minor k).transpose := by
    ext x v
    simp only [Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply, b, coeff_orbArg_tS,
      Matrix.transpose_apply, minor]
  have hbij := subst_bijective_equiv (Equiv.refl (Fin 143)) hb0 (by
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, isUnit_iff_ne_zero]
    exact det_minor_ne_zero k)
  intro g
  obtain ⟨f₀, hf₀⟩ := hbij.2 g
  let ρ : Fin 143 → MvPowerSeries Var k := fun i => X (colsA i)
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero fun i => constantCoeff_X _
  refine ⟨subst ρ f₀, ?_⟩
  rw [orbPull_apply, subst_comp_subst_apply hρ (hasSubst_orbArg _)]
  convert hf₀ using 2
  funext i
  exact subst_X (hasSubst_orbArg _) (colsA i)

/-- **The gauge-fixed orbit comorphism `Â → k⟦c⟧` is surjective.** -/
theorem sliceHat_surjective : Function.Surjective (sliceHat k) := by
  intro g
  obtain ⟨f, hf⟩ := slicePull_surjective k g
  exact ⟨Ideal.Quotient.mk _ f, hf⟩

/-- The target `k⟦c⟧` has dimension 143. -/
theorem ringKrullDim_slice : ringKrullDim (MvPowerSeries (Fin 143) k) = 143 := by
  rw [ringKrullDim_mvPowerSeries, Fintype.card_fin]
  rfl

end Lower

end Brent.Formal
