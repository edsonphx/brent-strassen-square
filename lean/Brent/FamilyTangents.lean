import Brent.FamilyParameters
import Mathlib.Data.Matrix.Basis

open TrivSqZeroExt
open scoped BigOperators

namespace Brent

namespace Jets

variable {R : Type} [CommRing R]

/-- A unit over the dual numbers with prescribed first derivative. -/
def scalarJet (a : R) : (DualNumber R)ˣ :=
  ⟨⟨1, a⟩, ⟨1, -a⟩, by ext <;> simp, by ext <;> simp⟩

@[simp] theorem forget_scalarJet (a : R) :
    Units.map (forget R).toMonoidHom (scalarJet a) = 1 := by
  apply Units.ext
  rfl

@[simp] theorem forget_matrixJet {α : Type} [Fintype α] [DecidableEq α] (a : Matrix α α R) :
    Units.map (forget R).mapMatrix.toMonoidHom (matrixJet a) = 1 := by
  apply Units.ext
  ext i j
  rfl

end Jets

namespace Decomposition

variable {R α ι : Type} [CommRing R] [Fintype α] [DecidableEq α]

omit [CommRing R] [Fintype α] [DecidableEq α] in
theorem eq_of_components {d e : Decomposition R α ι}
    (hu : d.u = e.u) (hv : d.v = e.v) (hw : d.w = e.w) : d = e := by
  cases d
  cases e
  simp_all

private def flatMatrix (f : α × α → R) : Matrix α α R := fun i j => f (i, j)

private def jetMatrix (A B : Matrix α α R) : Matrix α α (DualNumber R) :=
  fun i j => ⟨A i j, B i j⟩

omit [DecidableEq α] in
private theorem jetMatrix_mul (A B C D : Matrix α α R) :
    jetMatrix A B * jetMatrix C D = jetMatrix (A * C) (A * D + B * C) := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · simp [Matrix.mul_apply, jetMatrix, fst_sum, fst_mul]
  · simp [Matrix.mul_apply, jetMatrix, snd_sum, Finset.sum_add_distrib]

omit [CommRing R] [Fintype α] [DecidableEq α] in
private theorem jetMatrix_transpose (A B : Matrix α α R) :
    (jetMatrix A B).transpose = jetMatrix A.transpose B.transpose := rfl

/-- The three vertex derivatives, with the output convention used in the paper. -/
def vertexVariation (d : Decomposition R α ι) (E F H : Matrix α α R) :
    Decomposition R α ι where
  u s a := (E.transpose * flatMatrix (d.u s) - flatMatrix (d.u s) * F.transpose) a.1 a.2
  v s a := (F.transpose * flatMatrix (d.v s) - flatMatrix (d.v s) * H.transpose) a.1 a.2
  w s a := (-(E * flatMatrix (d.w s)) + flatMatrix (d.w s) * H) a.1 a.2

theorem tangent_changeBasis (d : Decomposition R α ι) (E F H : Matrix α α R) :
    ((d.map (Jets.constant R)).changeBasis (matrixJet E) (matrixJet F)
      (matrixJet H)).tangentPart = d.vertexVariation E F H := by
  have val (M : Matrix α α R) : (matrixJet M).val = jetMatrix 1 M := rfl
  have inv (M : Matrix α α R) : (matrixJet M).inv = jetMatrix 1 (-M) := rfl
  have action (M N A : Matrix α α R) :
      jetMatrix 1 M * jetMatrix A 0 * jetMatrix 1 N =
        jetMatrix A (A * N + M * A) := by
    rw [jetMatrix_mul, jetMatrix_mul]
    simp
  have u s : flatMatrix ((d.map (Jets.constant R)).u s) = jetMatrix (flatMatrix (d.u s)) 0 := rfl
  have v s : flatMatrix ((d.map (Jets.constant R)).v s) = jetMatrix (flatMatrix (d.v s)) 0 := rfl
  have w s : flatMatrix ((d.map (Jets.constant R)).w s) = jetMatrix (flatMatrix (d.w s)) 0 := rfl
  apply eq_of_components
  all_goals
    funext s a
    rcases a with ⟨i, j⟩
  · change (((matrixJet E).val.transpose * flatMatrix ((d.map (Jets.constant R)).u s) *
      (matrixJet F).inv.transpose) i j).snd = _
    rw [val, inv, u, jetMatrix_transpose, jetMatrix_transpose, Matrix.transpose_one, action]
    simp only [jetMatrix, snd_mk]
    simp [vertexVariation, sub_eq_add_neg, add_comm]
  · change (((matrixJet F).val.transpose * flatMatrix ((d.map (Jets.constant R)).v s) *
      (matrixJet H).inv.transpose) i j).snd = _
    rw [val, inv, v, jetMatrix_transpose, jetMatrix_transpose, Matrix.transpose_one, action]
    simp only [jetMatrix, snd_mk]
    simp [vertexVariation, sub_eq_add_neg, add_comm]
  · change (((matrixJet E).inv * flatMatrix ((d.map (Jets.constant R)).w s) *
      (matrixJet H).val) i j).snd = _
    rw [inv, val, w, action]
    simp only [jetMatrix, snd_mk]
    simp [vertexVariation, add_comm]

end Decomposition
end Brent

namespace Brent

namespace Decomposition

variable {R α ι : Type} [CommRing R] [Fintype α] [DecidableEq α]

/-- The coordinate derivative of a single matrix-unit change of basis. -/
def vertexUnitCoefficient (d : Decomposition R α ι) (g : Fin 3) (i j : α)
    (s : ι) (m : Mode) (a b : α) : R :=
  match m with
  | .u => if g = 0 then (if a = j then d.u s (i, b) else 0)
          else if g = 1 then (if b = i then -d.u s (a, j) else 0) else 0
  | .v => if g = 1 then (if a = j then d.v s (i, b) else 0)
          else if g = 2 then (if b = i then -d.v s (a, j) else 0) else 0
  | .w => if g = 0 then (if a = i then -d.w s (j, b) else 0)
          else if g = 2 then (if b = j then d.w s (a, i) else 0) else 0

def vertexUnit (g h : Fin 3) (i j : α) : Matrix α α R :=
  if g = h then Matrix.single i j 1 else 0

private theorem mul_single_coordinate (A : Matrix α α R) (i j a b : α) :
    (A * Matrix.single i j (1 : R)) a b = if b = j then A a i else 0 := by
  by_cases h : b = j
  · subst b
    simp
  · simp [h]

private theorem single_mul_coordinate (A : Matrix α α R) (i j a b : α) :
    (Matrix.single i j (1 : R) * A) a b = if a = i then A j b else 0 := by
  by_cases h : a = i
  · subst a
    simp
  · simp [h]

theorem vertexVariation_unit (d : Decomposition R α ι) (g : Fin 3)
    (i j : α) (s : ι) (m : Mode) (a b : α) :
    (d.vertexVariation (vertexUnit g 0 i j) (vertexUnit g 1 i j) (vertexUnit g 2 i j)).coordinates
      (s, m, (a, b)) = d.vertexUnitCoefficient g i j s m a b := by
  fin_cases g <;> cases m <;>
    simp [coordinates, vertexVariation, vertexUnitCoefficient, vertexUnit, flatMatrix,
      Matrix.transpose_single, mul_single_coordinate, single_mul_coordinate] <;> split_ifs <;> simp_all

end Decomposition

namespace FamilyParameters

variable {R : Type} [CommRing R]

theorem rescale_identity (d : Decomposition R SquareVertex SquareSummand) :
    d.rescale (fun _ => 1) (fun _ => 1) = d := by
  cases d
  simp [Decomposition.rescale]

/-- A matrix-unit generator in the global vertex group, shared by both charts. -/
def globalUnit (g : Fin 3) (i j : SquareVertex) : FamilyParameters (DualNumber R) :=
  { FamilyParameters.one _ with global := fun h => matrixJet (Decomposition.vertexUnit g h i j) }

@[simp] theorem globalUnit_base (g : Fin 3) (i j : SquareVertex) :
    (globalUnit (R := R) g i j).map (Jets.forget R) = FamilyParameters.one R := by
  simp only [globalUnit, map, FamilyParameters.one, _root_.map_one, FamilyParameters.mk.injEq, and_true]
  funext h
  exact Jets.forget_matrixJet _

private theorem square_constant :
    strassenSquare (DualNumber R) = (strassenSquare R).map (Jets.constant R) := by
  have h : (Int.castRingHom (DualNumber R)) =
      (Jets.constant R).comp (Int.castRingHom R) := Subsingleton.elim _ _
  rw [strassenSquare, strassenSquare, h]
  rfl

theorem globalUnit_tangent (left : Bool) (g : Fin 3) (i j : SquareVertex)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    ((globalUnit (R := R) g i j).value left).tangentPart.coordinates (s, m, (a, b)) =
      (strassenSquare R).vertexUnitCoefficient g i j s m a b := by
  have hs : (if left then leftFamily (R := DualNumber R) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    else rightFamily (fun _ => 1) (fun _ => 1) (fun _ => 1)) = strassenSquare (DualNumber R) := by
    cases left <;> simp [leftFamily_at_identity, rightFamily_at_identity]
  simp only [value, globalUnit, FamilyParameters.one, hs, rescale_identity, square_constant,
    Decomposition.tangent_changeBasis, Decomposition.vertexVariation_unit]

/-- A term scaling compensated in the second input or in the output. -/
def termUnit (k : SquareSummand) (second : Bool) : FamilyParameters (DualNumber R) :=
  { FamilyParameters.one _ with
    scale := fun s m => Jets.scalarJet (if s = k then
      if m = 0 then 1 else if second then -1 else 0 else 0) }

@[simp] theorem termUnit_base (k : SquareSummand) (second : Bool) :
    (termUnit (R := R) k second).map (Jets.forget R) = FamilyParameters.one R := by
  simp only [termUnit, map, FamilyParameters.one, _root_.map_one, FamilyParameters.mk.injEq, true_and]
  funext s m
  exact Jets.forget_scalarJet _

def termUnitCoefficient (d : Decomposition R SquareVertex SquareSummand)
    (k : SquareSummand) (second : Bool) (s : SquareSummand) (m : Mode)
    (a b : SquareVertex) : R :=
  if s = k then
    match m with
    | .u => d.u s (a, b)
    | .v => if second then -d.v s (a, b) else 0
    | .w => if second then 0 else -d.w s (a, b)
  else 0

theorem termUnit_tangent (left : Bool) (k : SquareSummand) (second : Bool)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    ((termUnit (R := R) k second).value left).tangentPart.coordinates (s, m, (a, b)) =
      termUnitCoefficient (strassenSquare R) k second s m a b := by
  have hs : (if left then leftFamily (R := DualNumber R) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    else rightFamily (fun _ => 1) (fun _ => 1) (fun _ => 1)) = strassenSquare (DualNumber R) := by
    cases left <;> simp [leftFamily_at_identity, rightFamily_at_identity]
  simp only [value, termUnit, FamilyParameters.one, hs, Decomposition.changeBasis_identity, square_constant]
  cases second <;> cases m <;> by_cases hk : s = k <;>
    simp [termUnitCoefficient, Decomposition.coordinates, Decomposition.rescale,
      Decomposition.tangentPart, Jets.scalarJet, Decomposition.map, Jets.constant, hk]

end FamilyParameters
end Brent
