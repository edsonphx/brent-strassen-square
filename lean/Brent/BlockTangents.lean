import Brent.FamilyTangents

open TrivSqZeroExt

namespace Brent.FamilyParameters

variable {R : Type} [CommRing R]

private def blockVertexUnit (k : Fin 7) (g : Fin 3) (i j : Fin 2)
    (s : Fin 7) (h : Fin 3) : (Matrix (Fin 2) (Fin 2) (DualNumber R))ˣ :=
  if s = k then matrixJet (Decomposition.vertexUnit g h i j) else 1

/-- A single vertex generator in one Strassen block. -/
def blockUnit (k : Fin 7) (g : Fin 3) (i j : Fin 2) : FamilyParameters (DualNumber R) :=
  { FamilyParameters.one _ with block := blockVertexUnit k g i j }

@[simp] theorem blockUnit_base (k : Fin 7) (g : Fin 3) (i j : Fin 2) :
    (blockUnit (R := R) k g i j).map (Jets.forget R) = FamilyParameters.one R := by
  simp only [blockUnit, map, FamilyParameters.one, _root_.map_one, FamilyParameters.mk.injEq,
    true_and, and_true]
  funext s h
  unfold blockVertexUnit
  split
  · exact Jets.forget_matrixJet _
  · exact _root_.map_one _

private def base (R : Type) [CommRing R] := strassen.map (Int.castRingHom R)

private theorem base_constant : base (DualNumber R) = (base R).map (Jets.constant R) := by
  have h : (Int.castRingHom (DualNumber R)) =
      (Jets.constant R).comp (Int.castRingHom R) := Subsingleton.elim _ _
  unfold base
  rw [h]
  rfl

private theorem block_specialized (k l : Fin 7) (g : Fin 3) (i j : Fin 2)
    (s : Fin 7) (m : Mode) (a b : Fin 2) :
    (((base (DualNumber R)).changeBasis (blockVertexUnit k g i j l 0)
      (blockVertexUnit k g i j l 1) (blockVertexUnit k g i j l 2)).tangentPart.coordinates
      (s, m, (a, b))) =
    if l = k then (base R).vertexUnitCoefficient g i j s m a b else 0 := by
  by_cases h : l = k
  · simp [blockVertexUnit, h, base_constant, Decomposition.tangent_changeBasis,
      Decomposition.vertexVariation_unit]
  · simp only [blockVertexUnit, h, if_false, Decomposition.changeBasis_identity, base_constant]
    cases m <;> rfl

def blockUnitCoefficient (left : Bool) (k : Fin 7) (g : Fin 3) (i j : Fin 2)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) : R :=
  if left then
    if s.1 = k then
      (base R).coordinates (s.1, m, (a.1, b.1)) *
        (base R).vertexUnitCoefficient g i j s.2 m a.2 b.2
    else 0
  else
    if s.2 = k then
      (base R).vertexUnitCoefficient g i j s.1 m a.1 b.1 *
        (base R).coordinates (s.2, m, (a.2, b.2))
    else 0

theorem blockUnit_tangent (left : Bool) (k : Fin 7) (g : Fin 3) (i j : Fin 2)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    ((blockUnit (R := R) k g i j).value left).tangentPart.coordinates (s, m, (a, b)) =
      blockUnitCoefficient left k g i j s m a b := by
  let ch (l : Fin 7) := (base (DualNumber R)).changeBasis
    (blockVertexUnit k g i j l 0) (blockVertexUnit k g i j l 1) (blockVertexUnit k g i j l 2)
  have slope (l s : Fin 7) (x y : Fin 2) :
      (ch l).tangentPart.coordinates (s, m, (x, y)) =
        if l = k then (base R).vertexUnitCoefficient g i j s m x y else 0 :=
    block_specialized k l g i j s m x y
  have rhsL :
      (((base (DualNumber R)).recursiveLeft ch).tangentPart.coordinates (s, m, (a, b))) =
       (base R).coordinates (s.1, m, (a.1, b.1)) *
         (ch s.1).tangentPart.coordinates (s.2, m, (a.2, b.2)) := by
    cases m <;> simp [Decomposition.recursiveLeft, Decomposition.coordinates, Decomposition.tangentPart,
      Decomposition.outer, Decomposition.inner, base_constant, Decomposition.map, Jets.constant]
  have rhsR :
      ((Decomposition.recursiveRight ch (base (DualNumber R))).tangentPart.coordinates (s, m, (a, b))) =
       (ch s.2).tangentPart.coordinates (s.1, m, (a.1, b.1)) *
         (base R).coordinates (s.2, m, (a.2, b.2)) := by
    cases m <;> simp [Decomposition.recursiveRight, Decomposition.coordinates, Decomposition.tangentPart,
      Decomposition.outer, Decomposition.inner, base_constant, Decomposition.map, Jets.constant]
  cases left
  · simp only [value, blockUnit, FamilyParameters.one, Bool.false_eq_true, if_false,
      Decomposition.changeBasis_identity]
    rw [rescale_identity]
    change (Decomposition.recursiveRight ch (base (DualNumber R))).tangentPart.coordinates _ = _
    rw [rhsR, slope]
    simp [blockUnitCoefficient, ite_mul]
  · simp only [value, blockUnit, FamilyParameters.one, if_true,
      Decomposition.changeBasis_identity]
    rw [rescale_identity]
    change ((base (DualNumber R)).recursiveLeft ch).tangentPart.coordinates _ = _
    rw [rhsL, slope]
    simp [blockUnitCoefficient, mul_ite]

end Brent.FamilyParameters
