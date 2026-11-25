import Brent.Generated.OriginChecks
import Brent.KernelCheck.JetProjection
import Brent.KernelCheck.TangentFrame

open scoped BigOperators

namespace Brent.TangentData

/-- Interpret a frozen signed tangent vector over an arbitrary coefficient ring. -/
def frameDirection (R : Type) [CommRing R] (i : Fin 251) :
    Decomposition R SquareVertex SquareSummand :=
  let coeff x := (SparseRow.coefficient (squareVariableNumber x).val (frame i) : R)
  ⟨fun s a => coeff (s, Mode.u, a), fun s a => coeff (s, Mode.v, a), fun s a => coeff (s, Mode.w, a)⟩

theorem frameDirection_coordinates (R : Type) [CommRing R] (i : Fin 251)
    (x : Variable SquareVertex SquareSummand) :
    (frameDirection R i).coordinates x =
      (SparseRow.coefficient (squareVariableNumber x).val (frame i) : R) := by
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

def castOrigin (R : Type) [CommRing R] (i : Fin 251) :
    FamilyParameters (DualNumber R) :=
  (frameOrigin Int i).map (Jets.map Int (Int.castRingHom R))

private theorem castOrigin_base (R : Type) [CommRing R] (i : Fin 251) :
    (castOrigin R i).map (Jets.forget R) = FamilyParameters.one R := by
  have comp : (Jets.forget R).comp (Jets.map Int (Int.castRingHom R)) =
      (Int.castRingHom R).comp (Jets.forget Int) := rfl
  rw [castOrigin, FamilyParameters.map_comp, comp, ← FamilyParameters.map_comp,
    frameOrigin_base, FamilyParameters.map_one]

/-- The numerical vector is literally the first derivative of either applicable exact family. -/
theorem archived_origin (R : Type) [CommRing R] (i : Fin 251) (left : Bool) (h : InChart i left) :
    ((castOrigin R i).value left).tangentPart = frameDirection R i := by
  have hcoordinates (x : Variable SquareVertex SquareSummand) :
      (((castOrigin R i).value left).tangentPart).coordinates x =
        (frameDirection R i).coordinates x := by
    rw [frameDirection_coordinates, castOrigin, ← FamilyParameters.value_map]
    have eq :
        (((frameOrigin Int i).value left).map (Jets.map Int (Int.castRingHom R))).tangentPart.coordinates x =
        (((frameOrigin Int i).value left).tangentPart.coordinates x : R) := by
      obtain ⟨s, m, a⟩ := x
      cases m <;> rfl
    rw [eq, origin_of_check i left h (checkedOrigin i)]
  apply Decomposition.eq_of_components
  · funext s a
    exact hcoordinates (s, Mode.u, a)
  · funext s a
    exact hcoordinates (s, Mode.v, a)
  · funext s a
    exact hcoordinates (s, Mode.w, a)

private def chartIndex (left : Bool) (i : Fin 197) : Fin 251 :=
  ⟨if left || i.val < 143 then i.val else i.val + 54, by have := i.isLt; split <;> omega⟩

private theorem chartIndex_injective (left : Bool) : Function.Injective (chartIndex left) := by
  intro i j h
  apply Fin.ext
  have eq := congrArg Fin.val h
  cases left <;> simp [chartIndex] at eq <;> (try split_ifs at eq) <;> omega

private theorem chartIndex_available (left : Bool) (i : Fin 197) : InChart (chartIndex left i) left := by
  have bound := i.isLt
  cases left <;> simp [chartIndex, InChart]
  split_ifs <;> omega

/-- Each of the two exact charts has 197 exhibited independent first derivatives. -/
theorem chart_independent_derivatives (R : Type) [Field R] (left : Bool) :
    LinearIndependent R (fun i : Fin 197 => fun j : Fin 2352 =>
      ((castOrigin R (chartIndex left i)).value left).tangentPart.coordinates (squareVariableNumber.symm j)) := by
  have full : LinearIndependent R (fun i : Fin 251 =>
      SparseRow.decode (K := R) (Fin.val : Fin 2352 → Nat) (frame i)) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin 251) = Module.finrank R (Submodule.span R
      (Set.range (fun i => SparseRow.decode (K := R) (Fin.val : Fin 2352 → Nat) (frame i))))
    rw [archived_frame_rank, Fintype.card_fin]
  convert full.comp (chartIndex left) (chartIndex_injective left) using 1
  funext i j
  rw [archived_origin R _ left (chartIndex_available left i), frameDirection_coordinates]
  simp only [Equiv.apply_symm_apply, Function.comp_apply, SparseRow.decode]

end Brent.TangentData

namespace Brent.QuadraticData

open TangentData

/-- The polar coefficient of a projected obstruction on two archived directions. -/
def projectedPolar (ell : Fin 54) (i j : Fin 251) : K :=
  ∑ e : EquationIndex SquareVertex, (strassenSquare K).polarizedEntry
    (frameDirection K i) (frameDirection K j) e.1 e.2.1 e.2.2 *
    functionalEntry ell (squareEquationNumber e)

/-- Coefficients vanish on any pair of directions from a common chart. -/
theorem archived_same_chart_zero (ell : Fin 54) (i j : Fin 251) (left : Bool)
    (hi : InChart i left) (hj : InChart j left) : projectedPolar ell i j = 0 := by
  have h := same_family_polar_zero ell left (castOrigin K j) (castOrigin K i)
    (castOrigin_base K j) (castOrigin_base K i)
  rwa [archived_origin K i left hi, archived_origin K j left hj] at h

/-- All polar coefficients outside the mixed left-only/right-only block vanish. -/
theorem archived_nonmixed_zero (ell : Fin 54) (i j : Fin 251)
    (nonmixed : ¬ ((143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) ∨
                    (143 ≤ j.val ∧ j.val < 197 ∧ 197 ≤ i.val))) :
    projectedPolar ell i j = 0 := by
  by_cases h : i.val < 197 ∧ j.val < 197
  · exact archived_same_chart_zero ell i j true h.1 h.2
  · apply archived_same_chart_zero ell i j false <;> simp [InChart] <;> omega

/-- The true coefficient of a square is half of the diagonal polar coefficient. -/
theorem archived_square_zero (ell : Fin 54) (i : Fin 251) :
    (∑ e : EquationIndex SquareVertex, (strassenSquare K).quadraticEntry
      (frameDirection K i) e.1 e.2.1 e.2.2 * functionalEntry ell (squareEquationNumber e)) = 0 := by
  have diagonal (e : EquationIndex SquareVertex) :
      (strassenSquare K).polarizedEntry (frameDirection K i) (frameDirection K i) e.1 e.2.1 e.2.2 =
        2 * (strassenSquare K).quadraticEntry (frameDirection K i) e.1 e.2.1 e.2.2 := by
    simp only [Decomposition.polarizedEntry, Decomposition.quadraticEntry, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have h := archived_nonmixed_zero ell i i (by omega)
  unfold projectedPolar at h
  simp_rw [diagonal, mul_assoc, ← Finset.mul_sum] at h
  have squareTwo : (2 : K) * 2 = 1 := by decide
  simpa only [← mul_assoc, squareTwo, one_mul, mul_zero] using congrArg (fun z : K => 2 * z) h

private theorem cast_mixedEntry (i j : Fin 54) (e : EquationIndex SquareVertex) :
    (mixedEntry i j e : K) = (strassenSquare K).polarizedEntry
      ((xDirection i).map (Int.castRingHom K)) ((yDirection j).map (Int.castRingHom K))
      e.1 e.2.1 e.2.2 := by
  let x := xDirection i
  let y := yDirection j
  let a := e.1
  let b := e.2.1
  let c := e.2.2
  let p := strassenSquareInt
  have integer : mixedEntry i j e = p.polarizedEntry x y a b c := by
    unfold mixedEntry
    simp only [Decomposition.quadraticEntry, Decomposition.polarizedEntry, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    change (x.u s a + y.u s a) * (x.v s b + y.v s b) * p.w s c +
      (x.u s a + y.u s a) * p.v s b * (x.w s c + y.w s c) +
      p.u s a * (x.v s b + y.v s b) * (x.w s c + y.w s c) - _ - _ = _
    ring
  rw [integer]
  change (Int.castRingHom K) (p.polarizedEntry x y a b c) = _
  simp only [Decomposition.polarizedEntry, map_sum, map_add, map_mul, strassenSquare, Decomposition.map, p, x, y, a, b, c]

private theorem left_direction (i : Fin 54) :
    frameDirection K (xFrameIndex i) = (xDirection i).map (Int.castRingHom K) := by
  apply Decomposition.eq_of_components <;> funext s a
  · exact congrArg (fun z : Int => (z : K)) (archived_left_coordinates i (s, Mode.u, a))
  · exact congrArg (fun z : Int => (z : K)) (archived_left_coordinates i (s, Mode.v, a))
  · exact congrArg (fun z : Int => (z : K)) (archived_left_coordinates i (s, Mode.w, a))

private theorem right_direction (i : Fin 54) :
    frameDirection K (yFrameIndex i) = (yDirection i).map (Int.castRingHom K) := by
  apply Decomposition.eq_of_components <;> funext s a
  · exact congrArg (fun z : Int => (z : K)) (archived_right_coordinates i (s, Mode.u, a))
  · exact congrArg (fun z : Int => (z : K)) (archived_right_coordinates i (s, Mode.v, a))
  · exact congrArg (fun z : Int => (z : K)) (archived_right_coordinates i (s, Mode.w, a))

/-- The verified mixed table is the restriction of the full projected polar form. -/
theorem archived_polar_mixed (ell i j : Fin 54) :
    projectedPolar ell (xFrameIndex i) (yFrameIndex j) = projectedMixed ell i j := by
  simp only [projectedPolar, projectedMixed, left_direction, right_direction, cast_mixedEntry]

/-- Each of the actual projected quadrics has the archived coefficient-one leader. -/
theorem archived_polar_leading (ell : Fin 54) :
    projectedPolar ell (xFrameIndex ell) (yFrameIndex (quadraticMatching ell)) = 1 ∧
      ∀ i j : Fin 54, 54 * i.val + j.val < 54 * ell.val + (quadraticMatching ell).val →
        projectedPolar ell (xFrameIndex i) (yFrameIndex j) = 0 := by
  constructor
  · rw [archived_polar_mixed, archived_mixed_pivots]
  · intro i j before
    rw [archived_polar_mixed]
    exact archived_mixed_zero_before ell i j before

end Brent.QuadraticData
