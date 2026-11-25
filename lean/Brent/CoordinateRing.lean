import Brent.StrassenSquare
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Tactic.DeriveFintype

open scoped BigOperators

namespace Brent

inductive Mode
  | u | v | w
  deriving DecidableEq, Fintype

/-- Variable coordinates are summand, mode, then matrix entry, in Appendix A.1 order. -/
abbrev Variable (α ι : Type*) := ι × Mode × (α × α)

/-- A row of the Brent system, in lexicographic tensor-coordinate order. -/
abbrev EquationIndex (α : Type*) := (α × α) × (α × α) × (α × α)

theorem square_variable_count : Fintype.card (Variable SquareVertex SquareSummand) = 2352 := by
  simp [Variable, SquareVertex, SquareSummand, Fintype.card_prod, show Fintype.card Mode = 3 by decide]

theorem square_equation_count : Fintype.card (EquationIndex SquareVertex) = 4096 := by
  simp [EquationIndex, SquareVertex, Fintype.card_prod]

namespace Decomposition

variable {R α ι : Type*}

def coordinates (d : Decomposition R α ι) : Variable α ι → R
  | (s, .u, a) => d.u s a
  | (s, .v, a) => d.v s a
  | (s, .w, a) => d.w s a

end Decomposition

section CoordinateRing

variable (R α ι : Type*) [CommRing R] [DecidableEq α] [Fintype ι]

/-- The actual cubic equation, with output-entry convention matching §2. -/
noncomputable def equation (a b c : α × α) : MvPolynomial (Variable α ι) R :=
  (∑ s, MvPolynomial.X (s, Mode.u, a) * MvPolynomial.X (s, Mode.v, b) *
    MvPolynomial.X (s, Mode.w, c)) - MvPolynomial.C (matrixMultiplicationEntry R a b c)

noncomputable def brentIdeal : Ideal (MvPolynomial (Variable α ι) R) :=
  Ideal.span (Set.range (fun (abc : EquationIndex α) =>
    equation R α ι abc.1 abc.2.1 abc.2.2))

/-- The ordered Brent scheme is the spectrum of this quotient. -/
abbrev CoordinateRing := MvPolynomial (Variable α ι) R ⧸ brentIdeal R α ι

variable {R α ι}

theorem eval_equation (d : Decomposition R α ι) (a b c : α × α) :
    MvPolynomial.eval d.coordinates (equation R α ι a b c) =
      d.entry a b c - matrixMultiplicationEntry R a b c := by
  simp [equation, Decomposition.entry, Decomposition.coordinates, map_sum]

noncomputable def pointEvaluation (d : Decomposition R α ι) (h : d.Solves) :
    CoordinateRing R α ι →+* R :=
  Ideal.Quotient.lift (brentIdeal R α ι) (MvPolynomial.eval d.coordinates) <| by
    intro p hp
    have hker : brentIdeal R α ι ≤ RingHom.ker (MvPolynomial.eval d.coordinates) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨a, b, c⟩, rfl⟩
      change MvPolynomial.eval d.coordinates (equation R α ι a b c) = 0
      rw [eval_equation, h a b c, sub_self]
    exact hker hp

theorem pointEvaluation_surjective (d : Decomposition R α ι) (h : d.Solves) :
    Function.Surjective (pointEvaluation d h) := by
  intro x
  exact ⟨Ideal.Quotient.mk _ (MvPolynomial.C x), MvPolynomial.eval_C x⟩

end CoordinateRing

section LocalRing

variable (k : Type*) [Field k]

abbrev SquareCoordinateRing := CoordinateRing k SquareVertex SquareSummand

noncomputable def squareEvaluation : SquareCoordinateRing k →+* k :=
  pointEvaluation (strassenSquare k) (strassenSquare_solves k)

noncomputable def squareMaximalIdeal : Ideal (SquareCoordinateRing k) :=
  RingHom.ker (squareEvaluation k)

instance squareMaximalIdeal_isMaximal : (squareMaximalIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (pointEvaluation_surjective (strassenSquare k) (strassenSquare_solves k))

/-- The local ring of the actual ordered Brent scheme at the recursive point. -/
noncomputable abbrev SquareLocalRing := Localization.AtPrime (squareMaximalIdeal k)

/-- Completion at the maximal ideal of the actual local Brent ring. -/
noncomputable abbrev SquareCompletion :=
  AdicCompletion (R := SquareLocalRing k) (IsLocalRing.maximalIdeal (SquareLocalRing k)) (SquareLocalRing k)

/-- The quantity in the main theorem. -/
noncomputable def squareLocalDimension : WithBot ℕ∞ :=
  ringKrullDim (SquareLocalRing k)

end LocalRing
end Brent
