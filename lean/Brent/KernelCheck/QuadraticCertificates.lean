import Brent.Generated.AnnihilatorChecks
import Brent.Generated.MixedChecks

open scoped BigOperators

namespace Brent.QuadraticData

/-- Each of the 54 finite covectors belongs to the left kernel of the Brent Jacobian. -/
theorem archived_covectors_annihilate (ell : Fin 54) (x : Variable SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex,
      (strassenSquare K).jacobianColumn x e.1 e.2.1 e.2.2 *
        functionalEntry ell (squareEquationNumber e) = 0 :=
  annihilates_jacobian checkedAnnihilator ell x

/-- The coefficient of the mixed monomial at the indicated two directions. -/
def projectedMixed (ell i j : Fin 54) : K :=
  ∑ e : EquationIndex SquareVertex,
    (mixedEntry i j e : K) * functionalEntry ell (squareEquationNumber e)

private theorem checkedMixed (i j : Fin 54) : checkMixed i j = true := by
  have h := checkedMixedNumber (finProdFinEquiv (i, j))
  simpa only [checkMixedNumber, Equiv.symm_apply_apply] using h

/-- All 157,464 literal mixed coefficients agree with the Brent contractions. -/
theorem archived_mixed_coefficients (ell i j : Fin 54) :
    projectedMixed ell i j = (SparseRow.coefficient ell.val (literalMixed i j) : K) :=
  mixed_coefficient i j ell (checkedMixed i j)

/-- All coefficients lexicographically before the matching pair are zero. -/
theorem archived_mixed_zero_before (ell i j : Fin 54)
    (before : 54 * i.val + j.val < 54 * ell.val + (quadraticMatching ell).val) :
    projectedMixed ell i j = 0 :=
  mixed_zero_before i j ell (checkedMixed i j) before

/-- The matching picks a coefficient-one leading mixed monomial in each form. -/
theorem archived_mixed_pivots (ell : Fin 54) :
    projectedMixed ell ell (quadraticMatching ell) = 1 :=
  mixed_pivot_one ell (checkedMixed ell (quadraticMatching ell))

end Brent.QuadraticData
