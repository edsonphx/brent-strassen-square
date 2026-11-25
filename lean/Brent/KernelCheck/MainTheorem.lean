import Brent.KernelCheck.UpperBound
import Brent.KernelCheck.LowerBound

/-!
# The exact local dimension in characteristic three

Combining the cotangent-surjective lower bound with the triangular-quadric upper bound:
over every field of characteristic three, the local dimension of the Brent variety
`V(4,4,4 | 49)` at the recursive Strassen-square point is exactly `197`.
-/

namespace Brent

theorem squareLocalDimension_eq_197_of_charThree (k : Type) [Field k] [CharP k 3] :
    squareLocalDimension k = 197 :=
  le_antisymm (UpperBound.squareLocalDimension_le_197 k) (LowerBound.le_squareLocalDimension k)

end Brent
