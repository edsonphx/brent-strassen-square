import Brent.EmbeddingDimension
import Brent.KernelCheck.SquareJacobianRank

namespace Brent

/-- The local dimension at the recursive Strassen-square point is at most the tangent
dimension 251 = 2352 - 2101. This is the embedding-dimension bound; the paper's sharper
upper bound 197 additionally uses the 54 quadratic obstructions. -/
theorem squareLocalDimension_le_tangent (k : Type*) [Field k] :
    squareLocalDimension k ≤ 251 := by
  have h := pointLocalDimension_le (strassenSquare k) (strassenSquare_solves k)
  rw [square_jacobian_rank, square_variable_count] at h
  exact h

end Brent
