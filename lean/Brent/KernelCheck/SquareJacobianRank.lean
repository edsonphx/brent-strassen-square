import Brent.Generated.RankChecks

namespace Brent

/-- Rank 2101 for the Brent differential, from kernel-verified integer certificates. -/
theorem square_jacobian_rank (k : Type*) [Field k] :
    Module.finrank k (Submodule.span k (Set.range (fun x : Variable SquareVertex SquareSummand =>
      fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) = 2101 :=
  JacobianTrace.rank_of_kernel_checks JacobianTrace.checkedSteps JacobianTrace.checkedAuxiliary k

/-- The kernel of the linearized Brent equations has dimension 251. -/
theorem square_jacobian_nullity (k : Type*) [Field k] :
    Module.finrank k (LinearMap.ker (squareDifferential k)) = 251 :=
  square_nullity_of_rank k 2101 (square_jacobian_rank k)

end Brent
