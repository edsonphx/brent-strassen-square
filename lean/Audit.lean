import Brent
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let theorems := [
    ``Brent.strassen_solves,
    ``Brent.strassenSquare_solves,
    ``Brent.square_variable_count,
    ``Brent.square_equation_count,
    ``Brent.pointEvaluation_surjective,
    ``Brent.Decomposition.entry_line,
    ``Brent.Decomposition.solves_changeBasis,
    ``Brent.Decomposition.solves_rescale,
    ``Brent.leftFamily_solves,
    ``Brent.rightFamily_solves,
    ``Brent.leftFamily_at_identity,
    ``Brent.rightFamily_at_identity,
    ``Brent.quadraticMatching_disjoint,
    ``Brent.SparseRow.coefficient_subScaled,
    ``Brent.rowSpan_eq_of_elimination,
    ``Brent.linearIndependent_of_pivots,
    ``Brent.rowRank_eq_of_elimination,
    ``Brent.SparseRow.rank_of_checked_trace,
    ``Brent.Decomposition.jacobianColumn_eq,
    ``Brent.squareJacobianColumn_correct,
    ``Brent.square_nullity_of_rank,
    ``Brent.quotient_dimension_of_le_nilradical,
    ``Brent.localDimension_le_of_power_le_span_sup_pow
  ]
  for name in theorems do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun dependency =>
      !([``propext, ``Classical.choice, ``Quot.sound].contains dependency))
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.toList}"

#print axioms Brent.strassenSquare_solves
#print axioms Brent.leftFamily_solves
#print axioms Brent.rightFamily_solves
#print axioms Brent.localDimension_le_of_power_le_span_sup_pow
