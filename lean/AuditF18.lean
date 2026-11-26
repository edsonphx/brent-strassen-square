import Brent.Census.AlphaTensor

open Lean Elab Command

run_cmd do
  let theorems := [
    ``Brent.Census.isClosed_rankBound,
    ``Brent.Census.det_submatrix_eq_zero_of_rank_lt,
    ``Brent.Census.mem_rankBound_of_profileBound,
    ``Brent.Census.dominated_of_formula,
    ``Brent.Census.profileBound_of_dominated,
    ``Brent.Census.strassen_factor,
    ``Brent.Census.rank_value_le,
    ``Brent.Census.profileBound_family,
    ``Brent.Census.closure_saturation_subset_rankBound,
    ``Brent.Census.BoundW.not_mem_rankBound,
    ``Brent.Census.BoundW.not_mem_closure,
    ``Brent.Census.boundWitnesses_check,
    ``Brent.Census.boundWitnesses_indices,
    ``Brent.Census.alphaTensor_bound_excluded
  ]
  for name in theorems do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun dependency =>
      !([``propext, ``Classical.choice, ``Quot.sound].contains dependency))
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.toList}"
