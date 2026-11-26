import Brent.Theorem11

open Lean Elab Command

run_cmd do
  let theorems := [
    ``Brent.squareLocalDimension_eq_197,
    ``Brent.reduced_localDimension_eq_197,
    ``Brent.sqBranchPrime_minimal,
    ``Brent.hilbert_initial_values,
    ``Brent.main_theorem
  ]
  for name in theorems do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun dependency =>
      !([``propext, ``Classical.choice, ``Quot.sound].contains dependency))
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.toList}"
