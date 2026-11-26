import Brent.Formal.Component

open Lean Elab Command

run_cmd do
  let theorems := [
    ``Brent.Formal.Component.ringKrullDim_locQ_le,
    ``Brent.Formal.Component.ringKrullDim_locQ_succ_le,
    ``Brent.Formal.Component.generic_map_evS,
    ``Brent.Formal.Component.family_kills,
    ``Brent.Formal.Component.derivD_independent,
    ``Brent.Formal.Component.localDim_closure,
    ``Brent.Formal.Component.prime_eq_ker,
    ``Brent.Formal.Component.vanishingIdeal_isPrime,
    ``Brent.Formal.Component.familyClosure_maximal,
    ``Brent.Formal.Component.familyClosure_isComponent,
    ``Brent.Formal.Component.ker_mem_minimalPrimes,
    ``Brent.Formal.Component.ringKrullDim_closure
  ]
  for name in theorems do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun dependency =>
      !([``propext, ``Classical.choice, ``Quot.sound].contains dependency))
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.toList}"
