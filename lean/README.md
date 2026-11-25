# Lean formalization of the Brent scheme at the Strassen square

The formalization targets the ordered Brent scheme in *Exact Local Dimension of
the Brent Variety V(4,4,4 | 49) at the Recursive Strassen-Square Point via
Quadratic Obstructions* by Edson Soares de Souza.

The source revision is `00f45dc3ec9aaaaf2e7bae0a09a1a8623f18e300`. The main
declaration to prove is an equality with `Brent.squareLocalDimension k`, the
Krull dimension of the localization of the Brent coordinate ring at the
maximal ideal cut out by the exact recursive point. See [STATUS.md](STATUS.md)
for the proof dependencies and current scope.

## Build and audit

Install [Elan](https://lean-lang.org/install/). The toolchain and Mathlib
revision are pinned in this directory.

```bash
cd lean
lake exe cache get $(find Brent -name '*.lean' -exec sed -n '/^import Mathlib/s/^import //p' {} + | sort -u)
lake build Brent
lake build Brent.KernelCheck.SquareJacobianRank
lake build Brent.KernelCheck.QuadraticCertificates
lake build Brent.KernelCheck.TangentFrame
lake build Brent.KernelCheck.FamilyQuadratics
lake env lean Audit.lean
for file in Brent/*.lean Brent/KernelCheck/*.lean; do
  module=${file%.lean}
  lake env leanchecker -v "${module//\//.}"
done
```

The cache step is optional when building the dependencies from source. The
branch CI runs the same commands.

`Audit.lean` checks the transitive axioms of the listed theorems against
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
`leanchecker` replays the project's declarations in Lean's kernel against
their imported environments. Modules replay sequentially to limit memory use.
The finite Strassen and matching identities use kernel reduction with `decide`.
The main library uses only the three audited standard axioms.

## Exact Jacobian rank

`Brent.square_jacobian_rank` and `Brent.square_jacobian_nullity` concern the
Jacobian of the actual ordered Brent equations. The kernel replays 2,352 signed
row identities, checks all 2,101 unit pivots, and verifies coverage and pivot
order. Integer coefficients allow the result over every field. The numerical
checks use `decide +kernel` in bounded-size batches. A clean build of the rank
target takes several minutes.

The elimination step compares signed integers in radix 4096. The checker also
verifies an absolute bound on each coefficient of the difference. A zero
encoding then forces all coefficients to be zero, by taking successive
residues in the radix. `SparseRow.rank_of_checked_radix_trace` connects these
identities to the field-linear rank.

Python and NumPy can replay the paper's certificates independently.
`python3 tools/generate_jacobian_trace.py` recreates the candidate trace from
the frozen factor file. `python3 tools/generate_rank_checks.py` regenerates the
batch declarations. Lean reconstructs the original columns and independently
checks the decoded trace.

## The 54 mixed quadratic forms

`Brent.KernelCheck.QuadraticCertificates` checks the 54 archived covectors
against the verified Jacobian pivots over `ZMod 3`. It then reconstructs
the polar quadratic contribution on each of the 2,916 pairs of frozen
left and right directions, and checks all 157,464 projected coefficients.
The exports certify coefficient-one matching positions and vanishing of
earlier mixed coefficients. The audit enforces the same kernel trust
boundary as the rank proof.

The source data and batch proofs can be regenerated with
`tools/generate_quadratic_data.py`, `tools/generate_annihilator_checks.py`,
`tools/generate_mixed_data.py`, and `tools/generate_mixed_checks.py`.
The remaining mathematical obligations are recorded in [STATUS.md](STATUS.md).

## Archived tangent frame

`Brent.KernelCheck.TangentFrame` certifies the 251 archived integer directions,
their annihilation by the signed Jacobian, and the ranks 143, 54, and 54 of the
three blocks over every field. It identifies the 108 directions used by the
mixed certificate with the left and right blocks of this frame.

`Brent.KernelCheck.FamilyQuadratics` verifies the origins of all 251
directions by differentiating the two exact recursive charts. It certifies
197 independent derivatives in each chart. The common 143 directions
come from global basis changes and term rescalings. Using two dual-number
parameters, it proves that all coefficients outside the mixed block vanish,
including each diagonal square coefficient. The mixed table agrees with
the quadratic coefficients evaluated on the full frame. Each of the 54
coefficient-one leading monomials is therefore certified for an actual
projected obstruction.

The chart-origin data and batch declarations can be regenerated with
`tools/generate_family_origins.py` and `tools/generate_origin_checks.py`.

The ordering of `SquareVertex = Fin 2 × Fin 2` and
`SquareSummand = Fin 7 × Fin 7` is `finProdFinEquiv`'s lexicographic
ordering. Given a summand `(i,j)`, mode `m`, and flattened matrix
entry `a`, the paper's variable column is `48 * (7 * i + j) + 16 * m + a`.
The equation row for flattened matrix entries `a,b,c` is `256*a + 16*b + c`.
The output factor is in row-major output order.
