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
lake build
lake env lean Audit.lean
for file in Brent/*.lean; do
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

## Optional compiler-backed Jacobian rank

```bash
lake build Brent.CompilerCheck.SquareJacobianRank
lake env lean RankAudit.lean
```

The optional theorem verifies the signed sparse elimination trace against the
Jacobian reconstructed from the Lean definition of the recursive point.
`SparseRow.rank_of_checked_trace` proves that checked trace data certify rank
over any field. This implementation uses `native_decide` for four finite
predicates, so the final rank and nullity declarations depend on Lean's compiler
in addition to the kernel. The main library does not import this optional module.

Python and NumPy can replay the original paper's certificates independently.
`python3 tools/generate_jacobian_trace.py` recreates the candidate trace from
the frozen factor file. Lean checks the decoded trace and reconstructs the
matrix independently of the generator.

The ordering of `SquareVertex = Fin 2 × Fin 2` and
`SquareSummand = Fin 7 × Fin 7` is `finProdFinEquiv`'s lexicographic
ordering. Given a summand `(i,j)`, mode `m`, and flattened matrix
entry `a`, the paper's variable column is `48 * (7 * i + j) + 16 * m + a`.
The equation row for flattened matrix entries `a,b,c` is `256*a + 16*b + c`.
The output factor is in row-major output order.
