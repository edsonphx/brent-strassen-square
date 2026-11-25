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
lake exe cache get $(sed -n '/^import Mathlib/s/^import //p' Brent/*.lean | sort -u)
lake build
lake env lean Audit.lean
lake env leanchecker -v Brent
```

The cache step is optional when building the dependencies from source. The
branch CI runs the same commands.

`Audit.lean` checks the transitive axioms of the listed theorems against
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
`leanchecker` replays the project's declarations in Lean's kernel against
their imported environments. The finite Strassen and matching identities
use kernel reduction with `decide`. No project-specific axioms or native
evaluation oracles are used. Python and NumPy can replay the original
paper's certificates independently.

The ordering of `SquareVertex = Fin 2 × Fin 2` and
`SquareSummand = Fin 7 × Fin 7` is `finProdFinEquiv`'s lexicographic
ordering. Given a summand `(i,j)`, mode `m`, and flattened matrix
entry `a`, the paper's variable column is `48 * (7 * i + j) + 16 * m + a`.
The equation row for flattened matrix entries `a,b,c` is `256*a + 16*b + c`.
The output factor is in row-major output order.
