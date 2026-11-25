# Proof status

The dimension-197 theorem is open **in this Lean project** in both
characteristic zero and characteristic three.

| Paper dependency | Lean declaration | Status |
| --- | --- | --- |
| §2, signed Strassen table and its recursive square | `strassen_solves`, `strassenSquare_solves` | Kernel-verified. The lift of the signed integral identity works over every commutative ring. |
| §2, ordered Brent scheme at the recursive point | `equation`, `brentIdeal`, `SquareCoordinateRing`, `squareMaximalIdeal`, `SquareLocalRing`, `SquareCompletion`, `squareLocalDimension` | Defined. The kernel of the surjective evaluation is proved maximal, and the 2,352 and 4,096 index counts are verified. |
| §2, reduction and Krull dimension | `quotient_dimension_of_le_nilradical` | Kernel-verified for any commutative ring, including the Brent local ring. |
| §3, identity on both families | `leftFamily_solves`, `rightFamily_solves`, `solves_changeBasis`, `solves_rescale` | Kernel-verified over any commutative ring. The 197-dimensional differential certificates and the connection to local dimension remain open. |
| §4, quadratic expansion and Jacobian columns | `Decomposition.entry_line`, `Decomposition.jacobianColumn` | Cubic expansion proved. Ranks and left-kernel calculations remain open. |
| §4, matching | `quadraticMatching_bijective`, `quadraticMatching_disjoint` | The permutation and disjoint support of the proposed leaders are verified. Verification that the 54 original quadrics have these leaders remains open. |
| §4, alternative finite local upper bound | `localDimension_le_of_power_le_span_sup_pow` | Kernel-verified application of Nakayama and Krull's height theorem. It still needs a parameter-system certificate for the actual local ring. |
| App. A, exact elimination | `SparseRow.coefficient_subScaled` | Sound sparse integer row subtraction. The row-span and triangular-minor implications are also proved in `RankCertificate.lean`. The actual matrix replay remains open. |
| §§5–6, transfer, branches, and Hilbert data | — | Open. |

## Remaining proof graph

- The two family identities feed the differential-rank certificate. That
  rank and a formal inverse (or a local algebraic substitute) give the lower
  bound. The differential alone gives a tangent-space statement.
- The Jacobian split and the 54 left-kernel contractions produce the
  quadratic initial forms. Their matching is the input to the local upper
  bound. The 2,749 augmented rank and 648 mixed rank are additional inputs to
  the degree-two Hilbert result.
- The characteristic-zero argument requires lifting through the split
  integer-local Jacobian and preserving the resulting dimension bound.
  The dimensions of the formal intersection and of the reduced tangent
  space follow after both bounds and the tangent split are established.

The published `bash verify.sh --full` replay passed independently of Lean
at the pinned source revision. The Jacobian's 2,352 transposed columns admit
a sparse integer elimination with 2,101 unit pivots and 15,124 row
additions in that order. This is a sizing probe for a certificate, outside
the Lean trust boundary until the matrix-level checker is proved and run.

Mathlib supplies ideal localization, the adic completion construction,
prime-spectrum and quotient APIs, Nakayama's lemma, and Krull's height
theorem. The pinned revision was searched for the Hilbert–Samuel
dimension comparison, the relevant formal inverse statement, and
Buchberger's product criterion. An API covering the published argument
directly has not been identified. One route for the upper bound is
to prove a finite-order parameter-system certificate using the 54
quadratic leaders, then apply the verified local dimension lemma.
