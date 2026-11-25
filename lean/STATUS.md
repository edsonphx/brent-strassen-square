# Proof status

The dimension-197 theorem is open **in this Lean project** in both
characteristic zero and characteristic three.

| Paper dependency | Lean declaration | Status |
| --- | --- | --- |
| §2, signed Strassen table and its recursive square | `strassen_solves`, `strassenSquare_solves` | Kernel-verified. The lift of the signed integral identity works over every commutative ring. |
| §2, ordered Brent scheme at the recursive point | `equation`, `brentIdeal`, `SquareCoordinateRing`, `squareMaximalIdeal`, `SquareLocalRing`, `SquareCompletion`, `squareLocalDimension` | Defined. The kernel of the surjective evaluation is proved maximal, and the 2,352 and 4,096 index counts are verified. |
| §2, reduction and Krull dimension | `quotient_dimension_of_le_nilradical` | Kernel-verified for any commutative ring, including the Brent local ring. |
| §3, identity on both families | `leftFamily_solves`, `rightFamily_solves`, `solves_changeBasis`, `solves_rescale` | Kernel-verified over any commutative ring. Both families specialize to the marked point at identity parameters. The first-order and two-parameter dual-number coefficient identities are kernel-verified in `DeformationJets.lean`. The 197-dimensional differential certificates and the connection to local dimension remain open. |
| §4, quadratic expansion and Jacobian columns | `Decomposition.entry_line`, `Decomposition.jacobianColumn` | Cubic expansion and sparse reconstruction of the actual Jacobian proved. `square_jacobian_rank` and `square_jacobian_nullity` certify 2,101 and 251 in the kernel over every field. The 54 archived covectors annihilate the actual Jacobian modulo three by `archived_covectors_annihilate`. |
| §4, matching | `quadraticMatching_bijective`, `quadraticMatching_disjoint` | All 157,464 mixed coefficients, coefficient-one leaders, earlier mixed zeros, and disjoint matched supports are verified. Vanishing of the other quadratic coefficients on the full tangent frame remains open. |
| §4, alternative finite local upper bound | `localDimension_le_of_power_le_span_sup_pow` | Kernel-verified application of Nakayama and Krull's height theorem. It still needs a parameter-system certificate for the actual local ring. |
| App. A, exact elimination | `SparseRow.coefficient_subScaled` | Sparse integer row operations, span preservation, and exact rank from the signed unit-pivot trace are kernel-verified using bounded radix checks. |
| §§5–6, transfer, branches, and Hilbert data | — | Open. |

## Remaining proof graph

- The two family identities feed the differential-rank certificate. That
  rank and a formal inverse (or a local algebraic substitute) give the lower
  bound. The differential alone gives a tangent-space statement.
- The kernel now checks the 54 covectors and all their coefficients on the
  mixed block. Relating these to the full tangent-space initial forms,
  proving the regular sequence implication, and deriving the local upper
  bound remain open. The 2,749 augmented rank and 648 mixed rank are additional inputs to
  the degree-two Hilbert result.
- The characteristic-zero argument requires lifting through the split
  integer-local Jacobian and preserving the resulting dimension bound.
  The dimensions of the formal intersection and of the reduced tangent
  space follow after both bounds and the tangent split are established.

The published `bash verify.sh --full` replay passed independently of Lean
at the pinned source revision. The Jacobian's 2,352 transposed columns admit
a sparse integer elimination with 2,101 unit pivots and 15,124 row
additions in that order. The kernel proves the implication from a checked trace to the rank theorem.
The row identities, pivot checks, and coverage are replayed in separate
kernel batches. The rank and nullity audit permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

Mathlib supplies ideal localization, the adic completion construction,
prime-spectrum and quotient APIs, Nakayama's lemma, and Krull's height
theorem. The pinned revision was searched for the Hilbert–Samuel
dimension comparison, the relevant formal inverse statement, and
Buchberger's product criterion. An API covering the published argument
directly has not been identified. One route for the upper bound is
to prove a finite-order parameter-system certificate using the 54
quadratic leaders, then apply the verified local dimension lemma.
