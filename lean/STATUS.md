# Proof status

Proved in Lean, over every field `k : Type`:
`197 ≤ squareLocalDimension k ≤ 251`. The equality `= 197` is still open
(the upper bound needs the quadratic-obstruction argument of §4).

| Paper dependency | Lean declaration | Status |
| --- | --- | --- |
| §2, signed Strassen table and its recursive square | `strassen_solves`, `strassenSquare_solves` | Kernel-verified. The lift of the signed integral identity works over every commutative ring. |
| §2, ordered Brent scheme at the recursive point | `equation`, `brentIdeal`, `SquareCoordinateRing`, `squareMaximalIdeal`, `SquareLocalRing`, `SquareCompletion`, `squareLocalDimension` | Defined. The kernel of the surjective evaluation is proved maximal, and the 2,352 and 4,096 index counts are verified. |
| §2, reduction and Krull dimension | `quotient_dimension_of_le_nilradical` | Kernel-verified for any commutative ring, including the Brent local ring. |
| §3, identity on both families | `leftFamily_solves`, `rightFamily_solves`, `solves_changeBasis`, `solves_rescale` | Kernel-verified over any commutative ring. Both families specialize to the marked point at identity parameters. The first-order and two-parameter dual-number coefficient identities are kernel-verified in `DeformationJets.lean`. `chart_independent_derivatives` exhibits 197 independent first derivatives in each chart. The deduction of a local dimension lower bound remains open. |
| §3, lower bound `dim ≥ 197` | `LowerBound.le_squareLocalDimension`, `ringKrullDim_le_of_maximalIdeal_le`, `le_ringKrullDim_affineGerm`, `mem_sq_of_germJet` | Kernel-verified over every field. The 197 left-chart directions are combined into one exact family over `k[t₁,…,t₁₉₇]` localized at the origin. This gives a local homomorphism from the Brent local ring. The 197 independent chart derivatives make it surjective on cotangent spaces, and a system-of-parameters argument (Nakayama plus Krull's height theorem) gives `dim ≥ 197`. This replaces the paper's formal-inverse/completion argument. |
| §4, quadratic expansion and Jacobian columns | `Decomposition.entry_line`, `Decomposition.jacobianColumn` | Cubic expansion and sparse reconstruction of the actual Jacobian proved. `square_jacobian_rank` and `square_jacobian_nullity` certify 2,101 and 251 in the kernel over every field. The 54 archived covectors annihilate the actual Jacobian modulo three by `archived_covectors_annihilate`. |
| §3, frozen tangent frame | `archived_frame_rank`, `archived_frame_tangent`, `archived_frame_split`, `archived_left_coordinates`, `archived_right_coordinates` | The kernel checks 251 independent integral kernel directions and block ranks 143, 54, and 54. The X and Y blocks match the mixed operands. `archived_origin` identifies each direction with the differential of its exact chart. |
| §4, matching | `quadraticMatching_bijective`, `quadraticMatching_disjoint` | All 157,464 mixed coefficients, coefficient-one leaders, earlier mixed zeros, and disjoint matched supports are verified. `archived_nonmixed_zero` and `archived_square_zero` prove all other coefficients vanish. `archived_polar_leading` identifies the leaders of the actual 54 projected quadratic forms. |
| §§2–4, tangent (embedding-dimension) upper bound | `pointLocalDimension_le`, `squareLocalDimension_le_tangent` | Kernel-verified over every field: `squareLocalDimension k ≤ 251`. At any solution the local Krull dimension is at most #variables − Jacobian rank. Supporting lemmas: `ker_eval_eq_span` (ideal of a point), `jacobianEntry_eq_sum`, `equation_eq_expansion` (Taylor expansion of the actual equations via `entry_line`), `maximalIdeal_pointLocalRing`. |
| §4, alternative finite local upper bound | `localDimension_le_of_power_le_span_sup_pow` | Kernel-verified application of Nakayama and Krull's height theorem. It still needs a parameter-system certificate for the actual local ring. |
| App. A, exact elimination | `SparseRow.coefficient_subScaled` | Sparse integer row operations, span preservation, and exact rank from the signed unit-pivot trace are kernel-verified using bounded radix checks. |
| §§5–6, transfer, branches, and Hilbert data | — | Open. |

## Remaining proof graph

- Proved so far: `squareLocalDimension k ≤ 251` (tangent bound). The paper's
  bound 197 still needs the 54 quadratic obstructions to cut the remaining
  54 dimensions, e.g. a `d = 2` instance of
  `localDimension_le_of_power_le_span_sup_pow` with 197 parameters.

- The kernel checks all coefficients of the 54 projected quadrics on the
  tangent frame. The formal elimination step, regular-sequence implication,
  and local upper bound remain open. The 2,749 augmented rank and 648 mixed
  rank are additional inputs to the degree-two Hilbert result.
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
