# Proof status

Proved in Lean:

- over every field `k : Type`, `197 ≤ squareLocalDimension k ≤ 251`;
- over every field of characteristic three,
  `squareLocalDimension k = 197` (`squareLocalDimension_eq_197_of_charThree`);
- over every field of characteristic zero,
  `squareLocalDimension k = 197` (`squareLocalDimension_eq_197_of_charZero`);
- over every field with `2 ≠ 0`, in particular in characteristics three and zero, the local
  Hilbert function of the Brent local ring starts `(1, 251, 30978)`
  (`HilbertValues.hilbert_initial`, `hilbert_initial_charP_three`, `hilbert_initial_charZero`).

The formal branches and their intersection in §6 remain open in Lean.

| Paper dependency | Lean declaration | Status |
| --- | --- | --- |
| §2, signed Strassen table and its recursive square | `strassen_solves`, `strassenSquare_solves` | Kernel-verified. The lift of the signed integral identity works over every commutative ring. |
| §2, ordered Brent scheme at the recursive point | `equation`, `brentIdeal`, `SquareCoordinateRing`, `squareMaximalIdeal`, `SquareLocalRing`, `SquareCompletion`, `squareLocalDimension` | Defined. The kernel of the surjective evaluation is proved maximal, and the 2,352 and 4,096 index counts are verified. |
| §2, reduction and Krull dimension | `quotient_dimension_of_le_nilradical` | Kernel-verified for any commutative ring, including the Brent local ring. |
| §3, identity on both families | `leftFamily_solves`, `rightFamily_solves`, `solves_changeBasis`, `solves_rescale` | Kernel-verified over any commutative ring. Both families specialize to the marked point at identity parameters. The first-order and two-parameter dual-number coefficient identities are kernel-verified in `DeformationJets.lean`. `chart_independent_derivatives` exhibits 197 independent first derivatives in each chart. |
| §3, lower bound `dim ≥ 197` | `LowerBound.le_squareLocalDimension`, `ringKrullDim_le_of_maximalIdeal_le`, `le_ringKrullDim_affineGerm`, `mem_sq_of_germJet` | Kernel-verified over every field. The 197 left-chart directions are combined into one exact family over `k[t₁,…,t₁₉₇]` localized at the origin. This gives a local homomorphism from the Brent local ring. The 197 independent chart derivatives make it surjective on cotangent spaces, and a system-of-parameters argument (Nakayama plus Krull's height theorem) gives `dim ≥ 197`. This replaces the paper's formal-inverse/completion argument. |
| §4, quadratic expansion and Jacobian columns | `Decomposition.entry_line`, `Decomposition.jacobianColumn` | Cubic expansion and sparse reconstruction of the actual Jacobian proved. `square_jacobian_rank` and `square_jacobian_nullity` certify 2,101 and 251 in the kernel over every field. The 54 archived covectors annihilate the actual Jacobian modulo three by `archived_covectors_annihilate`. |
| §3, frozen tangent frame | `archived_frame_rank`, `archived_frame_tangent`, `archived_frame_split`, `archived_left_coordinates`, `archived_right_coordinates` | The kernel checks 251 independent integral kernel directions and block ranks 143, 54, and 54. The X and Y blocks match the mixed operands. `archived_origin` identifies each direction with the differential of its exact chart. |
| §4, matching | `quadraticMatching_bijective`, `quadraticMatching_disjoint` | All 157,464 mixed coefficients, coefficient-one leaders, earlier mixed zeros, and disjoint matched supports are verified. `archived_nonmixed_zero` and `archived_square_zero` prove all other coefficients vanish. `archived_polar_leading` identifies the leaders of the actual 54 projected quadratic forms. |
| §§2–4, tangent (embedding-dimension) upper bound | `pointLocalDimension_le`, `squareLocalDimension_le_tangent` | Kernel-verified over every field: `squareLocalDimension k ≤ 251`. At any solution the local Krull dimension is at most #variables − Jacobian rank. Supporting lemmas: `ker_eval_eq_span` (ideal of a point), `jacobianEntry_eq_sum`, `equation_eq_expansion` (Taylor expansion of the actual equations via `entry_line`), `maximalIdeal_pointLocalRing`. |
| §4, alternative finite local upper bound | `localDimension_le_of_power_le_span_sup_pow` | Kernel-verified application of Nakayama and Krull's height theorem. |
| §4, upper bound `dim ≤ 197` in characteristic three | `UpperBound.squareLocalDimension_le_197`, `triangular_dim_le`, `pow_succ_le_of_triangular`, `exists_dual_frame`, `quadraticEntry_sub_mem`, `CharThree.*` | Kernel-verified over every field of characteristic three. Tangent coordinates `zᵢ` dual to the 251-vector frame satisfy `y ≡ Σ zᵢ vᵢ (mod 𝔪²)`. Contracting the Taylor expansion with the 54 covectors kills the linear part and gives 54 relations `Σ M_ℓ[a,b] x_a y_b ∈ 𝔪³`. The certified tables are triangular with unit leaders. With the 197 parameters `cᵢ` and `u_ℓ − x_ℓ`, every square `x_ℓ²` reduces to larger indices, so `𝔪⁵⁵ ⊆ (parameters) + 𝔪⁵⁶`, and Krull's height theorem gives `dim ≤ 197`. This elementary monomial reduction replaces the paper's Gröbner/Hilbert–Samuel step. |
| §4, exact dimension in characteristic three | `squareLocalDimension_eq_197_of_charThree` | Kernel-verified: the lower and upper bounds combine to `= 197`. |
| App. A, exact elimination | `SparseRow.coefficient_subScaled` | Sparse integer row operations, span preservation, and exact rank from the signed unit-pivot trace are kernel-verified using bounded radix checks. |
| §5, characteristic-zero transfer and exact dimension | `integer_annihilates`, `integerEntry_cast`, `Transfer.charZero_dim_le`, `CharZeroBound.squareLocalDimension_le_197`, `squareLocalDimension_eq_197_of_charZero` | The kernel checks that the 54 integer covectors annihilate the Jacobian and reduce to the archived covectors modulo three. Graded Nakayama transfer lifts the finite spanning certificate for the upper bound to characteristic zero. The same exact family lower bound then gives dimension 197. |
| §6, Hilbert function `(1, 251, 30978)` | `HilbertInitial.hilbertValue_zero`, `HilbertInitial.hilbertValue_one`, `HilbertTwo.ker_Ψ₂`, `HilbertTwo.hilbertValue_two_add`, `KernelVanishing.nonmixed_zero`, `KernelVanishing.square_zero`, `AugmentedTrace.augmented_rank`, `MixedRank.finrank_Rel`, `HilbertValues.hilbert_initial` | Kernel-verified over every field with `2 ≠ 0`. `H(d)` is the dimension of `𝔪ᵈ/𝔪ᵈ⁺¹`. `H(1) = 251` uses the dual-number jet at every tangent vector. For `H(2)`, second-order jets `p + Σ tᵢvᵢ + ηW` into `k ⊕ k²⁵¹ ⊕ k` identify the relations among the `zᵢzⱼ` with the symmetrized quadratic tables of the full left kernel of the Jacobian, so `H(2) = 31626 − dim Rel` over every field. Two-parameter exact-family jets show that every left-kernel covector kills all non-mixed polar terms. With `2 ≠ 0` it also kills the squares. So `Rel` is the image of `λ ↦ λM` on `ker Jᵗ`, of dimension `2749 − 2101 = 648`. The rank 2,749 of `[J ∣ M]` is replayed in bounded kernel batches. This replaces the paper's residual-generator basis argument. |
| §6, formal branches and their intersection | `Formal.isNoetherianRing_mvPowerSeries` | In progress. Route: take the formal local ring `Â = k⟦z⟧ ⧸ (Brent equations)` directly. This avoids the general theory of `AdicCompletion`. The power-series images of the two exact families give one formal coordinate change `H(c, x, y, n)` with invertible linear part, built by degree-by-degree recursion with no topology. In the new coordinates the branch kernels are `(y, n)` and `(x, n)`, with quotients `k⟦c, x⟧`, `k⟦c, y⟧` and `k⟦c⟧`. Minimality follows from `dim Â ≤ 197`: the degree-55 certificate holds in `Â`, so Nakayama and Krull's height theorem apply. Krull's height theorem needs `Â` Noetherian. Done so far: `R⟦σ⟧` is Noetherian for finite `σ` over a Noetherian `R`, via `R⟦Option σ⟧ ≃+* R⟦σ⟧⟦X⟧`. Still to do: the formal inverse function theorem, the power-series families, the coordinate change, and the dimension count. |
| §6, reduced tangent dimension 251 | — | Open. The two family maps into the reduced germs kill the nilradical, and their 197 + 197 derivatives span all 251 tangent directions. The left-family map exists (`LowerBound.pull`). The right-family analogue is still to be written. |

## Remaining proof graph

- §6: the two formal branches, their 143-dimensional formal intersection, and the reduced
  tangent dimension 251.

## §6 roadmap

Each step is done only when it builds with no `sorry`, `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`, it does not use `native_decide`, and `leanchecker` exits 0.
Each finished step is committed locally on `formalization/lean4` (not pushed). The files live
in `Brent/Formal/`, which does not import the `AugmentedBlocks` chain.

- [x] F0. `isNoetherianRing_mvPowerSeries`: `R⟦σ⟧` is Noetherian for finite `σ` and Noetherian `R`.
- [x] F1. Overlap: when every block parameter is `1`, `value true p = value false p`. This defines
  the common orbit map `γ(c)`.
- [x] F2. "Agree up to degree d" for `MvPowerSeries`, then the formal inverse function theorem
  for any finite `σ` with invertible linear part, by degree recursion (no `subst` iteration).
- [x] F3. Monomial-ideal lemma: the kernel of setting a set of variables to `0` is the ideal they
  generate (via `X_dvd_iff`). Quotient isomorphisms `k⟦c,x,y,n⟧ ⧸ (y,n) ≃ k⟦c,x⟧`, etc.
- [x] F4. The power-series left and right families `L(c,x)` and `R(c,y)` solving the Brent
  equations, built directly over `k⟦t⟧` (unit parameters `1 + Σ tᵢEᵢ`, so no map out of
  `Germ` is needed), with their constant terms and linear parts.
- [ ] F5. `Â := k⟦z⟧ ⧸ (Brent equations)`. Extend the 251 certified frame vectors to a basis
  (`Basis.extend`, no new certificate). Then
  `H(c,x,y,n) = L(c,x) + (R(c,y) − R(c,0)) + N(n)` has invertible linear part, and
  the Brent ideal composed with `H` lies in `(y,n) ∩ (x,n)`.
- [ ] F6. `Â` is local and Noetherian, and `dim Â ≤ 197` via the degree-55 certificate,
  Nakayama, and Krull's height theorem.
- [ ] F7. Branches: `𝔭_L`, `𝔭_R` are prime and minimal, with `Â⧸𝔭_L ≃ k⟦c,x⟧` and
  `Â⧸𝔭_R ≃ k⟦c,y⟧`. They are distinct, and `Â⧸(𝔭_L+𝔭_R) ≃ k⟦c⟧` has dimension 143, in
  characteristic three and zero.
- [ ] F8. The reduced local ring has tangent dimension 251.
- [ ] F9. Audit, README, CI and STATUS updated, and the full `leanchecker` replay passes.
  No open rows remain.

The published `bash verify.sh --full` replay passed independently of Lean
at the pinned source revision. The Jacobian's 2,352 transposed columns admit
a sparse integer elimination with 2,101 unit pivots and 15,124 row
additions in that order. The kernel proves the implication from a checked trace to the rank theorem.
The row identities, pivot checks, and coverage are replayed in separate
kernel batches. The rank and nullity audit permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.
