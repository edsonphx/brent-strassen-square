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

- for the formal local ring `Â = k⟦z⟧ ⧸ (centered Brent equations)` over every field of
  characteristic three or zero: `Â` is Noetherian local with `dim Â ≤ 197`; the branch primes
  `𝔭_L`, `𝔭_R` are distinct minimal primes with `Â ⧸ 𝔭_L ≃ k⟦c, x⟧` and `Â ⧸ 𝔭_R ≃ k⟦c, y⟧`
  (dimension 197 each), and `Â ⧸ (𝔭_L + 𝔭_R) ≃ k⟦c⟧` has dimension 143
  (`Formal.branchPrime_minimal_charThree`, `Formal.branchPrime_minimal_charZero`,
  `Formal.branchPrime_ne`, `Formal.intersectionEquiv`, `Formal.ringKrullDim_intersection`);
- over every field, the reduced local ring has tangent dimension 251
  (`Formal.hilbertValue_reduced_one`);
- over every field, the paper's `SquareCompletion` (the `𝔪`-adic completion of the Brent local
  ring) is isomorphic to `Â` (`Formal.sqEquiv`). Over every field of characteristic three or zero,
  the statements above about `Â` therefore hold for `SquareCompletion` itself: it is Noetherian
  local with dimension at most 197, with distinct minimal primes `𝔭_L`, `𝔭_R`, branch quotients
  `k⟦c, x⟧`, `k⟦c, y⟧`, and intersection `k⟦c⟧` of dimension 143
  (`Formal.ringKrullDim_squareCompletion_le_charThree`, `Formal.sqBranchPrime_minimal_charThree`,
  `Formal.sqBranchPrime_minimal_charZero`, `Formal.sqBranchPrime_ne`, `Formal.sqBranchQuotEquiv`,
  `Formal.sqIntersectionEquiv`, `Formal.ringKrullDim_sqIntersection`);
- over every field of characteristic three or zero, the reduced local ring is not regular:
  the reduced Brent variety is singular at the recursive point
  (`Formal.not_isRegularLocalRing_Ared_charThree`, `Formal.not_isRegularLocalRing_Ared_charZero`);
- over every field with `2 ≠ 0`, `H(2) = 30978` holds for `Â` and for `SquareCompletion`
  (`Formal.hilbertValue_two_Ahat`, `Formal.hilbertValue_two_squareCompletion`), while the reduced
  union of the two branches `Â ⧸ (𝔭_L ⊓ 𝔭_R)` has `H(2) = binom(252, 2) − 54 · 54 = 28710`
  (`Formal.hilbertValue_two_twoBranch`). Hence `𝔭_L ⊓ 𝔭_R ≠ 0` in `SquareCompletion`, so
  `SquareCompletion` is nonreduced or has a minimal prime other than `𝔭_L` and `𝔭_R`
  (`Formal.sqBranchPrime_inf_ne_bot`, `Formal.not_isReduced_or_extra_minimalPrime_charThree`,
  `Formal.not_isReduced_or_extra_minimalPrime_charZero`).

No §6 rows remain open.

| Paper dependency | Lean declaration | Status |
| --- | --- | --- |
| §2, signed Strassen table and its recursive square | `strassen_solves`, `strassenSquare_solves` | Kernel-verified. The lift of the signed integral identity works over every commutative ring. |
| §2, ordered Brent scheme at the recursive point | `equation`, `brentIdeal`, `SquareCoordinateRing`, `squareMaximalIdeal`, `SquareLocalRing`, `SquareCompletion`, `squareLocalDimension` | Defined. `SquareCompletion` is identified with `Â` in the §6 completion row. The kernel of the surjective evaluation is proved maximal, and the 2,352 and 4,096 index counts are verified. |
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
| §6, formal branches and their intersection | `Formal.isNoetherianRing_mvPowerSeries`, `Formal.subst_bijective_equiv`, `Formal.ker_killCompl`, `Formal.psFamily_solves`, `Formal.H_bijective`, `Formal.map_brentPS_le`, `Formal.ringKrullDim_Ahat_le_charThree`, `Formal.ringKrullDim_Ahat_le_charZero`, `Formal.ringKrullDim_mvPowerSeries`, `Formal.branchQuotEquiv`, `Formal.branchPrime_minimal_charThree`, `Formal.branchPrime_minimal_charZero`, `Formal.branchPrime_ne`, `Formal.intersectionEquiv`, `Formal.ringKrullDim_intersection` | Kernel-verified. `Â = k⟦z⟧ ⧸ (Brent equations centered at the point)` is taken directly, avoiding the general theory of `AdicCompletion`. The two exact families are built over `k⟦t⟧` with unit parameters `1 + Σ tᵢEᵢ`. Extending the 251 frame vectors to a basis gives the coordinate change `H(c,x,y,n) = L(c,x) + R(c,y) − R(c,0) + N(n) − p` with linear part that basis. The formal inverse function theorem, proved by degree recursion, makes substitution along `H` an automorphism. In the new coordinates every Brent equation lies in `(y,n) ∩ (x,n)`: restricted to `(c,x)` it is `L − p`, and restricted to `(c,y)` it is `R − p` by the overlap `L(c,0) = R(c,0)`. The map `A → Â` sends `𝔪_A` onto `𝔪_Â`, so the degree-55 certificates transport and give `dim Â ≤ 197`. With `dim k⟦σ⟧ = |σ|`, this gives minimality of both branch primes. |
| §6, completion `SquareCompletion ≃ Â` | `Formal.mem_pow_iff_lowZero`, `Formal.exists_limit`, `Formal.truncEquiv`, `Formal.completionEquiv`, `Formal.sqEquiv`, `Formal.sqBranchQuotEquiv`, `Formal.sqBranchPrime_minimal_charThree`, `Formal.sqBranchPrime_minimal_charZero`, `Formal.sqBranchPrime_ne`, `Formal.sqIntersectionEquiv`, `Formal.ringKrullDim_sqIntersection` | Kernel-verified. In `k⟦z⟧`, `(z)ⁿ` is the ideal of series with no terms below degree `n`, so `(z)`-adic Cauchy sequences converge coefficientwise and `Â` is `𝔪̂`-adically complete. The map `ψ : A → Â` induces `A ⧸ 𝔪ⁿ ≃ Â ⧸ 𝔪̂ⁿ`. Surjectivity: a series agrees with a polynomial modulo degree `n`. Injectivity: if `ψ(p) ∈ 𝔪̂ⁿ`, the coefficients of `ψ(p)` in the Brent equations can be truncated to polynomials, and what remains of `p` lies in `(z − p)ⁿ`. The universal properties of `AdicCompletion` and of complete rings then give `SquareCompletion ≃+* Â`, which carries the F6 and F7 statements over. Lean's default instance search equips `SquareCompletion` with the `OreLocalization` module structure, which hides its ring structure. The ring structure is taken from the definitionally equal completion with the standard module structure (`Formal.squareCompletion_eq`, proved by `rfl`). |
| §6, reduced variety singular | `Formal.le_spanFinrank_maximalIdeal_Ared`, `Formal.not_isRegularLocalRing_Ared_charThree`, `Formal.not_isRegularLocalRing_Ared_charZero` | Kernel-verified. Any generating set of `𝔪` of `A_red` spans `𝔪/𝔪²`, so it has at least 251 elements. Since `dim A_red = dim A ≤ 197`, Mathlib's `IsRegularLocalRing` (minimal number of generators of `𝔪` equals Krull dimension) fails. |
| §6, `H(2)` versus the two-branch value `28710` | `Formal.hilbertValue_eq_of_algHom`, `Formal.hilbertValue_two_Ahat`, `Formal.sqAlgEquiv`, `Formal.hilbertValue_two_squareCompletion`, `Formal.card_QIdx`, `Formal.hilbertValue_two_twoBranch`, `Formal.unionIdeal_ne_bot`, `Formal.sqBranchPrime_inf_ne_bot`, `Formal.not_isReduced_or_extra_minimalPrime` | Kernel-verified. `H(d)` only depends on `R ⧸ 𝔪^(d+1)`, so `A ⧸ 𝔪ⁿ ≃ Â ⧸ 𝔪̂ⁿ` and the `k`-algebra isomorphism `SquareCompletion ≃ Â` carry `H(2) = 30978` over. On `Â ⧸ (𝔭_L ⊓ 𝔭_R)`, in the F5 coordinates `(c, x, y, n)`, every `n` and every product `x_i y_j` vanishes, so the 28,710 products `w_i w_j` with `i ≤ j` and `(i, j)` not mixed span `𝔪²/𝔪³`. They are independent: their coefficients in the F5 coordinates are well defined, because a non-mixed monomial lies on one of the two branches. The paper's two-branch quotient `k⟦c,x,y⟧ ⧸ (x_i y_j)` is taken here as `Â ⧸ (𝔭_L ⊓ 𝔭_R)` itself, which is the ring the comparison needs. If `𝔭_L ⊓ 𝔭_R = 0`, then `Â` would equal this quotient and `30978 = 28710`. Finally, in a reduced Noetherian ring `0` is the intersection of the minimal primes, which gives the dichotomy. |
| §6, reduced tangent dimension 251 | `Formal.hilbertValue_reduced_one` | Kernel-verified over every field. The 251 tangent coordinates bound `dim 𝔪/𝔪²` of `A_red` above. The two branch maps `A → k⟦c,x⟧`, `A → k⟦c,y⟧` land in domains, so they kill the nilradical. Their linear coefficients along the 197 + 197 chart variables take the translated coordinates to the 251 independent frame vectors. |

## Remaining proof graph

None. Every row above is kernel-verified.

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
- [x] F5. `Â := k⟦z⟧ ⧸ (Brent equations)`. Extend the 251 certified frame vectors to a basis
  (`Basis.sumExtend`, no new certificate). Then
  `H(c,x,y,n) = L(c,x) + (R(c,y) − R(c,0)) + N(n) − p` has invertible linear part, and
  the Brent ideal composed with `H` lies in `(y,n) ∩ (x,n)`
  (`CoordinateChange.H_bijective`, `CoordinateChange.map_brentPS_le`).
- [x] F6. `Â` is local and Noetherian, and `dim Â ≤ 197` via the degree-55 certificate,
  Nakayama, and Krull's height theorem. The map `A → Â` (`z ↦ p + z`) sends `𝔪_A` onto `𝔪_Â`,
  so the existing relations transport (`FormalDimension.ringKrullDim_Ahat_le_charThree`,
  `FormalDimension.ringKrullDim_Ahat_le_charZero`).
- [x] F7. Branches: `𝔭_L`, `𝔭_R` are prime and minimal, with `Â⧸𝔭_L ≃ k⟦c,x⟧` and
  `Â⧸𝔭_R ≃ k⟦c,y⟧`. They are distinct, and `Â⧸(𝔭_L+𝔭_R) ≃ k⟦c⟧` has dimension 143, in
  characteristic three and zero (`Branches.branchQuotEquiv`, `Branches.branchPrime_minimal_charThree`,
  `Branches.branchPrime_minimal_charZero`, `Branches.branchPrime_ne`, `Branches.intersectionEquiv`,
  `Branches.ringKrullDim_intersection`; `dim k⟦σ⟧ = |σ|` is `PowerSeriesDimension.ringKrullDim_mvPowerSeries`).
- [x] F8. The reduced local ring has tangent dimension 251 (`ReducedTangent.hilbertValue_reduced_one`).
- [x] F9. Audit, README, CI and STATUS updated, and the full `leanchecker` replay passes.
  No open rows remain.
- [x] F10. `SquareCompletion ≃+* Â` (`Completion.sqEquiv`, via `PowerSeriesAdic`), with the
  F6 and F7 statements transported to `SquareCompletion`.
- [x] F11. The reduced local ring is not regular in characteristic three and zero
  (`Singular.not_isRegularLocalRing_Ared_charThree`, `Singular.not_isRegularLocalRing_Ared_charZero`).
- [x] F12. `H(2) = 30978` transported to `Â` and `SquareCompletion`; the reduced union of the
  branches has `H(2) = 28710`; hence `𝔭_L ⊓ 𝔭_R ≠ 0` and `SquareCompletion` is nonreduced or has
  an additional minimal prime (`TwoBranch.not_isReduced_or_extra_minimalPrime_charThree`,
  `TwoBranch.not_isReduced_or_extra_minimalPrime_charZero`).

The published `bash verify.sh --full` replay passed independently of Lean
at the pinned source revision. The Jacobian's 2,352 transposed columns admit
a sparse integer elimination with 2,101 unit pivots and 15,124 row
additions in that order. The kernel proves the implication from a checked trace to the rank theorem.
The row identities, pivot checks, and coverage are replayed in separate
kernel batches. The rank and nullity audit permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.
