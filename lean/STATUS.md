# Proof status

Proved in Lean:

- over every field `k : Type`, `197 ≤ squareLocalDimension k ≤ 251`;
- over every field of characteristic three,
  `squareLocalDimension k = 197` (`squareLocalDimension_eq_197_of_charThree`);
- over every field of characteristic zero,
  `squareLocalDimension k = 197` (`squareLocalDimension_eq_197_of_charZero`);
- over every field of characteristic three or zero, the §7 points `q_L`, `q_R` (blocks 4 and 5
  at `t = 1`) are smooth: Jacobian rank 2155, tangent and local dimension 197, regular local ring,
  `Â_q ≃ k⟦z₁,…,z₁₉₇⟧` (`Formal.SmoothPoints.smooth_points`);
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
- over every field, the 146-parameter centered group orbit map `Φ_orb` (the isotropy `GL₄³`
  and the 98 compensated term rescalings) has comorphism `Â → k⟦146⟧` factoring through `A`
  (`Formal.orbitHat`, `Formal.orbitA`, `Formal.orbPull_eqPS`). Its differential at `0` has rank
  exactly 143 and kernel exactly the central scalings `K₃` (`Formal.finrank_range_dOrbit`,
  `Formal.finrank_ker_dOrbit`). The gauge-fixed orbit map `Â → k⟦c⟧`, with `c` the 143 kept
  coordinates, is surjective (`Formal.sliceHat_surjective`). It is the restriction of `Φ_orb^*`
  to the gauge slice (`Formal.sliceHat_eq`).
- in characteristic three and zero, each branch is independent of the slice used to detect it.
  The comorphism `Â → k⟦230⟧` of the full parameter map of either family (all global, block and
  scaling parameters) has kernel exactly `𝔭_L`, resp. `𝔭_R`. Any restriction of it with minimal
  prime kernel gives the same prime (`Formal.ker_fullHat_charThree`, `Formal.ker_fullHat_charZero`,
  `Formal.slice_independent`). Over every field, the intersection `Â ⧸ (𝔭_L + 𝔭_R)` is the formal
  orbit subgerm of the group slice: the kernel of the gauge-fixed group orbit comorphism is
  `𝔭_L + 𝔭_R` (`Formal.ker_sliceHat`, `Formal.orbitSubgermEquiv`).
- over every commutative ring, the swap `K` (exchange of the two tensor factors of `k² ⊗ k²` in all
  three slots, composed with the term permutation `(i, j) ↦ (j, i)`) preserves solutions, fixes
  `p`, and sends the left family at any group element `g` to the right family at `KgK`
  (`Formal.swapDec_solves`, `Formal.swapDec_strassenSquare`, `Formal.swapDec_value`). It induces
  an involutive automorphism of `Â`. In characteristic three and zero this automorphism exchanges
  `𝔭_L` and `𝔭_R` and fixes `𝔭_L + 𝔭_R` (`Formal.swapHatEquiv`,
  `Formal.comap_swapHat_right_charThree`, `Formal.comap_swapHat_right_charZero`,
  `Formal.comap_swapHat_sup`).

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
| §3, orbit dimension 143 (lines 326–332) | `Formal.orbitHat`, `Formal.orbitA`, `Formal.orbPull_eqPS`, `Formal.coeff_orbitPull_X`, `Formal.dOrbit_kerVec`, `Formal.kerVec_independent`, `Formal.minor_upper`, `Formal.minor_diag`, `Formal.det_minor_ne_zero`, `Formal.finrank_range_dOrbit`, `Formal.finrank_ker_dOrbit`, `Formal.slicePull_eq`, `Formal.sliceHat_eq`, `Formal.sliceHat_surjective`, `Formal.ringKrullDim_slice` | Kernel-verified over every field. Parameters: 48 matrix units of the three global `GL₄` factors and, for each of the 49 terms, the rescalings `(λ, μ) = (1 + t₀ + t₁, 1 − t₁)`. Because the orbit consists of solutions, pullback kills the centered Brent ideal, so the comorphism factors through `Â` and `A`. Its linear part is the `jacRow` matrix, identified via first-order jets with the `globalUnit` and `termUnit` tangents. The three central scalings `K₃` lie in the kernel, so the rank is at most 143. Setting `(g, (1,1), (1,1))` to zero leaves 143 rows. A pivot search found 143 Brent coordinates for which the minor is upper triangular with diagonal `±1`. The kernel checks this over `ℤ` (`decide +kernel`), so the minor is invertible in every characteristic, including 3 and 0. Hence the rank is exactly 143 and the kernel is exactly `K₃`. The F2 formal inverse function theorem (`subst_bijective_equiv`) on the minor makes the gauge-fixed comorphism `Â → k⟦c⟧` surjective. |
| §6, slice independence and the orbit subgerm (lines 543–565) | `Formal.killCompl_subst`, `Formal.fullHat`, `Formal.branchMap_eq`, `Formal.ker_fullHat_charThree`, `Formal.ker_fullHat_charZero`, `Formal.slice_independent`, `Formal.orbitMap_eq`, `Formal.gauge_origin`, `Formal.orbitMap_eq_slice`, `Formal.eq_ker_of_le`, `Formal.ker_sliceHat`, `Formal.orbitSubgermEquiv` | Kernel-verified. Restriction to coordinate subspaces (`killCompl`) commutes with substitution, because both are continuous algebra maps (`comp_aeval`). So the branch map `kill ∘ Φ` is the comorphism of the chosen 197-parameter chart family. That family is the full parameter family (`1 + t` on every global, block and scaling factor) substituted along the linear map `specF`. Therefore `ker(full) ⊆ 𝔭_L`; it is prime because `k⟦230⟧` is a domain, and minimality of `𝔭_L` forces equality. The same steps show the frame orbit map is the group orbit comorphism substituted along `specO`. That map factors through the gauge slice because no orbit frame direction moves the gauge entry `(1,1),(1,1)` (checked by `decide +kernel`). Hence `ker(slice) ⊆ 𝔭_L + 𝔭_R`. Both quotients are `k⟦143⟧`, so a 143-chain argument gives equality. |
| §7, swap symmetry of the orientations (lines 643–651) | `Formal.swapDec_solves`, `Formal.swapDec_leftFamily`, `Formal.swapDec_strassenSquare`, `Formal.swapDec_changeBasis`, `Formal.swapDec_value`, `Formal.swapPS_eqPS`, `Formal.swapHatEquiv`, `Formal.fullHat_swapHat`, `Formal.comap_swapHat_right`, `Formal.comap_swapHat_sup` | Kernel-verified. `swapDec` relabels the vertex index by `K` and the terms by `(i,j) ↦ (j,i)`. It permutes the Brent equations, because `K` is a permutation of the matrix index that preserves the matrix multiplication tensor. `outer ∘ K = inner`, so `swapDec(leftFamily P Q T) = rightFamily P Q T` for the same blocks. `swapDec` commutes with changes of basis (conjugated by `K`) and with rescalings (terms permuted). On `k⟦z⟧` it is the variable permutation `piV`, which maps each centered equation to another centered equation, so it descends to an involution of `Â`. The full family maps satisfy `full_R ∘ swap = ρ ∘ full_L`, where `ρ` is the corresponding permutation of the parameters. With slice independence, `swap⁻¹(𝔭_R) = 𝔭_L`. |
| §7, one-parameter curves to smooth points (lines 621–633) | `Formal.e12`, `Formal.e21`, `Formal.det_e12`, `Formal.det_e21`, `Formal.e12_mul_neg`, `Formal.e21_mul_neg`, `Formal.curve`, `Formal.curve_value_zero`, `Formal.curve_one`, `Formal.pqInt`, `Formal.pqInt_value_left` | Kernel-verified over every commutative ring. `curve t` has the identity global action and scalings, `(P, R) = (I+tE₁₂, I+tE₂₁)` in block 4, `(I+tE₂₁, I+tE₁₂)` in block 5 and the identity elsewhere (Q = I). The four matrices have determinant one and inverse at `−t`. At `t = 0` both orientations give `p`; at `t = 1` the curve is `pqInt`, whose left value is the stored point `SmoothL.pointDec` (checked entrywise by `decide +kernel`). |
| §7, smooth points `q_L`, `q_R` (lines 633–642) | `Formal.SmoothPoints.smooth_points`, `SmoothPoints.integer_solves`, `SmoothPoints.qL_jacobian_rank`, `SmoothPoints.qR_jacobian_rank`, `SmoothPoints.qL_tangent_dimension`, `SmoothPoints.qR_tangent_dimension`, `SmoothPoints.qL_local_dimension`, `SmoothPoints.qR_local_dimension`, `SmoothPoints.qL_regular`, `SmoothPoints.qR_regular`, `SmoothPoints.qL_formal`, `SmoothPoints.qR_formal` | Kernel-verified over every field of characteristic three or zero. (a) The integer Brent identity holds at `t = 1` in both orientations. (b) Jacobian rank exactly 2155: the radix trace `SmoothL.checked` (six kernel blocks) gives rank 2155 modulo three of the selected rows. In characteristic three these rows are a 2155 × 2155 integer minor of the Jacobian, so its determinant is nonzero modulo three, hence over ℤ, hence in characteristic zero (`SmoothL.det_minor_ne_zero`). This gives rank ≥ 2155. 197 group directions lie in the kernel of the Jacobian (`tangent_satisfies_differential` on dual-number jets). Their minor on the 197 non-pivot variables is lower triangular with diagonal ±1 (`SmoothLeftMinor.minor_lower`, `minor_diag`), so they are independent and the rank is ≤ 2155. (c) The tangent space (`ker dF_q`) has dimension 197. (d) The local ring has dimension 197: `≤` by `pointLocalDimension_le`, and `≥` by an exact 197-parameter family over the germ `k[t]_(t)` (`GermLower.le_pointLocalDimension`, `le_localDimension_of_tangents`). (e) Smoothness: the maximal ideal is generated by `2352 − 2155 = 197` elements (`spanFinrank_maximalIdeal_le`, Nakayama), which equals the dimension, so the local ring is regular (`IsRegularLocalRing`). Moreover `Â_q ≃ₐ k⟦z₁,…,z₁₉₇⟧`: the formal inverse function theorem on the 2155-minor makes `k⟦free⟧ → Â_q` surjective (`freeMap_surjective`), the family comorphism restricted to the 197 parameters is surjective by the triangular minor and `subst_bijective_equiv`, and a surjective endomorphism of a Noetherian ring is injective (`freeMap_bijective`). `q_R = swap(q_L)` (`swapDec_value_trivial`); the swap permutes variables and equations, which carries rank, kernel, the germ family and `Â` across (`SmoothRightPoint`). The paper states rank 2155 modulo 3 and deduces the characteristic-zero bound; the Lean statement proves the rank exactly in both characteristics. |
| §7, Li–Wang–Hu comparison point (lines 652–656) | `LWH.solves`, `LWH.jacobian_rank`, `LWH.tangent_dimension`, `LWH.orbit_in_tangent`, `LWH.orbit_tangent_dimension`, `LWH.lwh_point` | Partial Lean build. The point is the AlphaTensor decomposition of Li–Wang–Hu §5.2.2 (`s526.ipynb` in their repository; DeepMind catalogue entry 1403), stored in the direct convention (`w = Wᵀ`); their §5.3 point is a different, singular one (nullity 198). (a) The 4096 integer identities are checked by the kernel in 16 batches (`LWHSolves`). (b) Rank ≥ 2155: a mod-3 radix trace for a 2155 × 2155 minor with 16-bit digits (`LWHBlocks`), transferred to characteristic zero as at `q_L`. Rank ≤ 2155: the unit solutions on the 197 free variables are integral, so 197 integer kernel vectors have the identity as free-variable minor; `J v = 0` is replayed over ℤ in 25 kernel batches (`LWHKernelChecks`). (c) Each of the 146 generators is the tangent of an exact dual-number change of basis or rescaling of the point (`tangent_satisfies_differential`). A 143 × 143 generator minor is upper triangular with diagonal ±1, and the identity units `(g, 0, 0)` are integer combinations of kept generators (the central scalings), so the span has dimension 143 over every field. Data: `tools/lwh_certificate.py`, `tools/generate_lwh.py`. |
| §7, dimension of the family closures: equidimensionality input (lines 610–617) | `Equidim.height_eq_ringKrullDim_of_isMaximal`, `Equidim.ringKrullDim_localization_eq`, `Equidim.ringKrullDim_ne_top`, `Equidim.eq_zero_of_eval_eq_zero_of_eval_ne_zero` | Kernel-verified (any field; the `[IsAlgClosed k]` versions are the stated corollaries). In a domain of finite type over a field every maximal ideal has height `dim B`, via Noether normalization, going-down and incomparability. This is the step from local dimension 197 at `p` to dimension 197 of each closure; the component statement itself is item F17 (in progress). |
| §7, family closures are components of dimension 197 (lines 608–619) | `Section7.closure_dimension`, `Section7.closure_component`, `Section7.closure_minimalPrime`, `Section7.closure_dimension_algClosed`, `Section7.closure_component_algClosed`; `Formal.Component.ringKrullDim_closure`, `familyClosure_isComponent`, `ker_mem_minimalPrimes` | Drafted, pending validation. Every infinite field of characteristic three or zero; the paper works over an algebraically closed field ("after passing to the algebraic closure"), which is the stated corollary. `familyClosure k left` is the Zariski closure in `k^2352` of the family image; its vanishing ideal is `ker ψ` (`vanishing_eq_ker`, needs `Infinite k`). Dimension: `dim k[x]/ker ψ` equals the local dimension at `p` (equidimensionality), which is `≤ 197` because the local ring is a quotient of the Brent local ring, and `≥ 197` by the 197-parameter germ family. Component: any prime between the Brent ideal and `ker ψ` equals `ker ψ` (`prime_eq_ker`, a strictly smaller prime would raise the dimension at `p` above 197), so no irreducible closed subset of `V` strictly contains the closure. |
| §7, rank bounds on the closures (lines 659–674) | `Section7.rank_bounds_closed`, `Census.closure_saturation_subset_rankBound`, `Census.closure_budgetOK` | Drafted (`RankBound` part compiled earlier, pending re-validation). `RankBound k` is the zero locus of the products of 14 `2 × 2` minors of distinct summands and of two `3 × 3` minors of distinct summands, so it encodes exactly "at most 13 summands have a mode of rank above one, at most one above two". It contains the closure of the saturated families (closed under every equivalence, `dominated_of_formula`). On each family closure the rank of mode `m` of summand `(i, j)` is at most `cᵢ cⱼ` (`BudgetOK`). The paper's exact family multiset `36(1,1,1) + 12(2,2,2) + 1(4,4,4)` (line 662) is used only through these upper bounds; equality on the family is not formalized (see the audit table). |
| §7, anchor structure and its persistence (lines 676–694) | `Section7.anchor_structure_closed`, `Census.family_stackOK`, `Census.closure_stackOK`, `Census.Minors.rank_le_iff_minors`, `Census.rank_eq_budget`, `Census.anchorTest_of_mem` | Drafted, pending validation. On the family image the child `(i, j)` and its anchor `(i, 0)` (left; `(0, j)` right) satisfy `M_child = Z M_anchor = M_anchor Z'`, because Strassen's summand `0` is the identity; changes of basis and rescalings preserve this. Hence the stacked matrices have rank `≤ 2` (closed, via `rank ≤ r ⇔` all `(r+1)`-minors vanish) on the closure. At a full-profile closure point both rank sums are 192, so each rank equals its budget, each anchor has rank two, and the stacking conditions give the span containments: the anchor test holds. |
| §7, census over every field (lines 696–705) | `Section7.census`, `Catalogue.AllFields.card_fullProfile`, `fullProfile_iff_rankBounds`, `card_not_rankBounds`, `anchor_excluded`, `card_pass_both`; `Catalogue.Q.*`, `Catalogue.F3.*` | Drafted on the helper's Task B (kernel census of all 14,236 points over `ℚ` and `ZMod 3`, in 112 chunks; pending the full run). Every field of characteristic three or zero: span containment is a rank equality of stacked integer matrices (`rowSpace_le_iff_rank`), and the rank of an integer matrix is the same over `K` as over `ℚ` or `ZMod 3` (`FieldTransfer.rank_map_algebraMap`, base change and flatness). Data: DeepMind `alphatensor_14236_factorizations.npz` at revision `1949163d…c767`, SHA-256 `15d27e30…ed06a3`; generated Lean files pinned by `Brent/Catalogue/GENERATED_SHA256.txt`. |
| §7, the exclusions as geometry (lines 659–660, 698–704) | `Section7.rank_bound_exclusion`, `Section7.anchor_exclusion`, `Section7.excluded_count`; `Census.catPoint`, `Census.rank_modeMat_catPoint`, `Census.catPoint_not_mem_saturated`, `Census.catalogue_excluded`, `Census.anchor_excluded_eqClosed`, `Census.card_excluded` | Drafted, pending validation. `catPoint k p` is catalogue entry `p` in `k^2352` (summand `(i, j)` = row `7i + j`, vertex `(a, b)` = index `2a + b`, `w = Wᵀ`); its mode-matrix ranks are the catalogue ranks. The 87 entries failing the rank bounds are outside `RankBound k` (nonzero minor products), hence outside the closure of the saturated families. 2445 and 5969 are outside both family closures and outside the closure of `eqClosed k`, all points equivalent to a family point under summand and mode relabelling, transposition, mode-wise invertible `L M R` and nonzero rescalings (`Equivalent`, which contains `changeBasis` and `rescale`). In total 89 entries. |
| §7, one theorem per claim (whole section) | `Brent.Section7` | Drafted. Each theorem quotes its lines; `Audit.lean` (single file) lists them with `Theorem11.main_theorem`. |
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
- [x] F13. The 146-parameter group orbit has dimension 143: `rank dΦ_orb(0) = 143` with kernel
  `K₃`, and the gauge-fixed orbit comorphism `Â → k⟦c⟧` is surjective
  (`OrbitDimension.finrank_range_dOrbit`, `OrbitDimension.sliceHat_surjective`).
- [x] F14. Slice independence: the full parameter map of each family has kernel `𝔭_L`, resp.
  `𝔭_R`. The intersection `Â ⧸ (𝔭_L + 𝔭_R)` is the group orbit subgerm
  (`SliceIndependence.ker_fullHat_charThree`, `SliceIndependence.ker_sliceHat`).
- [x] F15. The swap symmetry exchanges the two families and, on `Â`, the two branch primes
  (`SwapSymmetry.swapDec_value`, `SwapSymmetry.comap_swapHat_right_charThree`).
- [x] F16. §7 smooth points: the curves through `p` and `q_L`, `q_R`; at both points, in
  characteristic three and zero, Jacobian rank 2155, tangent dimension 197, local dimension 197,
  regular local ring, and `Â_q ≃ k⟦197⟧` (`SmoothPoints.smooth_points`). Equidimensionality of
  finitely generated domains (`Equidim.height_eq_ringKrullDim_of_isMaximal`) is in place for F17.
  The local `leanchecker` replay passed for all eight certificate modules: `SmoothLData`,
  `SmoothBlocks.L0` through `L5`, and `SmoothLChecks` (5,060 seconds total).
- [~] F17. §7 components: each family closure is irreducible of dimension 197, contains `p`, and
  is an irreducible component of `V(4,4,4|49)` over algebraically closed `k`.
- [~] F18. §7 rank-profile exclusions and the AlphaTensor catalogue census (14,149 / 87 / 2 / 89).
- [~] F19. §7 Li–Wang–Hu comparison (tangent 197, orbit tangent 143).
  The integer Brent identity (`LWHSolves`), the supporting `LWH.Trace` and `LWH.Kernel`
  modules, and rank certificate blocks `L0` and `L1` have compiled. Independent arithmetic
  checks passed for all 2,155 trace identities, all 197 integer kernel vectors, and the
  orbit tangent rank of 143. The remaining rank blocks, `LWHKernelChecks`, and `LWH.Orbit`
  are pending, followed by the full `Brent.LWH` build, axiom audit, and kernel replay.
- [~] F20. `main_theorem` bundling Theorem 1.1, and the final line-by-line faithfulness audit.

The published `bash verify.sh --full` replay passed independently of Lean
at the pinned source revision. The Jacobian's 2,352 transposed columns admit
a sparse integer elimination with 2,101 unit pivots and 15,124 row
additions in that order. The kernel proves the implication from a checked trace to the rank theorem.
The row identities, pivot checks, and coverage are replayed in separate
kernel batches. The rank and nullity audit permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

## Additional paper-coverage drafts (not compiled)

- [~] Arbitrary left-kernel lifting: `Brent.LeftKernelLift.actual_leftKernel_lift_mod3`; uses unit pivots of the integer Jacobian trace. Idempotent projection, linear retraction and explicit free-coordinate basis drafted.
- [~] Exact anchors 2445 and 5969: `Brent.Catalogue.ExactAnchors`; checks both positive and negative finite certificates over the reference fields and transfers to other fields. Generated catalogue data are needed to evaluate these checks.
- [~] Lemma 4.1 degreewise graded presentation: `Brent.CM.GradedPresentation`; homogeneous product compatibility drafted; full direct-sum graded-ring equivalence still open.
- [~] Appendix A.2 explicit support, coefficient and leading monomial checks: `Brent.PaperDetails`.
- [~] Modular determinant vanishing equivalence given a strict determinant bound: `Brent.PaperDetails.minor_vanishing_iff_mod_prime`.

All new major declarations are included in `Audit.lean`. Existing compiled/drafted statuses are retained; these new proofs have not been compiled or kernel replayed. Remaining semantic gaps are enumerated in `AUDIT_TABLE.md` (geometric orbit dimension, original quadratic ideal height, graded ring assembly, left-kernel freeness, normal elimination base change, Hadamard bound and catalogue provenance).

### Additional source drafts on top of revision 775319f

- [~] Original quadratic ideal height: `Brent.CM.QuadraticHeight`.
- [~] Left kernel: `leftKernel_linear_retraction`, `leftKernelFreeEquiv`, `leftKernelBasis`.
- [~] Homogeneous product compatibility: `Brent.CM.GradedPresentation`.
- [~] Centered substitution and inverse tuple base change: `Brent.Formal.BaseChange`.
- [~] Prime 65521 and sufficient determinant bound: `Brent.PaperDetails` (Leibniz, not the general Hadamard inequality).
- [~] Independent external source binding verifier in CI; tested on synthetic data only.

### Third coverage extension (not compiled)

- [~] Actual normal elimination over R0 and naturality of every residual equation: `Brent.Formal.NormalEliminationZ3.normal_elimination_exists`. The explicit bridge to the paper's frozen tangent frame and its quadratic initial forms is not complete.
- [~] Exact squared Hadamard inequality for every relevant minor order (≤4): `Brent.PaperDetails.HadamardSmall.squared_hadamard`, `censusMinor_vanishing_iff_hadamard`. Independent finite arithmetic enumeration passed; not a kernel replay.
- [~] Full direct-sum graded ring assembly: `Brent.CM.GradedRingAssembly.lemma41_ringEquiv`, `lemma41_ringEquiv_of`. The separate bundled identification of its source as the polynomial quotient by the ideal of initial forms remains open.

Still open: geometric orbit closure dimension, polynomial quotient identification, tangent-frame comparison noted above, and kernel-level catalogue provenance. Original NPZ and generated catalogue absent from the input. No compilation or kernel replay claimed for these new declarations.
