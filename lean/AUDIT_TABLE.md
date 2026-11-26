# Faithfulness audit: `paper.tex` claim by claim

Status values: **compiled** (built, audited, replayed), **drafted** (on `compilation-pending`, not
yet validated), **open** (not formalized; reason given).

## §7 Relation to the AlphaTensor schemes (lines 606–705)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 610–613 | The closure of either family image has dimension 197 | `Section7.closure_dimension`, `closure_dimension_algClosed` | drafted | Proved for every infinite field of characteristic 3 or 0; the algebraically closed statement is a corollary. Dimension is `ringKrullDim (k[x] ⧸ 𝔮)` with `𝔮` the vanishing ideal of the closure (`vanishing_eq_ker`). |
| 612–613 | The irreducible parameter space has irreducible image closure | `FamilyClosure.isIrreducible_familyClosure` | drafted | Over every infinite field. |
| 614–616 | The closure contains `p`; local dimension equals dimension; Theorem 1.1 bounds it | `FamilyClosure.pointP_mem`, `Equidim.ringKrullDim_localization_eq'`, `Component.localDim_closure` | drafted | — |
| 616–619 | Any component strictly containing it passes through `p` with larger dimension; each closure is a component | `Section7.closure_component`, `closure_component_algClosed`, `closure_minimalPrime` | drafted | Component = maximal irreducible closed subset of `V(k)` with the Zariski topology; also as a minimal prime of the Brent ideal. |
| 621–631 | The curves: identity global action, blocks 4 and 5 changed; determinant one; inverses at `−t` | `Section7.curve_matrices`, `Formal.curve` | compiled | — |
| 631–633 | At `t = 0` the curves pass through `p`; at `t = 1` the integer Brent identity holds | `SmoothPoints.smooth_points` (clauses 1–3) | compiled | — |
| 633–642 | Jacobian rank 2155 mod 3; tangent bound 197; local and tangent lower bounds; smoothness | `Section7.smooth_points` | compiled | Rank proved exactly in characteristic 3 and 0; smoothness as a regular local ring and `Â ≃ k⟦197⟧`. |
| 643–651 | The swap fixes `p` and exchanges the families | `Section7.swap_symmetry`, F15 rows | compiled | — |
| 652–653 | Li–Wang–Hu point: tangent 197, orbit tangent 143 | `Section7.lwh_point` | drafted (partially compiled) | Point identified as catalogue entry 1403 (`w = Wᵀ`). |
| 654–658 | "Equality of a dimension alone gives no criterion for membership" | — | not a claim | Expository. |
| 661–663 | Throughout either family the rank-triple multiset is `36(1,1,1) + 12(2,2,2) + 1(4,4,4)` | `Section7.family_rank_profile`, `Census.rank_value_eq`, `Census.rank_kron_eq` | drafted | Every field, at every family point. Exact ranks hold on the family image only; on the closures only the closed upper bounds are used, and equality is derived at full-profile points from the rank sums (both 192). |
| 663–667 | Base ranks; tensor products multiply ranks; changes are multiplications by invertible matrices | `RankBound.rank_kron_le`, `modeMat_changeBasis` | drafted | Upper bound `rank (A ⊗ B) ≤ rank A · rank B` via factorizations. |
| 667–668 | In the closures, ranks can only decrease at each labeled summand | `Census.closure_budgetOK` | drafted | — |
| 668–671 | Even allowing permutations: at most 13 summands with a mode rank above one, at most one above two | `Section7.rank_bounds_closed` | drafted | On the closure of the saturated families (`Dominated`: every equivalence acts by `L M R` or `L Mᵀ R`). |
| 676–681 | Unique rank-two term per group; its row and column spaces contain those of the other six | `Census.base_rel_left`, `base_rel_right`, `family_rel`, `unique_rankTwo_left`, `unique_rankTwo_right` | drafted | Stated as `M_child = Z M_anchor = M_anchor Z'`, equivalent to the containments (`rowSpan_le_of_stack`). Uniqueness now has separate drafted statements in FamilyProfile.lean. |
| 681–682 | Left and right changes preserve the inclusions | `Census.rowRel_changeBasis`, `colRel_changeBasis`, `Equivalences.shape_of_equivalent` | drafted | — |
| 682–688 | Persistence at closure points with the same profile; equal rank sums force equality per label; anchors keep rank two | `Census.closure_stackOK`, `Census.rank_eq_budget`, `Census.anchorTest_of_mem`, `Census.anchorTest_of_shape` | drafted | Sums are both 192. |
| 688–689 | The other orientation gives the same condition with roles exchanged | `anchor false`, `base_rel_right` | drafted | — |
| 689–694 | The filter: six rank-two terms each accommodating six rank-one terms, every rank-one term with a candidate anchor | `Catalogue.AnchorTest` | drafted | Matches `alphatensor_rank_profiles.py` (`Useful`: rank two with at least six children). |
| 696–698 | Over ℚ and 𝔽₃ exactly 14,149 points have the full profile | `Section7.census` (1), `Catalogue.Q/F3.card_fullProfile` | drafted | Every field of characteristic 3 or 0. |
| 698–699 | These are precisely the points satisfying the rank bounds, which exclude 87 entries | `Section7.census` (2, 3), `Section7.rank_bound_exclusion` | drafted | Excluded from the closure of the saturated families. |
| 700–703 | The space test excludes 2445 and 5969 (two and one useful anchors) | `Section7.census` (4), `Section7.anchor_exclusion` | drafted | Excluded from the closure of the families closed under all equivalences (`eqClosed`). Exact counts now have draft certificate proofs `Catalogue.usefulAnchors_count_2445`, `usefulAnchors_count_5969`; the generated catalogue must be present to check them. |
| 703–704 | A decomposition in the closure with this profile requires at least six | `Census.anchorTest_of_shape` | drafted | — |
| 704–705 | All 14,147 points passing both tests have the full profile | `Section7.census` (5) | drafted | — |
| 705–707 | Their membership remains open; other components through `p` possible | — | not a claim | Statement of an open problem. |

## Abstract and §1 Introduction (lines 1–95)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| abstract | Local dimension 197 over `F̄₃` and in characteristic 0; tangent dimension 251 | `main_theorem` | compiled | Every field of characteristic 3 or 0, not only `F̄₃`. |
| abstract | Two smooth formal branches of dimension 197 with intersection dimension 143; Hilbert function `(1, 251, 30978)` | `main_theorem` | compiled | — |
| abstract | Explicit deformations reach smooth points on both families | `Section7.smooth_points` | compiled | — |
| abstract | The catalogue comparison rules out membership for 89 of 14,236 schemes | `Section7.excluded_count`, `Section7.rank_bound_exclusion`, `Section7.anchor_exclusion` | drafted | — |
| 20–58 | Background, related work (Li–Bao–Zhang, Li–Zhang–Ke, Brysiewicz–Sinn) | — | not a claim | Citations of other papers' results. |
| 50–53 | Li–Wang–Hu's selected example: nullity 197, orbit tangent 143, 54 directions modulo the orbit | `Section7.lwh_point` | drafted | 197 − 143 = 54 is arithmetic. |
| 54–60 | At `p` the orbit has dimension 143 and the tangent quotient 108; each family gives 54 directions modulo the orbit and together they span the quotient | `Formal.finrank_range_dOrbit`, `archived_frame_split`, `square_jacobian_nullity` | compiled | 108 = 251 − 143. |

## §2 The Brent scheme and the recursive point (lines 96–175)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 100–110 | `M_n`, the Brent map with 2352 variables and 4096 equations | `matrixMultiplicationEntry`, `equation`, `square_variable_count`, `square_equation_count` | compiled | — |
| 111–115 | `V = Br_red`; local Krull dimensions agree because reduction preserves primes | `quotient_dimension_of_le_nilradical`, `reduced_localDimension_eq_197` | compiled | — |
| 118–140 | The integral point `p` (Strassen table, Kronecker shuffle) lies in `Br(ℤ)` | `strassen_solves`, `strassenSquare_solves` | compiled | Over every commutative ring. |
| 141–152 | Theorem 1.1: rank 2101, tangent 251, local dimension 197, orbit 143, two smooth branches of dimension 197 with intersection 143, Hilbert function `(1, 251, 30978)` | `main_theorem` | compiled | `k` any field of characteristic 3 or 0 (the paper: `F̄₃` or characteristic 0). "At least two distinct smooth branches" is stated as two distinct minimal primes `𝔭_L ≠ 𝔭_R` of `Â` with `Â ⧸ 𝔭 ≃ k⟦197⟧`. |

## §3 Two exact families and the tangent split (lines 176–390)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 178–196 | The `GL₄³` action and term scalings preserve solutions | `solves_changeBasis`, `solves_rescale` | compiled | — |
| 197–199 | Scalar `P, Q, R` are compensated by scalings: three-dimensional kernel in the 146-parameter group | `Formal.finrank_ker_dOrbit` | compiled | — |
| 200–226 | `D_L`, `D_R` are solutions over any ring; both send the identity to `p`; `g_i = 1` gives the same orbit map | `leftFamily_solves`, `rightFamily_solves`, `leftFamily_at_identity`, `rightFamily_at_identity`, F1 overlap (`value true = value false` at trivial blocks) | compiled | — |
| 228–252 | Lemma 3.1: the three copies of `𝔰𝔩₂` act injectively on Strassen's factor lines | `Section3.lemma_base` | drafted | Every field with `2 ≠ 0` (`Section3.two_ne_zero_of` for characteristic 3 or 0). |
| 253–288 | Projection to `Mat₂/kF`; the map from rescalings and the two block lists to the tangent space is injective | `Section3.kron_line`, `Section3.derivative_injective` | drafted | The derivative is written by the formula of lines 262–267 (`Section3.derivative`). |
| 289–320 | The 27 mixed global directions are independent modulo `S + L + R'` | `Section3.mixed_independent`, `Section3.KMat_line`, `Section3.mixed_count` | drafted | `H ⊗ H` is written as `∑ᵥ hᵥ ⊗ eᵥ` with trace-free `hᵥ`; the global derivative has the cyclic form of lines 236–240. |
| 321–328 | Dimension table: `T₀ = 143`, `T₀ + L = T₀ + R' = 197`, `T₀ + L + R' = 251` | `finrank_range_dOrbit`, `chart_independent_derivatives`, `archived_frame_split`, `square_jacobian_nullity` | compiled | The 197 is stated as 197 independent chart derivatives per family. |
| 329 | The two branch tangent spaces intersect precisely in `T₀` | `TangentData.branchTangent_inf`, `finrank_branchTangent`, `finrank_orbitTangent`, `branchTangent_ne` | drafted | Branch tangent space = span of that family's archived first derivatives (`branchTangent_generators`). |
| 330–337 | Orbit dimension 143: fibers contain the central kernel (≤ 143) and an invertible 143-minor gives 143 formal coordinates (≥ 143) | `Formal.finrank_range_dOrbit`, `Formal.ringKrullDim_slice` | partial | Formal slice and differential covered; algebraic orbit closure dimension is not yet a separate theorem. |
| 338–343 | Group and block directions lie in `ker J`; a nonzero 2101-minor mod 3 gives tangent ≤ 251 in both characteristics | `tangent_satisfies_differential`, `square_jacobian_rank`, `square_jacobian_nullity` | compiled | Rank proved exactly over every field. |
| 344–356 | `ker J = T₀ ⊕ X ⊕ Y` with dimensions `(143, 54, 54)` | `archived_frame_rank`, `archived_frame_split`, `archived_origin` | compiled | — |
| 357–378 | Lower bound `dim ≥ 197` via slices, formal inversion and completion | `LowerBound.le_squareLocalDimension` | compiled | Different proof: an exact family over `k[t]_(t)` and a system-of-parameters argument, without completion. Same statement. |
| 375–378 | The two surjections define embedded smooth formal subgerms with distinct tangent images | `Formal.branchQuotEquiv`, `Formal.branchPrime_ne` | compiled | — |

## §4 The quadratic certificate in characteristic three (lines 391–498)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 392–405 | Coefficients of `t`, `t²` are `Jv`, `Jh + Q₂(v)`; `v ∈ ker J` lifts to order two iff `Q₂(v) ∈ im J` | `Decomposition.second_order_expansion`, `Decomposition.liftsToOrderTwo_iff` | drafted | Every commutative ring; lifting is over `R[X]` modulo `X³`. |
| 405–413 | `λQ₂` vanishes on `T₀ + X` and `T₀ + Y`, leaving only the mixed monomials `xᵢyⱼ` | `archived_nonmixed_zero`, `archived_square_zero`, `same_family_polar_zero` | compiled | — |
| 414–426 | The 54 rows `λᵢ` kill `J` and `qᵢ = λᵢ M (x ⊗ y)` | `archived_covectors_annihilate`, `archived_mixed_coefficients` | compiled | — |
| 427–432 | Leading monomials `xᵢ y_π(i)` form a perfect matching | `quadraticMatching_bijective`, `archived_mixed_pivots`, `archived_mixed_zero_before`, `archived_polar_leading` | compiled | — |
| 433–443 | How the witnesses were found (bipartite matching) | — | not a claim | Method description. |
| 444–456 | Buchberger: the `qᵢ` are a Gröbner basis; height 54; regular sequence by Cohen–Macaulayness | Buchberger: `Groebner.isGroebnerBasis_of_coprime`, `Groebner.initialIdeal_span_of_coprime`, `Groebner.Paper.row11`; height 54: `Groebner.MonomialHeight.height_pairIdeal`, `prime_contains_pair`, `primeHeight_choice`; regular sequence: `CM.mem_of_mul_mem_of_coprime`, `CM.q_regular` | compiled (Gröbner basis, height 54) / **drafted, not compiled** (regular sequence) | Different route for the regular sequence: Mathlib at our pin has no Cohen–Macaulay rings, so `q_regular` is proved directly from the same Gröbner input (division by a Gröbner basis with pairwise coprime leading monomials), in the graded polynomial ring. |
| 457–482 | Lemma 4.1: `dim A/I ≤ N − s` when the initial forms are a regular sequence; associated graded presentation | Hilbert–Serre: `CM.orderLE_length_fam`; Hilbert–Samuel: `CM.gnoeth_grFam`, `CM.orderLE_chi`; dimension theorem `dim A ≤ d(A)`: `CM.length_quot_add_le_rel`, `CM.chain_bound`, `CM.ringKrullDim_le_of_orderLE_chi`; Lemma 4.1: `CM.orderLE_R`, `CM.length_gr_le` (graded surjection), `CM.lemma41_chain`, `CM.lemma41`; graded presentation: `InitialForms.*`; `hA` from `m = (g₁..g_N)`: `CM.length_le_card`, `CM.pow_le_span_mono`, `CM.orderLE_hilbR_zero`, `CM.lemma41_of_span`; instance `A = 𝔽₃⟦x, y⟧`, `fᵢ* = qᵢ`: `CM.PSInstance.Hs_mul`, `Hs_relI`, `hreg_q`, `lemma41_q` | **drafted, not compiled** | Follows the paper's proof. The hypothesis `hA` is discharged for any `m` generated by `N` elements; for `𝔽₃⟦x, y⟧` the initial forms of the `qᵢ` are the `qᵢ` (quadratic forms), and `hreg` is `q_regular` read through homogeneous components. `lemma41_q`: `dim A ⧸ I ≤ 54` for `I ⊇ (qᵢ)`. |
| 483–498 | Normal elimination: `Â = k⟦z⟧/I`, `fᵢ* = qᵢ`, `dim ≤ 251 − 54 = 197` in characteristic three | `UpperBound.squareLocalDimension_le_197`, `squareLocalDimension_eq_197_of_charThree`, `Formal.H_bijective` | compiled | Same conclusion; different route. |

## §5 Transfer to characteristic zero (lines 499–545)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 500–504 | Rank 2101 over `ℚ` too; 251 integral tangent generators independent over `ℚ` | `square_jacobian_rank`, `square_jacobian_nullity` | compiled | Every field of characteristic 0. |
| 505–520 | Kernels free direct summands over `ℤ₍₃₎`; modular kernel vectors lift; the 251 vectors are an `R₀`-basis; the 54 rows lift | `Z3.kernel_basis_Z3`, `Z3.kernelBasisZ3`, `Z3.kernel_retract_Z3`, `Z3.kernel_lift_mod3`, `integer_annihilates` | drafted | Right kernel stated; exact lifts of the 54 rows are in `CM.LiftedQuadrics.lamExact_annihilates`. Arbitrary left-kernel lifting and an idempotent projection are drafted in `LeftKernelLift.actual_leftKernel_lift_mod3` and `project_idempotent`. A linear retraction and free-coordinate basis are drafted in `LeftKernelLift.leftKernel_linear_retraction`, `leftKernelFreeEquiv`, `leftKernelBasis`. |
| 521–545 | `3, q̃₁, …, q̃₅₄` regular in `ℤ₍₃₎[z]`; regular in `ℚ⟦z⟧`; upper bound in characteristic 0 | `Transfer.charZero_dim_le`, `CharZeroBound.squareLocalDimension_le_197`, `squareLocalDimension_eq_197_of_charZero`; lift: `CM.LiftInstance.isWeaklyRegular_q`, `cons_regular_lift`, `lifted_regular_local`, `lifted_regular_flat`, `ker_rho3`, `lifted_quadrics_regular`, `CM.LiftedQuadrics.map_qtOf`, `qtOf_regular` | compiled (conclusion) / **drafted, not compiled** (regular-sequence lift) | The lift avoids unmixedness: `3, q̃₁, …` is regular by `cons` from the regularity of the `qᵢ` mod 3, then by permutation in the local ring and flat base change. `CM.LiftedQuadrics.qtOf` builds `q̃ℓ` from lifted rows `λ̃ℓ` through the integer mixed derivatives, and `map_qtOf` proves its reduction is `qℓ`, so `qtOf_regular` applies to the paper's left-kernel lifts. `lamExact_annihilates`, `map_qtExact`, `qtExact_regular` connect the exact integer left-kernel rows to the lifted quadrics. The conclusion, `dim = 197` in characteristic 0, is compiled by a different route: graded Nakayama transfer of the finite spanning certificate. |

## §6 Formal branches and Hilbert function (lines 546–605)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 547–555 | `𝔭_L`, `𝔭_R` are prime, minimal and distinct | `Formal.branchPrime_minimal_charThree`, `_charZero`, `Formal.branchPrime_ne`, `sqBranchPrime_*` | compiled | — |
| 556–562 | Slice independence: the full-parameter kernel equals the slice kernel | `Formal.slice_independent`, `Formal.ker_fullHat_charThree`, `_charZero` | compiled | — |
| 563–575 | `H(c, x, y)` is a formal coordinate change; branch ideals `(y)`, `(x)`; intersection `k⟦c⟧` of dimension 143, the orbit subgerm | `Formal.intersectionEquiv`, `Formal.ringKrullDim_intersection`, `Formal.orbitSubgermEquiv`, `Formal.sqIntersectionEquiv` | compiled | — |
| 576–582 | Branch maps kill the nilradical; the reduced variety has tangent dimension 251 and is singular | `Formal.hilbertValue_reduced_one`, `Formal.not_isRegularLocalRing_Ared_charThree`, `_charZero` | compiled | — |
| 583–597 | The 1995 residual combinations; rank of `[J | M]` is 2749 over `ℚ` and `F₃`; quadratic initial space 648; `H(2) = 31626 − 648 = 30978` | `AugmentedTrace.augmented_rank`, `MixedRank.finrank_Rel`, `HilbertTwo.hilbertValue_two_add`, `HilbertValues.hilbert_initial` | compiled | Over every field with `2 ≠ 0`, so in particular characteristic 3 and 0. |
| 598–604 | The reduced two-branch union has `H(2) = 28710`, so `Â` is nonreduced or has another minimal prime | `Formal.hilbertValue_two_twoBranch`, `Formal.not_isReduced_or_extra_minimalPrime` | compiled | — |
| 604–605 | Full Hilbert series and number of branches remain open | — | not a claim | Open problem. |

## §7 tail and Reproducibility (lines 706–740)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 710–718 | Census input pinned by SHA-256; Hadamard bound makes reduction at the chosen prime faithful | `tools/catalogue/gen_catalogue_lean.py`, CI hash checks | not needed | The Lean census uses exact rank certificates. `PaperDetails.minor_vanishing_iff_mod_prime` drafts the determinant-reduction implication given the strict magnitude bound. A separate Leibniz bound and primality certificate are drafted below; the exact squared Hadamard inequality for all minor sizes 0–4 is drafted in `HadamardSmall.squared_hadamard`. |
| 719–721 | The open parameterizations preserve every nonzero factor and keep all 49 summands | `Census.family_factor_ne_zero` | drafted | Every field, every parameter value, both families. |
| 722–740 | Reproducibility, archives, collaboration note | — | not a claim | — |

## Appendix A (lines 760–900)

| Lines | Claim | Declaration | Status | Difference from the paper |
|---|---|---|---|---|
| 765–780 | Index conventions; Jacobian columns as tensors | `squareVariableNumber`, `Decomposition.jacobianColumn` | compiled | — |
| 781–795 | `tangent_bases.npz`: 143, 54, 54 retained vectors | `archived_frame_rank`, `archived_frame_split` | compiled | Data pinned by SHA-256 in the repository manifest. |
| 796–806 | The column of `M` is the cross coefficient of `Q₂` | `archived_mixed_coefficients`, `archived_polar_leading` | compiled | — |
| 807–830 | The matching permutation `π`; the sample coefficient `M₀,₁₉` | `quadraticMatching_bijective`, `archived_mixed_pivots`, `PaperDetails.appendix_mixed_entry`, `appendix_covector_entry`, `appendix_unique_support`, `appendix_earlier_zero`, `appendix_projected_coefficient` | compiled (matching and pivots); drafted (worked example) | Numeric example now has direct source statements. |
| 831–900 | Independent replay specification | — | not a claim | Verifier description; the Lean kernel checks replace it. |

## Historical open rows (see latest extension below)

1. **Regular sequence (lines 444–456) and the dimension step of Lemma 4.1 (457–482).** Need Cohen–Macaulay and Hilbert–Samuel theory, absent from Mathlib at our pin. The Gröbner basis, height 54 and the graded presentation are formalized; the bound they serve is compiled by another route.
2. **Regular-sequence lift over `ℤ₍₃₎` (lines 521–545).** Drafted in `CM/LiftInstance.lean` and `CM/LiftedQuadrics.lean` (lifted quadrics from lifted rows); the left-kernel property has a draft in `CM.LiftedQuadrics.lamExact_annihilates`. The characteristic-zero bound is compiled by another route.

## Coverage extension (drafts; not a kernel acceptance claim)

| Claim | New declaration(s) | Source coverage |
|---|---|---|
| Arbitrary left-kernel vector modulo 3 lifts over the localized integers | `LeftKernelLift.actual_leftKernel_lift_mod3` | Draft, using the actual checked integer elimination trace |
| Left-kernel projection is idempotent | `LeftKernelLift.project_inLeft`, `project_eq_self`, `project_idempotent` | Draft; explicit linear retraction and basis added below |
| Exact useful-anchor counts in both characteristics | `Catalogue.usefulAnchors_count_2445`, `usefulAnchors_count_5969` | Draft, two-sided finite certificates; generated catalogue absent from the archive used for this patch |
| Lemma 4.1 graded presentation | `CM.firstIdeal_inf_pow_le_relI`, `toGr_firstIdeal_injective`, `lemma41_gradedPieceEquiv` | Draft of each graded piece and homogeneous product compatibility; direct-sum graded-ring assembly remains open |
| Appendix A.2 worked example | `PaperDetails.appendix_*` | Draft, directly checking actual sparse mixed entries and covector |
| Faithful modular reduction of bounded determinants | `PaperDetails.minor_vanishing_iff_mod_prime` | Draft, conditional on the determinant size bound |

## Further coverage extension (historical source drafts, not kernel acceptance)

| Target | Declaration / evidence | Residual gap |
|---|---|---|
| Original quadratic ideal height 54 | `CM.quadraticIdeal_height_eq_54` | Source proof drafted using regularity and prime chains; compilation not checked. |
| Full left kernel | `LeftKernelLift.leftKernel_linear_retraction`, `leftKernelFreeEquiv`, `leftKernelBasis` | Source proofs drafted over every commutative ring; compilation not checked. |
| Multiplication of graded pieces | `CM.relI_mul_pow`, `graded_product_congr`, `lemma41_product_representatives` | Full external direct-sum ring equivalence drafted in `CM.GradedRingAssembly.lemma41_ringEquiv`; identification of the source with the polynomial quotient by the ideal of initial forms still needs a bundled proof. |
| Formal reduction modulo 3 | `Formal.map_subst_centered`, `inverse_tuple_baseChange`, `normal_substitution_mod3` | Actual selected Jacobian minor, inverse over R0, and all residual-equation base change drafted in `Formal.NormalEliminationZ3.normal_elimination_exists`. Explicit transport to the paper’s fixed tangent frame and quadratic initial-form identification not completed here. |
| Census modulus | `PaperDetails.censusPrime_isPrime`, `censusPrime_hadamard_expression`, `censusMinor_vanishing_iff` | Exact squared Hadamard bound for arbitrary integer matrices of every relevant size (≤4) drafted in `PaperDetails.HadamardSmall.squared_hadamard`; faithful reduction using that bound in `censusMinor_vanishing_iff_hadamard`. |
| Catalogue source binding | `tools/catalogue/verify_source_binding.py`, CI invocation | External coordinate-by-coordinate verifier, not a Lean theorem about NPZ parsing or SHA-256. Synthetic positive/negative tests only; original NPZ not included in input archive. |
| Geometric orbit closure dimension | Existing `Formal.finrank_range_dOrbit`, `Formal.ringKrullDim_slice` | Still open: geometric dimension of the actual algebraic orbit closure. |

No change to paper.tex. No claim of 100% semantic coverage or successful compilation is made. The existing audit entries labelled compiled are inherited from the input archive and have not been independently replayed here.

### Third coverage extension (historical snapshot) (source drafts, not kernel acceptance)

- `NormalEliminationZ3.normal_elimination_exists`: actual 2101-equation unit-minor chart over R0, 251 free coordinates, centered inverse, reduction of both inverse identities and every residual equation; selected equations vanish. No assumed minor or assumed inverse. Explicit comparison to the frozen tangent-frame coordinates and its quadratic initial forms remains separate.
- `HadamardSmall.squared_hadamard`: exact squared bound for every integer entry bound and each order 0–4, including stacked minors. Finite sign-corner checks independently enumerated in Python (66,067 cases; maxima 1, 1, 4, 16, 256). This is not a Lean kernel result. The argument uses endpoint convexity from determinant multilinearity, not the earlier factorial estimate.
- `GradedRingAssembly.lemma41_ringEquiv` and `_of`: direct-sum commutative ring structures built independently from bilinear representative multiplication, inverse ring maps, and preservation of the grading. A separate bundled identification of the source with the polynomial quotient by the initial forms is still needed for the literal paper statement.
- Geometric orbit closure dimension and kernel-level source catalogue provenance still open. The NPZ was not included and could not be retrieved in this environment.

The new declarations are registered in `Audit.lean`. No compilation or kernel acceptance is claimed.

## Fourth coverage extension — current source status

All entries below are **drafted, not compiled**. This supersedes earlier
open-row descriptions for these specific targets; it does not certify Lean
elaboration, kernel acceptance, or an independent complete paper audit.

| Target | Declaration(s) | Status |
|---|---|---|
| Geometric orbit closure (not only tangent rank) | `Formal.OrbitClosure.orbitClosure_vanishingIdeal`, `orbit_trdeg_lower`, `orbit_trdeg_upper`, `orbitClosure_dimension_eq_143`, `orbitClosure_localDimension_eq_143` | Draft: actual orbit vanishing ideal over infinite fields, normalized 143-parameter chart, both transcendence-degree bounds. Includes algebraically closed fields in the paper's characteristics. |
| Original quadratic ideal height | `CM.quadraticIdeal_height_eq_54` | Prior draft retained. |
| Literal polynomial quotient in Lemma 4.1 | `CM.GradedRingAssembly.projection_ker`, `CM.GradedPolynomial.basePolynomialEquiv`, `lemma41_finite_polynomialQuotientEquiv` | Draft: actual homogeneous coefficient map, kernel ideal, multiplication and finite-prefix regularity, not just degreewise dimensions. |
| Full left-kernel freeness and retraction | `LeftKernelLift.leftKernel_linear_retraction`, `leftKernelFreeEquiv`, `leftKernelBasis` | Prior drafts retained. |
| Reduction and the frozen integral frame | `Formal.NormalEliminationZ3.normal_elimination_frozen_frame`, `actual_residual_initial_quadric`, `fullFrameQuadric_mixed` | Draft: actual normal equations, reduction of the substitution and exact mixed coefficients using the lifted left-kernel covectors. |
| Hadamard and modulus | `PaperDetails.HadamardSmall.squared_hadamard`, `censusMinor_vanishing_iff_hadamard`, `PaperDetails.censusPrime_isPrime` | Prior drafts retained. |
| Original catalogue provenance | `tools/catalogue/verify_source_binding.py` and CI | External verifier retained; original NPZ absent, real dataset replay and kernel-level source binding not established. Exact anchor count drafts require generated catalogue data. |

The remaining catalogue provenance issue is not closed by the mathematical
drafts. No original-data validation or complete kernel replay is claimed.
The paper is unchanged. All major new declarations are registered in Audit.lean.
