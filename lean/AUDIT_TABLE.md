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
| 676–681 | Unique rank-two term per group; its row and column spaces contain those of the other six | `Census.base_rel_left`, `base_rel_right`, `family_rel` | drafted | Stated as `M_child = Z M_anchor = M_anchor Z'`, equivalent to the containments (`rowSpan_le_of_stack`). Uniqueness is not stated separately; the test uses existence. |
| 681–682 | Left and right changes preserve the inclusions | `Census.rowRel_changeBasis`, `colRel_changeBasis`, `Equivalences.shape_of_equivalent` | drafted | — |
| 682–688 | Persistence at closure points with the same profile; equal rank sums force equality per label; anchors keep rank two | `Census.closure_stackOK`, `Census.rank_eq_budget`, `Census.anchorTest_of_mem`, `Census.anchorTest_of_shape` | drafted | Sums are both 192. |
| 688–689 | The other orientation gives the same condition with roles exchanged | `anchor false`, `base_rel_right` | drafted | — |
| 689–694 | The filter: six rank-two terms each accommodating six rank-one terms, every rank-one term with a candidate anchor | `Catalogue.AnchorTest` | drafted | Matches `alphatensor_rank_profiles.py` (`Useful`: rank two with at least six children). |
| 696–698 | Over ℚ and 𝔽₃ exactly 14,149 points have the full profile | `Section7.census` (1), `Catalogue.Q/F3.card_fullProfile` | drafted | Every field of characteristic 3 or 0. |
| 698–699 | These are precisely the points satisfying the rank bounds, which exclude 87 entries | `Section7.census` (2, 3), `Section7.rank_bound_exclusion` | drafted | Excluded from the closure of the saturated families. |
| 700–703 | The space test excludes 2445 and 5969 (two and one useful anchors) | `Section7.census` (4), `Section7.anchor_exclusion` | drafted | Excluded from the closure of the families closed under all equivalences (`eqClosed`). The anchor counts (two, one) are recorded in `Catalogue/REPORT.md`, not as theorems. |
| 703–704 | A decomposition in the closure with this profile requires at least six | `Census.anchorTest_of_shape` | drafted | — |
| 704–705 | All 14,147 points passing both tests have the full profile | `Section7.census` (5) | drafted | — |
| 705–707 | Their membership remains open; other components through `p` possible | — | not a claim | Statement of an open problem. |

## §1–§6

Mapped in `STATUS.md` (rows for Theorem 1.1, §2–§6). A full line-by-line pass over lines 1–605
is still to be done; it will be added here before the merge.
