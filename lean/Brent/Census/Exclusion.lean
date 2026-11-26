import Brent.Census.AlphaTensor

/-!
# Tasks 2 and 3 (F18): the exclusions are statements about the family closures

DRAFT, NOT YET COMPILED.

Paper, lines 659–660 and 694–707: the rank tests "rule out membership" of catalogue points in
the family closures; "These are precisely the points that satisfy the two rank bounds, which
exclude 87 entries"; the row- and column-space test "excludes two of the 14,149 points, at
zero-based catalogue indices 2445 and 5969".

* **Task 2.** `alphaTensor_bound_excluded` excludes a point from the closure of the union of the
  two *saturated* family images (closed under summand permutations and the other equivalences in
  `Dominated`). Each family closure `familyClosure k left = closure (imageA k left)` is contained
  in that set, so the point lies in neither family closure (`not_mem_familyClosure`). This is the
  paper's "rule out membership", and it is stronger: it also excludes the permuted closures
  ("even allowing summand and mode permutations", line 669).
* **Task 3.** The 87 rank-bound indices and the two anchor-test indices `2445`, `5969` are
  disjoint, so 89 catalogue entries are excluded in total (`excluded_card`).

Still missing for Task 3 (needs Task B's `Neg.lean` and a new geometric lemma): that a point of
a family closure with the full rank profile satisfies the anchor test (paper lines 678–688:
"They persist at closure points with the same profile because the relevant minors of the
stacked matrices vanish"). Task B certifies the anchor test *fails* at 2445 and 5969; the
persistence lemma turns that into non-membership. It is not drafted here.
-/

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure

variable {k : Type} [Field k]

/-- Each family closure lies in the closure of the union of the saturated family images. -/
theorem familyClosure_subset_saturated (left : Bool) :
    familyClosure k left ⊆ closure (saturation (imageA k true) ∪ saturation (imageA k false)) := by
  unfold familyClosure
  apply closure_mono
  cases left
  · exact (subset_saturation _).trans Set.subset_union_right
  · exact (subset_saturation _).trans Set.subset_union_left

/-- **Task 2.** A point excluded by one of the 87 rank-bound certificates lies in neither family
closure, in characteristic three and zero. -/
theorem not_mem_familyClosure (hk : CharP k 3 ∨ CharZero k) {n : ℕ} {b : BoundW}
    (h : (n, b) ∈ boundWitnesses) (v : Affine k) (hv : b.Agrees v) (left : Bool) :
    v ∉ familyClosure k left := fun hmem =>
  alphaTensor_bound_excluded hk h v hv (familyClosure_subset_saturated left hmem)

/-- The 87 rank-bound indices. -/
def boundIndices : List ℕ := boundWitnesses.map Prod.fst

/-- The two anchor-test indices (paper line 701). -/
def anchorIndices : List ℕ := [2445, 5969]

/-- **Task 3 (counting part).** The two exclusion lists are disjoint and together have 89
distinct catalogue indices, all below 14,236. -/
theorem excluded_card :
    (boundIndices ++ anchorIndices).Nodup ∧ (boundIndices ++ anchorIndices).length = 89 ∧
      ∀ n ∈ boundIndices ++ anchorIndices, n < 14236 := by
  decide +kernel

end Brent.Census
