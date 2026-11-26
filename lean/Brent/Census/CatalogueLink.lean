import Brent.Catalogue.AllFields
import Brent.Census.AnchorClosure

/-!
# §7: the catalogue exclusions as statements about the family closures (F18, part 5)

DRAFT, NOT YET COMPILED.

Paper, lines 659–705. The census (`Brent.Catalogue`) is about catalogue indices; the paper's
conclusion is that the excluded entries are not in the family closures. This file connects the
two.

* `catPoint k p : Affine k` is catalogue entry `p` as a point of `k^2352`, in the convention of
  `Census.AlphaTensor`: summand `(i, j)` is catalogue row `7 i + j` (`sE`), vertex `(a, b)` is
  matrix index `2 a + b` (`vE`), `u = U`, `v = V`, `w = Wᵀ`. Its mode matrices are the catalogue
  factors, reindexed (and transposed in mode `w`), so they have the catalogue ranks
  (`rank_modeMat_catPoint`).
* **Rank bounds** (`rankBounds_of_mem`): on a family closure every summand `(i, j)` has every mode
  of rank at most `cᵢ cⱼ` (`closure_budgetOK`). Only 13 summands have budget above one and one
  above two, so a closure point satisfies `RankBounds`.
* **Anchor test** (`anchorTest_of_mem`): at a closure point with the full profile, the total rank
  is 192, the sum of the budgets, so every rank equals its budget (`rank_eq_budget`). Anchors
  `(i, 0)` (left) or `(0, j)` (right) have rank two and the stacking conditions
  (`closure_stackOK`) give the span containments, so `AnchorTest` holds.
* **Conclusion** (`catalogue_excluded`): over every field of characteristic three or zero, the
  87 entries failing the rank bounds and the entries 2445 and 5969 lie in neither family
  closure.
-/

open scoped BigOperators

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure Brent.Catalogue

/-! ### Index conventions -/

/-- Vertex `(a, b)` is matrix index `2 a + b`. -/
def vE : SquareVertex ≃ Fin 4 := finProdFinEquiv

/-- Summand `(i, j)` is catalogue row `7 i + j`. -/
def sE : SquareSummand ≃ Fin 49 := finProdFinEquiv

/-- Modes `u, v, w` are catalogue modes `0, 1, 2`. -/
def mE : Mode ≃ Fin 3 where
  toFun | .u => 0 | .v => 1 | .w => 2
  invFun i := if i = 0 then .u else if i = 1 then .v else .w
  left_inv m := by cases m <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The integer mode matrix of catalogue point `p` (transposed in mode `w`). -/
def catMode (p : Fin 14236) (s : SquareSummand) : Mode → Matrix (Fin 4) (Fin 4) ℤ
  | .u => factor p (sE s) 0
  | .v => factor p (sE s) 1
  | .w => (factor p (sE s) 2).transpose

/-- Catalogue entry `p` as a point of `k^2352`. -/
def catPoint (k : Type) [Field k] (p : Fin 14236) : Affine k :=
  fun x => ((catMode p x.1 x.2.1 (vE x.2.2.1) (vE x.2.2.2) : ℤ) : k)

variable {k : Type} [Field k]

theorem modeMat_catPoint (p : Fin 14236) (s : SquareSummand) (m : Mode) :
    modeMat (catPoint k p) s m = ((catMode p s m).map (Int.cast : ℤ → k)).submatrix vE vE := rfl

theorem rank_catMode (p : Fin 14236) (s : SquareSummand) (m : Mode) :
    ((catMode p s m).map (Int.cast : ℤ → k)).rank = rk k p (sE s) (mE m) := by
  cases m
  · rfl
  · rfl
  · show ((factor p (sE s) 2).transpose.map (Int.cast : ℤ → k)).rank = rk k p (sE s) 2
    rw [← Matrix.transpose_map, Matrix.rank_transpose]
    rfl

theorem rank_modeMat_catPoint (p : Fin 14236) (s : SquareSummand) (m : Mode) :
    (modeMat (catPoint k p) s m).rank = rk k p (sE s) (mE m) := by
  rw [modeMat_catPoint, Matrix.rank_submatrix, rank_catMode]

/-! ### Rank bounds on the closures -/

theorem budget_le_four (s : SquareSummand) : budget s.1 * budget s.2 ≤ 4 := by
  revert s; decide

theorem card_budget_gt_one :
    (Finset.univ.filter fun s : SquareSummand => 1 < budget s.1 * budget s.2).card = 13 := by
  decide

theorem card_budget_gt_two :
    (Finset.univ.filter fun s : SquareSummand => 2 < budget s.1 * budget s.2).card = 1 := by
  decide

/-- **A family-closure point satisfies the two rank bounds.** -/
theorem rankBounds_of_mem (p : Fin 14236) (left : Bool)
    (h : catPoint k p ∈ familyClosure k left) : RankBounds k p := by
  classical
  have hb := closure_budgetOK (k := k) left h
  have hrk : ∀ s m, rk k p (sE s) (mE m) ≤ budget s.1 * budget s.2 := fun s m => by
    rw [← rank_modeMat_catPoint]; exact hb s m
  have key : ∀ r : ℕ, (Finset.univ.filter fun n : Fin 49 => ∃ mi, r < rk k p n mi) ⊆
      (Finset.univ.filter fun s : SquareSummand => r < budget s.1 * budget s.2).map
        sE.toEmbedding := by
    intro r n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨mi, hmi⟩ := hn.2
    rw [Finset.mem_map_equiv, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, lt_of_lt_of_le ?_ (hrk (sE.symm n) (mE.symm mi))⟩
    simpa using hmi
  refine ⟨?_, ?_⟩
  · refine (Finset.card_le_card (key 1)).trans ?_
    rw [Finset.card_map, card_budget_gt_one]
  · refine (Finset.card_le_card (key 2)).trans ?_
    rw [Finset.card_map, card_budget_gt_two]

/-! ### Exact ranks at full-profile closure points -/

theorem sum_budget : ∑ s : SquareSummand, ∑ _m : Mode, budget s.1 * budget s.2 = 192 := by
  decide

theorem sum_fullProfile :
    (fullProfile.map fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2).sum = 192 := by
  decide

theorem sum_rk_of_profile (p : Fin 14236) (hp : profile k p = fullProfile) :
    ∑ s : SquareSummand, ∑ m : Mode, rk k p (sE s) (mE m) = 192 := by
  have h := congrArg (fun M : Multiset (ℕ × ℕ × ℕ) => (M.map fun x => x.1 + x.2.1 + x.2.2).sum) hp
  simp only [profile, Multiset.map_map, Function.comp_def, sum_fullProfile] at h
  rw [← h]
  have hm : ∀ n : Fin 49, ∑ m : Mode, rk k p n (mE m) = rk k p n 0 + rk k p n 1 + rk k p n 2 := by
    intro n
    rw [Equiv.sum_comp mE (fun mi => rk k p n mi), Fin.sum_univ_three]
  simp only [hm]
  rw [Equiv.sum_comp sE (fun n => rk k p n 0 + rk k p n 1 + rk k p n 2)]
  rfl

/-- **Every rank equals its budget** at a full-profile point of a family closure. -/
theorem rank_eq_budget (p : Fin 14236) (left : Bool) (h : catPoint k p ∈ familyClosure k left)
    (hp : profile k p = fullProfile) (s : SquareSummand) (m : Mode) :
    rk k p (sE s) (mE m) = budget s.1 * budget s.2 := by
  have hb := closure_budgetOK (k := k) left h
  have hle : ∀ s m, rk k p (sE s) (mE m) ≤ budget s.1 * budget s.2 := fun s m => by
    rw [← rank_modeMat_catPoint]; exact hb s m
  have hsum := sum_rk_of_profile p hp
  have hle' : ∀ s ∈ (Finset.univ : Finset SquareSummand),
      ∑ m : Mode, rk k p (sE s) (mE m) ≤ ∑ _m : Mode, budget s.1 * budget s.2 :=
    fun s _ => Finset.sum_le_sum fun m _ => hle s m
  have heq := (Finset.sum_eq_sum_iff_of_le hle').mp (hsum.trans sum_budget.symm) s
    (Finset.mem_univ _)
  exact (Finset.sum_eq_sum_iff_of_le fun m _ => hle s m).mp heq m (Finset.mem_univ _)

/-! ### Stacked ranks between the two conventions -/

theorem rank_fromRows_reindex (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    (Matrix.fromRows ((A.map (Int.cast : ℤ → k)).submatrix vE vE)
      ((B.map (Int.cast : ℤ → k)).submatrix vE vE)).rank =
      ((stack A B).map (Int.cast : ℤ → k)).rank := by
  rw [stack_map]
  have e : Matrix.fromRows ((A.map (Int.cast : ℤ → k)).submatrix vE vE)
      ((B.map (Int.cast : ℤ → k)).submatrix vE vE) =
      (Matrix.fromRows (A.map (Int.cast : ℤ → k)) (B.map (Int.cast : ℤ → k))).submatrix
        (Equiv.sumCongr vE vE) vE := by
    ext i j
    cases i <;> rfl
  rw [e, Matrix.rank_submatrix]

theorem rank_fromCols_reindex (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    (Matrix.fromCols ((A.map (Int.cast : ℤ → k)).submatrix vE vE)
      ((B.map (Int.cast : ℤ → k)).submatrix vE vE)).rank =
      ((stack A.transpose B.transpose).map (Int.cast : ℤ → k)).rank := by
  rw [← rank_fromRows_reindex]
  have e : Matrix.fromCols ((A.map (Int.cast : ℤ → k)).submatrix vE vE)
      ((B.map (Int.cast : ℤ → k)).submatrix vE vE) =
      (Matrix.fromRows ((A.transpose.map (Int.cast : ℤ → k)).submatrix vE vE)
        ((B.transpose.map (Int.cast : ℤ → k)).submatrix vE vE)).transpose := by
    ext i j
    cases j <;> rfl
  rw [e, Matrix.rank_transpose]

theorem rank_map_transpose (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (A.transpose.map (Int.cast : ℤ → k)).rank = (A.map (Int.cast : ℤ → k)).rank := by
  rw [← Matrix.transpose_map, Matrix.rank_transpose]

/-- From stacked-rank equalities in our convention to `CanAnchor` in the catalogue's. -/
theorem canAnchor_of_stack (p : Fin 14236) (t a : SquareSummand)
    (h : ∀ m : Mode,
      (Matrix.fromRows (modeMat (catPoint k p) t m) (modeMat (catPoint k p) a m)).rank =
        (modeMat (catPoint k p) a m).rank ∧
      (Matrix.fromCols (modeMat (catPoint k p) t m) (modeMat (catPoint k p) a m)).rank =
        (modeMat (catPoint k p) a m).rank) :
    CanAnchor k p (sE t) (sE a) := by
  intro mi
  rw [rowSpace_le_iff_rank, colSpace_le_iff_rank]
  have hu := h .u
  have hv := h .v
  have hw := h .w
  simp only [modeMat_catPoint, Matrix.rank_submatrix, rank_fromRows_reindex,
    rank_fromCols_reindex, catMode] at hu hv hw
  fin_cases mi
  · exact ⟨hu.1, by rw [rank_map_transpose]; exact hu.2⟩
  · exact ⟨hv.1, by rw [rank_map_transpose]; exact hv.2⟩
  · refine ⟨?_, ?_⟩
    · have := hw.2
      simp only [Matrix.transpose_transpose] at this
      rw [this, rank_map_transpose]
    · rw [rank_map_transpose]
      exact hw.1

/-! ### The anchor test at full-profile closure points -/

theorem budget_eq_one_iff (s : SquareSummand) :
    budget s.1 * budget s.2 = 1 ↔ s.1 ≠ 0 ∧ s.2 ≠ 0 := by
  revert s; decide

theorem budget_eq_two_left (i : Fin 7) (hi : i ≠ 0) : budget i * budget 0 = 2 := by
  revert i; decide

theorem budget_eq_two_right (j : Fin 7) (hj : j ≠ 0) : budget 0 * budget j = 2 := by
  revert j; decide

theorem inGroup_of_one (left : Bool) (s : SquareSummand) (hs : s.1 ≠ 0 ∧ s.2 ≠ 0) :
    InGroup left s := by
  cases left <;> simp [InGroup, hs.1, hs.2]

/-- The anchors of an orientation: `(i, 0)` or `(0, i)`, `i ≠ 0`. -/
def anchorOf (left : Bool) (i : Fin 7) : SquareSummand := if left then (i, 0) else (0, i)

/-- The children of anchor `i`: `(i, j)` or `(j, i)`, `j ≠ 0`. -/
def childOf (left : Bool) (i j : Fin 7) : SquareSummand := if left then (i, j) else (j, i)

theorem anchor_childOf (left : Bool) (i j : Fin 7) :
    anchor left (childOf left i j) = anchorOf left i := by
  cases left <;> rfl

theorem childOf_ne (left : Bool) (i j : Fin 7) (hi : i ≠ 0) (hj : j ≠ 0) :
    (childOf left i j).1 ≠ 0 ∧ (childOf left i j).2 ≠ 0 := by
  cases left <;> simp [childOf, hi, hj]

theorem anchorOf_budget (left : Bool) (i : Fin 7) (hi : i ≠ 0) :
    budget (anchorOf left i).1 * budget (anchorOf left i).2 = 2 := by
  cases left
  · exact budget_eq_two_right i hi
  · exact budget_eq_two_left i hi

theorem anchor_of_one (left : Bool) (s : SquareSummand) (hs : s.1 ≠ 0 ∧ s.2 ≠ 0) :
    anchor left s = anchorOf left (if left then s.1 else s.2) := by
  cases left <;> rfl

theorem anchorOf_injective (left : Bool) : Function.Injective (anchorOf left) := by
  intro i i' h
  cases left
  · simpa [anchorOf] using h
  · simpa [anchorOf] using h

theorem childOf_injective (left : Bool) (i : Fin 7) : Function.Injective (childOf left i) := by
  intro j j' h
  cases left
  · simpa [childOf] using h
  · simpa [childOf] using h

theorem card_nonzero : (Finset.univ.filter fun i : Fin 7 => i ≠ 0).card = 6 := by decide

/-- **At a full-profile point of a family closure, the anchor test passes.** -/
theorem anchorTest_of_mem (p : Fin 14236) (left : Bool)
    (h : catPoint k p ∈ familyClosure k left) (hp : profile k p = fullProfile) :
    AnchorTest k p := by
  classical
  have hr := rank_eq_budget p left h hp
  -- ranks of mode matrices
  have hM : ∀ s m, (modeMat (catPoint k p) s m).rank = budget s.1 * budget s.2 := fun s m => by
    rw [rank_modeMat_catPoint, hr]
  -- every summand of a rank-one group can be anchored by its anchor
  have hcan : ∀ t : SquareSummand, t.1 ≠ 0 ∧ t.2 ≠ 0 →
      CanAnchor k p (sE t) (sE (anchor left t)) := by
    intro t ht
    have hst := closure_stackOK (k := k) left t (inGroup_of_one left t ht) h
    have ha : ∀ m, (modeMat (catPoint k p) (anchor left t) m).rank = 2 := fun m => by
      rw [hM, budget_anchor left t (inGroup_of_one left t ht)]
    apply canAnchor_of_stack
    intro m
    obtain ⟨h1, h2⟩ := hst m
    refine ⟨le_antisymm ((ha m).symm ▸ h1) (rank_le_fromRows _ _), ?_⟩
    refine le_antisymm ((ha m).symm ▸ h2) ?_
    rw [← Matrix.rank_transpose, ← Matrix.rank_transpose (Matrix.fromCols _ _),
      show (Matrix.fromCols (modeMat (catPoint k p) t m)
        (modeMat (catPoint k p) (anchor left t) m)).transpose =
        Matrix.fromRows (modeMat (catPoint k p) t m).transpose
          (modeMat (catPoint k p) (anchor left t) m).transpose by
        ext i j; cases i <;> rfl]
    exact rank_le_fromRows _ _
  -- rank classes
  have hone : ∀ s : SquareSummand, sE s ∈ rankOne k p ↔ s.1 ≠ 0 ∧ s.2 ≠ 0 := by
    intro s
    simp only [rankOne, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← budget_eq_one_iff]
    constructor
    · intro hs
      have := hs (mE .u)
      rwa [hr] at this
    · intro hs mi
      rw [← mE.apply_symm_apply mi, hr, hs]
  have htwo : ∀ i : Fin 7, i ≠ 0 → sE (anchorOf left i) ∈ rankTwo k p := by
    intro i hi
    simp only [rankTwo, Finset.mem_filter, Finset.mem_univ, true_and]
    intro mi
    rw [← mE.apply_symm_apply mi, hr, anchorOf_budget left i hi]
  -- anchors are useful
  have huseful : ∀ i : Fin 7, i ≠ 0 → Useful k p (sE (anchorOf left i)) := by
    intro i hi
    refine ⟨htwo i hi, ?_⟩
    have hsub : ((Finset.univ.filter fun j : Fin 7 => j ≠ 0).map
        ((childOf_injective left i).embedding.trans sE.toEmbedding)) ⊆
        children k p (sE (anchorOf left i)) := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨j, hj, rfl⟩ := hn
      rw [Finset.mem_filter] at hj
      simp only [Function.Embedding.trans_apply, Function.Injective.embedding_apply,
        Equiv.toEmbedding_apply]
      rw [children, Finset.mem_filter]
      have hc := childOf_ne left i j hi hj.2
      refine ⟨(hone _).2 hc, ?_⟩
      have := hcan (childOf left i j) hc
      rwa [anchor_childOf] at this
    have := Finset.card_le_card hsub
    rwa [Finset.card_map, card_nonzero] at this
  refine ⟨?_, ?_⟩
  · have hsub : ((Finset.univ.filter fun i : Fin 7 => i ≠ 0).map
        ((anchorOf_injective left).embedding.trans sE.toEmbedding)) ⊆
        (rankTwo k p).filter (Useful k p) := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨i, hi, rfl⟩ := hn
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨htwo i hi.2, huseful i hi.2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_map, card_nonzero] at this
  · intro n hn
    obtain ⟨t, rfl⟩ := sE.surjective n
    have ht := (hone t).1 hn
    refine ⟨sE (anchor left t), ?_, hcan t ht⟩
    rw [anchor_of_one left t ht]
    apply huseful
    cases left
    · exact ht.2
    · exact ht.1

/-! ### The exclusions -/

/-- **A catalogue entry failing the rank bounds is in neither family closure.** -/
theorem not_mem_of_not_rankBounds (p : Fin 14236) (hp : ¬ RankBounds k p) (left : Bool) :
    catPoint k p ∉ familyClosure k left :=
  fun h => hp (rankBounds_of_mem p left h)

/-- **A full-profile catalogue entry failing the anchor test is in neither family closure.** -/
theorem not_mem_of_not_anchorTest (p : Fin 14236) (hp : profile k p = fullProfile)
    (hA : ¬ AnchorTest k p) (left : Bool) : catPoint k p ∉ familyClosure k left :=
  fun h => hA (anchorTest_of_mem p left h hp)

/-- **The 89 exclusions of §7** (paper lines 696–702), over every field of characteristic three
or zero: the 87 entries that fail the rank bounds and the two entries 2445 and 5969 that fail the
row- and column-space test lie in neither family closure. -/
theorem catalogue_excluded (hk : CharP k 3 ∨ CharZero k) (p : Fin 14236)
    (hp : ¬ RankBounds k p ∨ p = 2445 ∨ p = 5969) (left : Bool) :
    catPoint k p ∉ familyClosure k left := by
  rcases hp with hp | hp
  · exact not_mem_of_not_rankBounds p hp left
  · have hf := facts_allFields k hk
    have hn : p.val ∈ neg2 := (mem_neg2 p).2 hp
    have hb : p.val ∉ bad87 := by
      rcases hp with rfl | rfl
      · exact neg2_not_bad.1
      · exact neg2_not_bad.2
    exact not_mem_of_not_anchorTest p ((hf.1 p).2 hb) (hf.2.2.2 p hn) left

/-- The excluded set has 89 elements. -/
theorem card_excluded (hk : CharP k 3 ∨ CharZero k) :
    (Finset.univ.filter fun p : Fin 14236 => ¬ RankBounds k p ∨ p = 2445 ∨ p = 5969).card = 89 := by
  classical
  have h87 := AllFields.card_not_rankBounds k hk
  have hrb : ∀ p : Fin 14236, p = 2445 ∨ p = 5969 → RankBounds k p := by
    intro p hp
    have hf := facts_allFields k hk
    rcases hp with rfl | rfl
    · exact (hf.2.1 _).2 neg2_not_bad.1
    · exact (hf.2.1 _).2 neg2_not_bad.2
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  · rw [h87]
    have : (Finset.univ.filter fun p : Fin 14236 => p = 2445 ∨ p = 5969) = {2445, 5969} := by
      ext p; simp
    rw [this]
    rfl
  · rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact h1 (hrb p h2)

end Brent.Census
