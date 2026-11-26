import Brent.Catalogue.Main
import Brent.Census.FieldTransfer

/-!
# The catalogue census over every field of characteristic three or zero

DRAFT, NOT YET COMPILED.

`Main.lean` proves the four census statements over `ℚ` and over `ZMod 3`. The paper's census
(lines 696–705) is stated "over both ℚ and 𝔽₃", and the goal asks for every field `K` with
`CharP K 3 ∨ CharZero K`. Every notion in `Defs.lean` depends on the field only through ranks
of integer matrices:

* `rk`, `profile`, `RankBounds`, `rankOne`, `rankTwo` directly;
* `CanAnchor` through span containment, which is a rank equality for the stacked matrix
  (`rowSpace_le_iff_rank`), and the stacked matrix is again an integer matrix.

The rank of an integer matrix over `K` equals its rank over `ℚ` (characteristic zero) or over
`ZMod 3` (characteristic three) (`FieldTransfer.rank_intCast_charZero`, `rank_intCast_charThree`).
So `AnchorTest K p ↔ AnchorTest ℚ p` or `↔ AnchorTest (ZMod 3) p`, and the census transfers.
-/

namespace Brent.Catalogue

open Brent.Census.FieldTransfer

/-! ### Span containment is a rank equality -/

section Span

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rows of `fromRows A B` span the sum of the row spans. -/
theorem span_range_fromRows (A B : Matrix ι (Fin 4) K) :
    Submodule.span K (Set.range (Matrix.fromRows A B).row) =
      Submodule.span K (Set.range A.row) ⊔ Submodule.span K (Set.range B.row) := by
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_union, Sum.exists]
  exact Iff.rfl

/-- **Row-span containment as a rank equality.** -/
theorem span_le_iff_rank (A B : Matrix ι (Fin 4) K) :
    Submodule.span K (Set.range A.row) ≤ Submodule.span K (Set.range B.row) ↔
      (Matrix.fromRows A B).rank = B.rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, span_range_fromRows]
  constructor
  · intro h
    rw [sup_eq_right.mpr h]
  · intro h
    have hle : Submodule.span K (Set.range B.row) ≤
        Submodule.span K (Set.range A.row) ⊔ Submodule.span K (Set.range B.row) := le_sup_right
    have heq := Submodule.eq_of_le_of_finrank_eq hle h.symm
    rw [heq]
    exact le_sup_left

end Span

/-- The integer matrix stacking the rows of `A` above those of `B`. -/
def stack (A B : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4) ℤ :=
  Matrix.fromRows A B

theorem stack_map (K : Type) [Field K] (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    (stack A B).map (Int.cast : ℤ → K) =
      Matrix.fromRows (A.map (Int.cast : ℤ → K)) (B.map (Int.cast : ℤ → K)) := by
  ext i j
  cases i <;> rfl

/-- `rowSpace K A ≤ rowSpace K B` is a rank equality between integer matrices. -/
theorem rowSpace_le_iff_rank (K : Type) [Field K] (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    rowSpace K A ≤ rowSpace K B ↔
      ((stack A B).map (Int.cast : ℤ → K)).rank = (B.map (Int.cast : ℤ → K)).rank := by
  rw [stack_map]
  exact span_le_iff_rank _ _

theorem colSpace_le_iff_rank (K : Type) [Field K] (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    colSpace K A ≤ colSpace K B ↔
      ((stack A.transpose B.transpose).map (Int.cast : ℤ → K)).rank =
        (B.transpose.map (Int.cast : ℤ → K)).rank :=
  rowSpace_le_iff_rank K _ _

/-! ### Transfer between fields

`L` is the reference field (`ℚ` or `ZMod 3`) and `hL` says every integer matrix has the same
rank over `K` as over `L`. -/

section Transfer

variable (K L : Type) [Field K] [Field L]
  (hL : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι (Fin 4) ℤ),
    (M.map (Int.cast : ℤ → K)).rank = (M.map (Int.cast : ℤ → L)).rank)

include hL

theorem rk_transfer (p : Fin 14236) (s : Fin 49) (m : Fin 3) : rk K p s m = rk L p s m :=
  hL (factor p s m)

theorem profile_transfer (p : Fin 14236) : profile K p = profile L p := by
  simp only [profile, rk_transfer K L hL]

theorem rankBounds_transfer (p : Fin 14236) : RankBounds K p ↔ RankBounds L p := by
  simp only [RankBounds, rk_transfer K L hL]

theorem canAnchor_transfer (p : Fin 14236) (t a : Fin 49) :
    CanAnchor K p t a ↔ CanAnchor L p t a := by
  simp only [CanAnchor, rowSpace_le_iff_rank, colSpace_le_iff_rank, hL]

theorem rankOne_transfer (p : Fin 14236) : rankOne K p = rankOne L p := by
  ext s
  simp only [rankOne, Finset.mem_filter, rk_transfer K L hL]

theorem rankTwo_transfer (p : Fin 14236) : rankTwo K p = rankTwo L p := by
  ext s
  simp only [rankTwo, Finset.mem_filter, rk_transfer K L hL]

theorem children_transfer (p : Fin 14236) (a : Fin 49) : children K p a = children L p a := by
  ext t
  simp only [children, Finset.mem_filter, rankOne_transfer K L hL, canAnchor_transfer K L hL]

theorem useful_transfer (p : Fin 14236) (a : Fin 49) : Useful K p a ↔ Useful L p a := by
  simp only [Useful, rankTwo_transfer K L hL, children_transfer K L hL]

theorem anchorTest_transfer (p : Fin 14236) : AnchorTest K p ↔ AnchorTest L p := by
  classical
  unfold AnchorTest
  have hf : (rankTwo K p).filter (Useful K p) = (rankTwo L p).filter (Useful L p) := by
    rw [rankTwo_transfer K L hL]
    ext a
    simp only [Finset.mem_filter, useful_transfer K L hL]
  rw [hf, rankOne_transfer K L hL]
  simp only [useful_transfer K L hL, canAnchor_transfer K L hL]

end Transfer

/-- The rank comparison for a field of characteristic zero (reference `ℚ`). -/
theorem hL_charZero (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin 4) ℤ) :
    (M.map (Int.cast : ℤ → K)).rank = (M.map (Int.cast : ℤ → ℚ)).rank :=
  rank_intCast_charZero K M

/-- The rank comparison for a field of characteristic three (reference `ZMod 3`). -/
theorem hL_charThree (K : Type) [Field K] [CharP K 3] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin 4) ℤ) :
    (M.map (Int.cast : ℤ → K)).rank = (M.map (Int.cast : ℤ → ZMod 3)).rank :=
  rank_intCast_charThree K M

/-! ### The census over every field of characteristic three or zero -/

theorem facts_allFields (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    (∀ p : Fin 14236, profile K p = fullProfile ↔ p.val ∉ bad87) ∧
    (∀ p : Fin 14236, RankBounds K p ↔ p.val ∉ bad87) ∧
    (∀ p : Fin 14236, p.val ∉ bad87 → p.val ∉ neg2 → AnchorTest K p) ∧
    (∀ p : Fin 14236, p.val ∈ neg2 → ¬ AnchorTest K p) := by
  rcases hK with hK | hK
  · have h := @hL_charThree K _ hK
    refine ⟨fun p => ?_, fun p => ?_, fun p hb hn => ?_, fun p hn => ?_⟩
    · rw [profile_transfer K (ZMod 3) h]; exact fullF p
    · rw [rankBounds_transfer K (ZMod 3) h]; exact rbF p
    · rw [anchorTest_transfer K (ZMod 3) h]; exact ancF p hb hn
    · rw [anchorTest_transfer K (ZMod 3) h]; exact negF p hn
  · have h := @hL_charZero K _ hK
    refine ⟨fun p => ?_, fun p => ?_, fun p hb hn => ?_, fun p hn => ?_⟩
    · rw [profile_transfer K ℚ h]; exact fullQ p
    · rw [rankBounds_transfer K ℚ h]; exact rbQ p
    · rw [anchorTest_transfer K ℚ h]; exact ancQ p hb hn
    · rw [anchorTest_transfer K ℚ h]; exact negQ p hn

namespace AllFields

variable (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K)

include hK

/-- Paper line 697: exactly 14,149 points have the full profile. -/
theorem card_fullProfile :
    (Finset.univ.filter fun p => profile K p = fullProfile).card = 14149 :=
  let h := facts_allFields K hK
  (census K h.1 h.2.1 h.2.2.1 h.2.2.2).1

/-- Paper lines 698–699: these are precisely the points satisfying the two rank bounds. -/
theorem fullProfile_iff_rankBounds : ∀ p, profile K p = fullProfile ↔ RankBounds K p :=
  let h := facts_allFields K hK
  (census K h.1 h.2.1 h.2.2.1 h.2.2.2).2.1

open Classical in
/-- Paper line 699: the rank bounds exclude 87 entries. -/
theorem card_not_rankBounds : (Finset.univ.filter fun p => ¬ RankBounds K p).card = 87 :=
  let h := facts_allFields K hK
  (census K h.1 h.2.1 h.2.2.1 h.2.2.2).2.2.1

open Classical in
/-- Paper lines 700–702: the row- and column-space test excludes exactly 2445 and 5969. -/
theorem anchor_excluded :
    (Finset.univ.filter fun p => profile K p = fullProfile ∧ ¬ AnchorTest K p) = {2445, 5969} :=
  let h := facts_allFields K hK
  (census K h.1 h.2.1 h.2.2.1 h.2.2.2).2.2.2

/-- Paper lines 704–705: "all 14,147 points that pass both tests have the full profile". -/
theorem card_pass_both :
    (Finset.univ.filter fun p => RankBounds K p ∧ AnchorTest K p).card = 14147 := by
  classical
  have h1 := card_fullProfile K hK
  have h2 := anchor_excluded K hK
  have hsplit : (Finset.univ.filter fun p => profile K p = fullProfile) =
      (Finset.univ.filter fun p => RankBounds K p ∧ AnchorTest K p) ∪
        (Finset.univ.filter fun p => profile K p = fullProfile ∧ ¬ AnchorTest K p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      fullProfile_iff_rankBounds K hK p]
    tauto
  have hdisj : Disjoint (Finset.univ.filter fun p => RankBounds K p ∧ AnchorTest K p)
      (Finset.univ.filter fun p => profile K p = fullProfile ∧ ¬ AnchorTest K p) := by
    rw [Finset.disjoint_filter]
    intro p _ h h'
    exact h'.2 h.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, h2] at h1
  simp at h1
  omega

end AllFields

end Brent.Catalogue
