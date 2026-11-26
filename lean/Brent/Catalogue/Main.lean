import Brent.Catalogue.Checks
import Brent.Catalogue.Neg

/-!
# The AlphaTensor catalogue census (paper §7, lines 660–705)

The four statements of `TASKS.md`, for `K = ℚ` (namespace `Brent.Catalogue.Q`) and for
`K = ZMod 3` (namespace `Brent.Catalogue.F3`). They follow from
* `all_points` (every point passes the kernel check `pointOK`, `Brent.Catalogue.Check.K###`),
* `facts_of_pointOK` (what a passing check means, `Brent.Catalogue.Census`),
* `neg2445_Q`, …, `not_anchorTest_of_negOK` (the two anchor-test failures).
-/

namespace Brent.Catalogue

theorem pointOK_all (p : Fin 14236) : pointOK p.val = true := by
  simpa using (rangeOK_spec 0 14236).1 all_points p.val p.isLt

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_bad : (Finset.univ.filter fun p : Fin 14236 => p.val ∈ bad87).card = 87 := by
  decide +kernel

theorem neg2_not_bad : 2445 ∉ bad87 ∧ 5969 ∉ bad87 := by decide

theorem mem_neg2 (p : Fin 14236) : p.val ∈ neg2 ↔ p = 2445 ∨ p = 5969 := by
  simp only [neg2, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  rfl

/-- The counting argument, given the per-point facts. -/
theorem census (K : Type) [Field K]
    (hfull : ∀ p : Fin 14236, profile K p = fullProfile ↔ p.val ∉ bad87)
    (hrb : ∀ p : Fin 14236, RankBounds K p ↔ p.val ∉ bad87)
    (hanc : ∀ p : Fin 14236, p.val ∉ bad87 → p.val ∉ neg2 → AnchorTest K p)
    (hneg : ∀ p : Fin 14236, p.val ∈ neg2 → ¬ AnchorTest K p) :
    (Finset.univ.filter fun p => profile K p = fullProfile).card = 14149 ∧
    (∀ p, profile K p = fullProfile ↔ RankBounds K p) ∧
    (open Classical in (Finset.univ.filter fun p => ¬ RankBounds K p).card = 87) ∧
    (open Classical in (Finset.univ.filter fun p => profile K p = fullProfile ∧ ¬ AnchorTest K p)
      = {2445, 5969}) := by
  classical
  have hnot : (Finset.univ.filter fun p : Fin 14236 => p.val ∉ bad87).card = 14149 := by
    rw [Finset.filter_not, Finset.card_sdiff (Finset.filter_subset _ _), card_bad,
      Finset.card_univ, Fintype.card_fin]
  refine ⟨?_, fun p => by rw [hfull, hrb], ?_, ?_⟩
  · rw [← hnot]; congr 1; ext p; simp [hfull]
  · rw [← card_bad]; congr 1; ext p; simp [hrb]
  · ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfull, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hb, hA⟩
      by_contra hn
      exact hA (hanc p hb (fun h => hn ((mem_neg2 p).1 h)))
    · intro hp
      have hn : p.val ∈ neg2 := (mem_neg2 p).2 hp
      refine ⟨?_, hneg p hn⟩
      rcases hp with rfl | rfl
      · exact neg2_not_bad.1
      · exact neg2_not_bad.2

theorem rkQ (p : Fin 14236) (s : Fin 49) (m : Fin 3) :
    rk ℚ p s m = rkC false (certNat p.val) s.val m.val := by
  have h := pointOK_all p
  simp only [pointOK, Bool.and_eq_true] at h
  exact (rk_eq_of_matOK p s m (matOK_of_ranksOK h.1.1.1.1.1 s.val s.isLt m.val m.isLt)).1

theorem rkF (p : Fin 14236) (s : Fin 49) (m : Fin 3) :
    rk (ZMod 3) p s m = rkC true (certNat p.val) s.val m.val := by
  have h := pointOK_all p
  simp only [pointOK, Bool.and_eq_true] at h
  exact (rk_eq_of_matOK p s m (matOK_of_ranksOK h.1.1.1.1.1 s.val s.isLt m.val m.isLt)).2

theorem negQ (p : Fin 14236) (hp : p.val ∈ neg2) : ¬ AnchorTest ℚ p := by
  rcases (mem_neg2 p).1 hp with rfl | rfl
  · exact not_anchorTest_of_negOK ℚ 0 false 2445 w2445_Q (rkQ 2445) neg2445_Q
  · exact not_anchorTest_of_negOK ℚ 0 false 5969 w5969_Q (rkQ 5969) neg5969_Q

theorem negF (p : Fin 14236) (hp : p.val ∈ neg2) : ¬ AnchorTest (ZMod 3) p := by
  rcases (mem_neg2 p).1 hp with rfl | rfl
  · exact not_anchorTest_of_negOK (ZMod 3) 3 true 2445 w2445_F (rkF 2445) neg2445_F
  · exact not_anchorTest_of_negOK (ZMod 3) 3 true 5969 w5969_F (rkF 5969) neg5969_F

theorem fullQ (p : Fin 14236) : profile ℚ p = fullProfile ↔ p.val ∉ bad87 :=
  (facts_of_pointOK p (pointOK_all p)).2.1
theorem rbQ (p : Fin 14236) : RankBounds ℚ p ↔ p.val ∉ bad87 :=
  (facts_of_pointOK p (pointOK_all p)).2.2.1
theorem ancQ (p : Fin 14236) (hb : p.val ∉ bad87) (hn : p.val ∉ neg2) : AnchorTest ℚ p :=
  ((facts_of_pointOK p (pointOK_all p)).2.2.2.2.2 hb hn).1
theorem fullF (p : Fin 14236) : profile (ZMod 3) p = fullProfile ↔ p.val ∉ bad87 :=
  (facts_of_pointOK p (pointOK_all p)).2.2.2.1
theorem rbF (p : Fin 14236) : RankBounds (ZMod 3) p ↔ p.val ∉ bad87 :=
  (facts_of_pointOK p (pointOK_all p)).2.2.2.2.1
theorem ancF (p : Fin 14236) (hb : p.val ∉ bad87) (hn : p.val ∉ neg2) : AnchorTest (ZMod 3) p :=
  ((facts_of_pointOK p (pointOK_all p)).2.2.2.2.2 hb hn).2
end Brent.Catalogue

/-! ### The statements of `TASKS.md`, over `ℚ` -/

namespace Brent.Catalogue.Q

open Brent.Catalogue

theorem card_fullProfile :
    (Finset.univ.filter fun p => profile ℚ p = fullProfile).card = 14149 := (census ℚ fullQ rbQ ancQ negQ).1

theorem fullProfile_iff_rankBounds : ∀ p, profile ℚ p = fullProfile ↔ RankBounds ℚ p :=
  (census ℚ fullQ rbQ ancQ negQ).2.1

open Classical in
theorem card_not_rankBounds : (Finset.univ.filter fun p => ¬ RankBounds ℚ p).card = 87 :=
  (census ℚ fullQ rbQ ancQ negQ).2.2.1

open Classical in
theorem anchor_excluded :
    (Finset.univ.filter fun p => profile ℚ p = fullProfile ∧ ¬ AnchorTest ℚ p) = {2445, 5969} :=
  (census ℚ fullQ rbQ ancQ negQ).2.2.2

end Brent.Catalogue.Q

/-! ### The statements of `TASKS.md`, over `ZMod 3` -/

namespace Brent.Catalogue.F3

open Brent.Catalogue

theorem card_fullProfile :
    (Finset.univ.filter fun p => profile (ZMod 3) p = fullProfile).card = 14149 := (census (ZMod 3) fullF rbF ancF negF).1

theorem fullProfile_iff_rankBounds :
    ∀ p, profile (ZMod 3) p = fullProfile ↔ RankBounds (ZMod 3) p := (census (ZMod 3) fullF rbF ancF negF).2.1

open Classical in
theorem card_not_rankBounds :
    (Finset.univ.filter fun p => ¬ RankBounds (ZMod 3) p).card = 87 := (census (ZMod 3) fullF rbF ancF negF).2.2.1

open Classical in
theorem anchor_excluded :
    (Finset.univ.filter fun p => profile (ZMod 3) p = fullProfile ∧ ¬ AnchorTest (ZMod 3) p) =
      {2445, 5969} := (census (ZMod 3) fullF rbF ancF negF).2.2.2

end Brent.Catalogue.F3

#print axioms Brent.Catalogue.Q.card_fullProfile
#print axioms Brent.Catalogue.Q.fullProfile_iff_rankBounds
#print axioms Brent.Catalogue.Q.card_not_rankBounds
#print axioms Brent.Catalogue.Q.anchor_excluded
#print axioms Brent.Catalogue.F3.card_fullProfile
#print axioms Brent.Catalogue.F3.fullProfile_iff_rankBounds
#print axioms Brent.Catalogue.F3.card_not_rankBounds
#print axioms Brent.Catalogue.F3.anchor_excluded
