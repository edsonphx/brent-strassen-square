import Brent.Census.CatalogueLink
import Brent.Census.Exclusion

/-!
# §7: the rank-bound exclusion as geometry (F18c)

DRAFT, NOT YET COMPILED.

Paper, lines 659–674: "Consequently, even allowing summand and mode permutations, at most 13
summands can have any mode rank above one, and at most one summand can have any mode rank above
two." and lines 698–699: the rank bounds "exclude 87 entries".

`RankBound k` (in `Census.RankBound`) is the zero locus of products of minors and contains the
closure of the saturated union of the two families (`closure_saturation_subset_rankBound`). Here:
a catalogue entry that fails the census rank bounds (`Catalogue.RankBounds`) is not in
`RankBound k` (`catPoint_not_mem_rankBound`): fourteen summands with a mode of rank `≥ 2` give
fourteen nonzero `2 × 2` minors (`Minors.exists_minor_ne_zero`) whose product is a nonvanishing
obstruction polynomial, and two summands with a mode of rank `≥ 3` give two nonzero `3 × 3`
minors. Hence it lies outside the closure of the saturated families, and outside both family
closures.
-/

open MvPolynomial
open scoped BigOperators

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure Brent.Catalogue

variable {k : Type} [Field k]

theorem exists_minor_catPoint (p : Fin 14236) (n : Fin 49) (r : ℕ)
    (h : ∃ mi, r < rk k p n mi) :
    ∃ c : MinorChoice (r + 1),
      ((modeMat (catPoint k p) (sE.symm n) c.1).submatrix c.2.1 c.2.2).det ≠ 0 := by
  obtain ⟨mi, hmi⟩ := h
  have hr : r + 1 ≤ (modeMat (catPoint k p) (sE.symm n) (mE.symm mi)).rank := by
    rw [rank_modeMat_catPoint]
    simpa using hmi
  obtain ⟨f, g, hfg⟩ := Minors.exists_minor_ne_zero _ hr
  exact ⟨(mE.symm mi, f, g), hfg⟩

/-- **A catalogue entry failing the rank bounds is outside the closed set `RankBound k`.** -/
theorem catPoint_not_mem_rankBound (p : Fin 14236) (hp : ¬ RankBounds k p) :
    catPoint k p ∉ RankBound k := by
  classical
  intro hv
  have hv' : ∀ f ∈ boundPolys (k := k), eval (catPoint k p) f = 0 := hv
  rw [RankBounds, not_and_or] at hp
  rcases hp with h1 | h2
  · set S := Finset.univ.filter fun n : Fin 49 => ∃ mi, 1 < rk k p n mi
    have hS : 14 ≤ S.card := by omega
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
    let e := T.orderEmbOfFin hT
    have hmem : ∀ i, e i ∈ S := fun i => hTS (T.orderEmbOfFin_mem hT i)
    have hc : ∀ i : Fin 14, ∃ c : MinorChoice 2,
        ((modeMat (catPoint k p) (sE.symm (e i)) c.1).submatrix c.2.1 c.2.2).det ≠ 0 :=
      fun i => exists_minor_catPoint p (e i) 1 (Finset.mem_filter.mp (hmem i)).2
    choose c hc using hc
    have h0 := hv' (∏ i, minorPoly (sE.symm (e i)) (c i))
      (Or.inl ⟨fun i => sE.symm (e i), c, sE.symm.injective.comp e.injective, rfl⟩)
    rw [map_prod] at h0
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => by rw [eval_minorPoly]; exact hc i) h0
  · set S := Finset.univ.filter fun n : Fin 49 => ∃ mi, 2 < rk k p n mi
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    obtain ⟨c, hc⟩ := exists_minor_catPoint p a 2 (Finset.mem_filter.mp ha).2
    obtain ⟨c', hc'⟩ := exists_minor_catPoint p b 2 (Finset.mem_filter.mp hb).2
    have h0 := hv' (minorPoly (sE.symm a) c * minorPoly (sE.symm b) c')
      (Or.inr ⟨_, _, c, c', fun h => hab (sE.symm.injective h), rfl⟩)
    rw [map_mul, eval_minorPoly, eval_minorPoly] at h0
    exact mul_ne_zero hc hc' h0

/-- **F18c.** A catalogue entry failing the rank bounds lies outside the closure of the
saturated families (closed under every equivalence, `dominated_of_formula`). -/
theorem catPoint_not_mem_saturated (p : Fin 14236) (hp : ¬ RankBounds k p) :
    catPoint k p ∉ closure (saturation (imageA k true) ∪ saturation (imageA k false)) :=
  fun h => catPoint_not_mem_rankBound p hp (closure_saturation_subset_rankBound h)

/-- Hence outside both family closures. -/
theorem catPoint_not_mem_familyClosure_of_rankBounds (p : Fin 14236) (hp : ¬ RankBounds k p)
    (left : Bool) : catPoint k p ∉ familyClosure k left :=
  fun h => catPoint_not_mem_saturated p hp (familyClosure_subset_saturated left h)

/-- **The 87 rank-bound exclusions**, over every field of characteristic three or zero: exactly
87 catalogue entries fail the rank bounds, and each lies outside the closure of the saturated
families. -/
theorem rank_bound_exclusions (hk : CharP k 3 ∨ CharZero k) :
    (Finset.univ.filter fun p : Fin 14236 => ¬ RankBounds k p).card = 87 ∧
      ∀ p : Fin 14236, ¬ RankBounds k p →
        catPoint k p ∉ closure (saturation (imageA k true) ∪ saturation (imageA k false)) := by
  classical
  exact ⟨by convert AllFields.card_not_rankBounds k hk, catPoint_not_mem_saturated⟩

end Brent.Census
