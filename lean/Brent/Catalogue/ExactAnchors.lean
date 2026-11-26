import Brent.Catalogue.AllFields

/-! Exact useful-anchor counts, rather than just failure of the anchor test.
The positive certificate checks actual factor entries and the rank/pivot certificates;
the upper certificate counts pairs not excluded by the existing negative witnesses.
No reported list of compatible pairs is taken as a mathematical hypothesis. -/
namespace Brent.Catalogue

open Classical in
noncomputable def usefulAnchors (K : Type) [Field K] (p : Fin 14236) : Finset (Fin 49) :=
  (rankTwo K p).filter (Useful K p)

def possible (f : Bool) (p a : Nat) (ws : List Wit) : Bool :=
  triple f (certNat p) a 2 &&
    Nat.ble 6 (cnt 49 fun t => triple f (certNat p) t 1 && !hasWit ws t a)

/-- Every useful anchor survives the negative certificate. -/
theorem useful_card_le_possible (K : Type) [Field K] (q : Nat) [CharP K q] (f : Bool)
    (p : Fin 14236) (ws : List Wit)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f (certNat p.val) s.val m.val)
    (hws : ∀ w ∈ ws, witOK q (pointNat p.val) w = true) :
    (usefulAnchors K p).card ≤ cnt 49 (fun a => possible f p.val a ws) := by
  classical
  rw [cnt_eq]
  apply Finset.card_le_card
  intro a ha
  simp only [usefulAnchors, Finset.mem_filter, Useful] at ha
  obtain ⟨ha2, -, hch⟩ := ha
  simp only [possible, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
    Nat.ble_eq]
  refine ⟨(forall_mode_iff K p f _ hrk a 2).1 (by simpa [rankTwo] using ha2), ?_⟩
  rw [cnt_eq]
  refine le_trans hch (Finset.card_le_card ?_)
  intro t ht
  simp only [children, Finset.mem_filter] at ht
  obtain ⟨ht1, hcan⟩ := ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
    Bool.not_eq_true']
  refine ⟨(forall_mode_iff K p f _ hrk t 1).1 (by simpa [rankOne] using ht1), ?_⟩
  by_contra hw
  simp only [Bool.not_eq_false, hasWit, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨w, hw, hwt, hwa⟩ := hw
  exact not_canAnchor_of_wit K q p w (hws w hw) t a hwt.symm hwa.symm hcan

/-- The positive check uses the rational pivot code only if that code also passes in the
requested characteristic. `compat` checks integral identities, which then hold in the field. -/
def positiveRank (q p s r : Nat) : Bool :=
  triple false (certNat p) s r &&
    allBelow 3 (fun m => chkCode q (mat (pointNat p) s m) (code (certNat p) s m))

def positiveChild (q p t a : Nat) : Bool :=
  positiveRank q p t 1 && compat (pointNat p) (certNat p) t a

def positiveUseful (q p a : Nat) : Bool :=
  positiveRank q p a 2 && Nat.ble 6 (cnt 49 fun t => positiveChild q p t a)

theorem positiveRank_sound (K : Type) [Field K] (q : Nat) [CharP K q]
    (p : Fin 14236) (s : Fin 49) (r : Nat) (h : positiveRank q p.val s.val r = true) :
    (∀ m : Fin 3, rk K p s m = r) ∧
    (∀ m : Fin 3, chkCode q (mat (pointNat p.val) s.val m.val)
      (code (certNat p.val) s.val m.val) = true) ∧
    (∀ m : Fin 3, cR (code (certNat p.val) s.val m.val) = r) := by
  simp only [positiveRank, Bool.and_eq_true] at h
  have hc : ∀ m : Fin 3, chkCode q (mat (pointNat p.val) s.val m.val)
      (code (certNat p.val) s.val m.val) = true :=
    fun m => (allBelow_iff _ _).1 h.2 m.val m.isLt
  have hr : ∀ m : Fin 3, cR (code (certNat p.val) s.val m.val) = r := by
    intro m
    have h' := (triple_iff _ _ _ _).1 h.1
    simp only [Prod.mk.injEq, rkC_false] at h'
    fin_cases m
    · exact h'.1
    · exact h'.2.1
    · exact h'.2
  refine ⟨fun m => ?_, hc, hr⟩
  rw [rk, factor_map, chkCode_sound q _ _ (hc m), hr m]

theorem positiveUseful_sound (K : Type) [Field K] (q : Nat) [CharP K q]
    (p : Fin 14236) (a : Fin 49) (h : positiveUseful q p.val a.val = true) :
    a ∈ usefulAnchors K p := by
  classical
  simp only [positiveUseful, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨ha, hcnt⟩ := h
  obtain ⟨hra, hca, hcodea⟩ := positiveRank_sound K q p a 2 ha
  have ha2 : a ∈ rankTwo K p := by simpa [rankTwo] using hra
  change a ∈ (rankTwo K p).filter (Useful K p)
  apply Finset.mem_filter.mpr
  refine ⟨ha2, ha2, ?_⟩
  rw [cnt_eq] at hcnt
  refine hcnt.trans (Finset.card_le_card ?_)
  intro t ht
  simp only [positiveChild, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at ht
  obtain ⟨hrt, hct, hcodet⟩ := positiveRank_sound K q p t 1 ht.1
  exact Finset.mem_filter.mpr ⟨by simpa [rankOne] using hrt,
    canAnchor_of_compat K q p t a (fun m => ⟨hct m, hca m⟩) hcodet hcodea ht.2⟩

/-- Two-sided finite certificate: the proposed anchors all pass, and the number of possible
anchors is no greater than the size of the proposed set. -/
theorem exact_usefulAnchors (K : Type) [Field K] (q : Nat) [CharP K q] (f : Bool)
    (p : Fin 14236) (ws : List Wit) (S : Finset (Fin 49))
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f (certNat p.val) s.val m.val)
    (hws : ws.all (witOK q (pointNat p.val)) = true)
    (hpos : ∀ a ∈ S, positiveUseful q p.val a.val = true)
    (hupper : cnt 49 (fun a => possible f p.val a ws) ≤ S.card) :
    usefulAnchors K p = S := by
  classical
  have hsub : S ⊆ usefulAnchors K p := fun a ha => positiveUseful_sound K q p a (hpos a ha)
  have hle := (useful_card_le_possible K q f p ws hrk (List.all_eq_true.mp hws)).trans hupper
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

-- These four direct certificate checks intentionally reference the generated catalogue,
-- rather than trusting REPORT.md or the JSON list of useful anchors.
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem usefulAnchors_2445_Q : usefulAnchors ℚ 2445 = {1, 25} := by
  apply exact_usefulAnchors ℚ 0 false 2445 w2445_Q _ (rkQ 2445)
  · exact (Bool.and_eq_true.mp neg2445_Q).1
  · decide +kernel
  · decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem usefulAnchors_5969_Q : usefulAnchors ℚ 5969 = {3} := by
  apply exact_usefulAnchors ℚ 0 false 5969 w5969_Q _ (rkQ 5969)
  · exact (Bool.and_eq_true.mp neg5969_Q).1
  · decide +kernel
  · decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem usefulAnchors_2445_F : usefulAnchors (ZMod 3) 2445 = {1, 25} := by
  apply exact_usefulAnchors (ZMod 3) 3 true 2445 w2445_F _ (rkF 2445)
  · exact (Bool.and_eq_true.mp neg2445_F).1
  · decide +kernel
  · decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem usefulAnchors_5969_F : usefulAnchors (ZMod 3) 5969 = {3} := by
  apply exact_usefulAnchors (ZMod 3) 3 true 5969 w5969_F _ (rkF 5969)
  · exact (Bool.and_eq_true.mp neg5969_F).1
  · decide +kernel
  · decide +kernel

theorem usefulAnchors_transfer (K L : Type) [Field K] [Field L]
    (hL : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι (Fin 4) ℤ),
      (M.map (Int.cast : ℤ → K)).rank = (M.map (Int.cast : ℤ → L)).rank)
    (p : Fin 14236) : usefulAnchors K p = usefulAnchors L p := by
  classical
  ext a
  simp only [usefulAnchors, Finset.mem_filter, rankTwo_transfer K L hL,
    useful_transfer K L hL]

theorem usefulAnchors_2445 (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    usefulAnchors K 2445 = {1, 25} := by
  rcases hK with h | h
  · rw [usefulAnchors_transfer K (ZMod 3) (@hL_charThree K _ h)]
    exact usefulAnchors_2445_F
  · rw [usefulAnchors_transfer K ℚ (@hL_charZero K _ h)]
    exact usefulAnchors_2445_Q

theorem usefulAnchors_5969 (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    usefulAnchors K 5969 = {3} := by
  rcases hK with h | h
  · rw [usefulAnchors_transfer K (ZMod 3) (@hL_charThree K _ h)]
    exact usefulAnchors_5969_F
  · rw [usefulAnchors_transfer K ℚ (@hL_charZero K _ h)]
    exact usefulAnchors_5969_Q

theorem usefulAnchors_count_2445 (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    (usefulAnchors K 2445).card = 2 := by
  rw [usefulAnchors_2445 K hK]
  decide

theorem usefulAnchors_count_5969 (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    (usefulAnchors K 5969).card = 1 := by
  rw [usefulAnchors_5969 K hK]
  decide

end Brent.Catalogue
