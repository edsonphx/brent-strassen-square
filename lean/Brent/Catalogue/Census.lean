import Brent.Catalogue.Anchor

/-!
# From a passing `pointOK` to the census facts at that point

For a catalogue point `p` with `pointOK p = true` and `K ∈ {ℚ, ZMod 3}`:
* `profile K p = fullProfile ↔ p ∉ bad87` and `RankBounds K p ↔ p ∉ bad87`;
* if `p ∉ bad87` and `p ∉ neg2`, then `AnchorTest K p`.
-/

namespace Brent.Catalogue

theorem rkC_false (C s m : ℕ) : rkC false C s m = cR (code C s m) := by simp [rkC]

theorem forall_mode_iff (K : Type) [Field K] (p : Fin 14236) (f : Bool) (C : ℕ)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC f C s.val m.val) (s : Fin 49)
    (r : ℕ) : (∀ m, rk K p s m = r) ↔ triple f C s.val r = true := by
  rw [triple_iff]
  simp only [hrk, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ m; fin_cases m <;> assumption

/-- The anchor certificate gives the anchor test, over any field of characteristic `q` in which
all rank certificates of the point pass and whose ranks are the `ℚ`-certified ones. -/
theorem anchorTest_of_anchorOK (K : Type) [Field K] (q : ℕ) [CharP K q] (p : Fin 14236)
    (hchk : ∀ (s : Fin 49) (m : Fin 3),
      chkCode q (mat (pointNat p.val) s.val m.val) (code (certNat p.val) s.val m.val) = true)
    (hrk : ∀ (s : Fin 49) (m : Fin 3), rk K p s m = rkC false (certNat p.val) s.val m.val)
    (h : anchorOK (pointNat p.val) (certNat p.val) = true) : AnchorTest K p := by
  classical
  set N := pointNat p.val
  set C := certNat p.val
  simp only [anchorOK, Bool.and_eq_true] at h
  obtain ⟨⟨-, hg⟩, ht⟩ := h
  rw [allBelow_iff] at hg ht
  -- the six anchors
  have hgs : ∀ g : Fin 6, Nat.blt (anc C g) 49 = true ∧ triple false C (anc C g) 2 = true ∧
      allBelow g (fun h => !(anc C h == anc C g)) = true ∧
      Nat.ble 6 (cnt 49 fun t => triple false C t 1 && grp C t == g) = true := by
    intro g
    have := hg g.val g.isLt
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  let a : Fin 6 → Fin 49 := fun g => ⟨anc C g, Nat.blt_eq.mp (hgs g).1⟩
  have mem1 : ∀ t : Fin 49, t ∈ rankOne K p ↔ triple false C t.val 1 = true := by
    intro t; simp only [rankOne, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_mode_iff K p false C hrk t 1
  have mem2 : ∀ t : Fin 49, t ∈ rankTwo K p ↔ triple false C t.val 2 = true := by
    intro t; simp only [rankTwo, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_mode_iff K p false C hrk t 2
  have hcR : ∀ (s : Fin 49) (r : ℕ), triple false C s.val r = true →
      ∀ m : Fin 3, cR (code C s.val m.val) = r := by
    intro s r hs m
    have := (forall_mode_iff K p false C hrk s r).2 hs m
    rw [hrk, rkC_false] at this; exact this
  -- compatible pairs give `CanAnchor`
  have hcan : ∀ t a' : Fin 49, triple false C t.val 1 = true → triple false C a'.val 2 = true →
      compat N C t.val a'.val = true → CanAnchor K p t a' :=
    fun t a' h1 h2 hc => canAnchor_of_compat K q p t a' (fun m => ⟨hchk t m, hchk a' m⟩)
      (hcR t 1 h1) (hcR a' 2 h2) hc
  have hassign : ∀ t : Fin 49, triple false C t.val 1 = true →
      ∃ g : Fin 6, grp C t.val = g.val ∧ CanAnchor K p t (a g) := by
    intro t h1
    have := ht t.val t.isLt
    simp only [h1, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq] at this
    refine ⟨⟨grp C t.val, this.1⟩, rfl, hcan t _ h1 (hgs _).2.1 this.2⟩
  -- each anchor is useful
  have huseful : ∀ g : Fin 6, Useful K p (a g) := by
    intro g
    refine ⟨(mem2 _).2 (hgs g).2.1, ?_⟩
    have hcnt := Nat.ble_eq.mp (hgs g).2.2.2
    rw [cnt_eq] at hcnt
    refine le_trans hcnt (Finset.card_le_card ?_)
    intro t ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      beq_iff_eq] at ht'
    obtain ⟨h1, hgt⟩ := ht'
    simp only [children, Finset.mem_filter]
    refine ⟨(mem1 t).2 h1, ?_⟩
    obtain ⟨g', hg', hcan'⟩ := hassign t h1
    have : g' = g := Fin.ext (by rw [← hg', hgt])
    exact this ▸ hcan'
  -- the anchors are distinct
  have hinj : Function.Injective a := by
    intro g1 g2 heq
    have heq' : anc C g1 = anc C g2 := congrArg Fin.val heq
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := (allBelow_iff _ _).1 (hgs g2).2.2.1 g1 hlt
      simp [heq'] at this
    · have := (allBelow_iff _ _).1 (hgs g1).2.2.1 g2 hlt
      simp [heq'] at this
  refine ⟨?_, ?_⟩
  · calc 6 = (Finset.univ.image a).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ _ := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_filter.mpr ⟨(huseful g).1, huseful g⟩
  · intro t ht1
    obtain ⟨g, -, hc⟩ := hassign t ((mem1 t).1 ht1)
    exact ⟨a g, huseful g, hc⟩

/-! ### The per-point facts -/

theorem sameAll_rk (C : ℕ) (h : sameAll C = true) (s : ℕ) (hs : s < 49) (m : ℕ) (hm : m < 3) :
    rkC true C s m = rkC false C s m := by
  have := (allBelow_iff 49 _).1 h s hs
  simp only [Bool.and_eq_true] at this
  have hsame : cSame (code C s m) = true := by
    interval_cases m
    · exact this.1.1
    · exact this.1.2
    · exact this.2
  simp only [rkC, codeF, hsame, if_true]
  exact (code_low _).1

theorem chk3_of_matOK (N C s m : ℕ) (h : matOK N C s m = true) (hs : cSame (code C s m) = true) :
    chkCode 3 (mat N s m) (code C s m) = true := by
  simp only [matOK, Bool.and_eq_true, hs, if_true, Bool.not_eq_true'] at h
  exact certChk_of_exact 3 _ _ _ _ _ _ _ _ h.1 h.2

/-- Everything a passing `pointOK` gives at one point, for `K = ℚ` and `K = ZMod 3`. -/
theorem facts_of_pointOK (p : Fin 14236) (h : pointOK p.val = true) :
    (∀ K : Type, ∀ [Field K], (K = ℚ ∨ K = ZMod 3) → True) ∧
    (profile ℚ p = fullProfile ↔ p.val ∉ bad87) ∧ (RankBounds ℚ p ↔ p.val ∉ bad87) ∧
    (profile (ZMod 3) p = fullProfile ↔ p.val ∉ bad87) ∧
    (RankBounds (ZMod 3) p ↔ p.val ∉ bad87) ∧
    (p.val ∉ bad87 → p.val ∉ neg2 → AnchorTest ℚ p ∧ AnchorTest (ZMod 3) p) := by
  simp only [pointOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hr, hfQ⟩, hbQ⟩, hfF⟩, hbF⟩, han⟩ := h
  set N := pointNat p.val
  set C := certNat p.val
  have hmat : ∀ (s : Fin 49) (m : Fin 3), matOK N C s.val m.val = true :=
    fun s m => matOK_of_ranksOK hr s.val s.isLt m.val m.isLt
  have hQ : ∀ (s : Fin 49) (m : Fin 3), rk ℚ p s m = rkC false C s.val m.val :=
    fun s m => (rk_eq_of_matOK p s m (hmat s m)).1
  have hF : ∀ (s : Fin 49) (m : Fin 3), rk (ZMod 3) p s m = rkC true C s.val m.val :=
    fun s m => (rk_eq_of_matOK p s m (hmat s m)).2
  have hbad : (bad87.contains p.val = true) ↔ p.val ∈ bad87 := by simp
  refine ⟨fun _ _ _ => trivial, ?_, ?_, ?_, ?_, ?_⟩
  · rw [profile_eq_full_iff ℚ p false C hQ, hfQ]; simp
  · rw [rankBounds_iff ℚ p false C hQ, hbQ]; simp
  · rw [profile_eq_full_iff (ZMod 3) p true C hF, hfF]; simp
  · rw [rankBounds_iff (ZMod 3) p true C hF, hbF]; simp
  · intro hb hn
    have hb' : bad87.contains p.val = false := by simpa using hb
    have hn' : neg2.contains p.val = false := by simpa using hn
    simp only [hb', hn', Bool.false_eq_true, false_or] at han
    have hsame : sameAll C = true := by
      simp only [anchorOK, Bool.and_eq_true] at han; exact han.1.1
    have hsameS : ∀ (s : Fin 49) (m : Fin 3), cSame (code C s.val m.val) = true := by
      intro s m
      have := (allBelow_iff 49 _).1 hsame s.val s.isLt
      simp only [Bool.and_eq_true] at this
      fin_cases m
      · exact this.1.1
      · exact this.1.2
      · exact this.2
    refine ⟨anchorTest_of_anchorOK ℚ 0 p (fun s m => ?_) hQ han,
      anchorTest_of_anchorOK (ZMod 3) 3 p (fun s m => chk3_of_matOK N C _ _ (hmat s m)
        (hsameS s m)) (fun s m => by rw [hF, sameAll_rk C hsame _ s.isLt _ m.isLt]) han⟩
    have := hmat s m
    simp only [matOK, Bool.and_eq_true] at this
    exact this.1

end Brent.Catalogue
