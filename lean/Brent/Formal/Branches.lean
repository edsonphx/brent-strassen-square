import Brent.Formal.FormalDimension
import Brent.Formal.PowerSeriesDimension

/-!
# The two formal branches

Composing the coordinate change `Φ` with restriction to the left variables `(c, x)` or the
right variables `(c, y)` gives surjections `Â → k⟦c, x⟧` and `Â → k⟦c, y⟧`. Their kernels
`𝔭_L` and `𝔭_R` are primes with `Â ⧸ 𝔭_L ≃ k⟦c, x⟧` and `Â ⧸ 𝔭_R ≃ k⟦c, y⟧`, both of
dimension 197. Since `dim Â ≤ 197`, both are minimal primes. They are distinct, and
`Â ⧸ (𝔭_L + 𝔭_R) ≃ k⟦c⟧` has dimension 143.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries TangentData IsLocalRing

set_option linter.unusedSectionVars false

/-- The kernel of a map out of a quotient. -/
theorem ker_quotient_lift {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : ∀ a ∈ I, f a = 0) :
    RingHom.ker (Ideal.Quotient.lift I f H) = Ideal.map (Ideal.Quotient.mk I) (RingHom.ker f) := by
  rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (RingHom.ker (Ideal.Quotient.lift I f H)), RingHom.comap_ker, Ideal.Quotient.lift_comp_mk]

variable (k : Type) [Field k]

theorem card_inChart (left : Bool) : Fintype.card {i : Fin 251 // InChart i left} = 197 := by
  cases left <;> (rw [Fintype.card_subtype]; decide +kernel)

/-- Branch coordinates are the chart's frame directions. -/
def branchEquiv (left : Bool) : BranchVar k left ≃ {i : Fin 251 // InChart i left} where
  toFun w := match w with
    | ⟨Sum.inl i, h⟩ => ⟨i, h⟩
    | ⟨Sum.inr _, h⟩ => False.elim h
  invFun i := ⟨Sum.inl i.1, i.2⟩
  left_inv w := by
    rcases w with ⟨i | n, h⟩
    · rfl
    · exact False.elim h
  right_inv i := rfl

theorem card_branchVar (left : Bool) : Fintype.card (BranchVar k left) = 197 := by
  rw [Fintype.card_congr (branchEquiv k left), card_inChart]

/-! ### The branch maps -/

theorem brentPS_le_ker (left : Bool) :
    ∀ f ∈ brentPS k, (killR k left).comp (Φ k).toRingHom f = 0 := by
  intro f hf
  have h := map_brentPS_le k (Ideal.mem_map_of_mem (Φ k) hf)
  have h' : Φ k f ∈ branchIdeal k left := by
    cases left
    · exact h.2
    · exact h.1
  rw [← ker_kill] at h'
  exact h'

/-- **Projection of `Â` to a branch.** -/
noncomputable def branchMap (left : Bool) : Ahat k →+* MvPowerSeries (BranchVar k left) k :=
  Ideal.Quotient.lift _ ((killR k left).comp (Φ k).toRingHom) (brentPS_le_ker k left)

theorem branchMap_mk (left : Bool) (f : MvPowerSeries Var k) :
    branchMap k left (mkA k f) = kill k left (Φ k f) := rfl

theorem branchMap_surjective (left : Bool) : Function.Surjective (branchMap k left) := by
  intro g
  obtain ⟨f, rfl⟩ := killCompl_surjective (k := k) (emb k left) g
  refine ⟨mkA k ((Φ k).symm f), ?_⟩
  rw [branchMap_mk, RingEquiv.apply_symm_apply]
  rfl

/-- **The branch primes** `𝔭_L` (`left = true`) and `𝔭_R` (`left = false`). -/
noncomputable def branchPrime (left : Bool) : Ideal (Ahat k) := RingHom.ker (branchMap k left)

instance branchPrime_isPrime (left : Bool) : (branchPrime k left).IsPrime :=
  RingHom.ker_isPrime _

/-- **`Â ⧸ 𝔭_L ≃ k⟦c, x⟧` and `Â ⧸ 𝔭_R ≃ k⟦c, y⟧`.** -/
noncomputable def branchQuotEquiv (left : Bool) :
    (Ahat k ⧸ branchPrime k left) ≃+* MvPowerSeries (BranchVar k left) k :=
  RingHom.quotientKerEquivOfSurjective (branchMap_surjective k left)

theorem ringKrullDim_branch (left : Bool) :
    ringKrullDim (Ahat k ⧸ branchPrime k left) = 197 := by
  rw [ringKrullDim_eq_of_ringEquiv (branchQuotEquiv k left), ringKrullDim_mvPowerSeries,
    card_branchVar]
  rfl

/-- **Minimality**, given `dim Â ≤ 197`. -/
theorem branchPrime_minimal (left : Bool) (hdim : ringKrullDim (Ahat k) ≤ 197) :
    branchPrime k left ∈ minimalPrimes (Ahat k) := by
  refine ker_mem_minimalPrimes (branchMap k left) (branchMap_surjective k left)
    (varChain (BranchVar k left) k) (varChain_head _ k) ?_
  rw [varChain_length, card_branchVar]
  exact hdim

theorem branchPrime_minimal_charThree [CharP k 3] (left : Bool) :
    branchPrime k left ∈ minimalPrimes (Ahat k) :=
  branchPrime_minimal k left (ringKrullDim_Ahat_le_charThree k)

theorem branchPrime_minimal_charZero [CharZero k] (left : Bool) :
    branchPrime k left ∈ minimalPrimes (Ahat k) :=
  branchPrime_minimal k left (ringKrullDim_Ahat_le_charZero k)

/-- **The branches are distinct.** -/
theorem branchPrime_ne : branchPrime k true ≠ branchPrime k false := by
  let j : Fin 251 := ⟨143, by norm_num⟩
  let a : Ahat k := mkA k ((Φ k).symm (X (Sum.inl j)))
  have hR : a ∈ branchPrime k false := by
    rw [branchPrime, RingHom.mem_ker, branchMap_mk, RingEquiv.apply_symm_apply]
    exact kill_X_drop k false (by simp [Keep, InChart, j])
  have hL : a ∉ branchPrime k true := by
    rw [branchPrime, RingHom.mem_ker, branchMap_mk, RingEquiv.apply_symm_apply]
    have hk : Keep k true (Sum.inl j) := by simp [Keep, InChart, j]
    have h := killCompl_X (R := k) (e := emb k true) ⟨Sum.inl j, hk⟩
    change kill k true (X (Sum.inl j)) = X ⟨Sum.inl j, hk⟩ at h
    rw [h]
    exact X_ne_zero' _
  intro h
  exact hL (h ▸ hR)

/-! ### The intersection -/

/-- The orbit coordinates `c`. -/
def KeepO : W k → Prop := Sum.elim (fun i => i.val < 143) (fun _ => False)

instance : DecidablePred (KeepO k) := fun w => by
  cases w <;> (simp only [KeepO, Sum.elim_inl, Sum.elim_inr]; infer_instance)

abbrev OrbitVar := {w : W k // KeepO k w}

def embO : OrbitVar k ↪ W k := Function.Embedding.subtype _

noncomputable def killO : MvPowerSeries (W k) k →+* MvPowerSeries (OrbitVar k) k :=
  (killCompl (R := k) (embO k)).toRingHom

theorem range_embO_compl :
    (Set.range (embO k))ᶜ = (Set.range (emb k true))ᶜ ∪ (Set.range (emb k false))ᶜ := by
  have hO : Set.range (embO k) = {w | KeepO k w} := by
    ext w
    simp [embO]
  rw [← Set.compl_inter, range_emb, range_emb, hO]
  congr 1
  ext w
  rcases w with i | n
  · simp only [Set.mem_setOf_eq, Set.mem_inter_iff, KeepO, Keep, Sum.elim_inl, InChart]
    simp only [if_true, Bool.false_eq_true, if_false]
    omega
  · simp [KeepO, Keep]

theorem ker_killO :
    RingHom.ker (killO k) = branchIdeal k true ⊔ branchIdeal k false := by
  rw [killO, ker_killCompl, range_embO_compl, Set.image_union, Ideal.span_union]
  rfl

theorem brentPS_le_kerO : ∀ f ∈ brentPS k, (killO k).comp (Φ k).toRingHom f = 0 := by
  intro f hf
  have h := map_brentPS_le k (Ideal.mem_map_of_mem (Φ k) hf)
  change Φ k f ∈ RingHom.ker (killO k)
  rw [ker_killO]
  exact Ideal.mem_sup_left h.1

/-- The projection of `Â` to the orbit coordinates. -/
noncomputable def orbitMap : Ahat k →+* MvPowerSeries (OrbitVar k) k :=
  Ideal.Quotient.lift _ ((killO k).comp (Φ k).toRingHom) (brentPS_le_kerO k)

theorem orbitMap_surjective : Function.Surjective (orbitMap k) := by
  intro g
  obtain ⟨f, rfl⟩ := killCompl_surjective (k := k) (embO k) g
  refine ⟨mkA k ((Φ k).symm f), ?_⟩
  change killO k (Φ k ((Φ k).symm f)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem comap_Φ (I : Ideal (MvPowerSeries (W k) k)) :
    I.comap (Φ k).toRingHom = I.map (Φ k).symm := (Ideal.map_symm (Φ k)).symm

theorem ker_branchMap (left : Bool) :
    branchPrime k left = Ideal.map (mkA k) ((branchIdeal k left).map (Φ k).symm) := by
  rw [branchPrime, branchMap, ker_quotient_lift, ← RingHom.comap_ker, ← comap_Φ, ← ker_kill]

theorem ker_orbitMap : RingHom.ker (orbitMap k) = branchPrime k true ⊔ branchPrime k false := by
  rw [orbitMap, ker_quotient_lift, ← RingHom.comap_ker, ker_killO, comap_Φ, Ideal.map_sup,
    Ideal.map_sup, ker_branchMap, ker_branchMap]

/-- **`Â ⧸ (𝔭_L + 𝔭_R) ≃ k⟦c⟧`.** -/
noncomputable def intersectionEquiv :
    (Ahat k ⧸ (branchPrime k true ⊔ branchPrime k false)) ≃+* MvPowerSeries (OrbitVar k) k :=
  (Ideal.quotEquivOfEq (ker_orbitMap k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (orbitMap_surjective k))

def orbitEquiv : OrbitVar k ≃ {i : Fin 251 // i.val < 143} where
  toFun w := match w with
    | ⟨Sum.inl i, h⟩ => ⟨i, h⟩
    | ⟨Sum.inr _, h⟩ => False.elim h
  invFun i := ⟨Sum.inl i.1, i.2⟩
  left_inv w := by
    rcases w with ⟨i | n, h⟩
    · rfl
    · exact False.elim h
  right_inv i := rfl

theorem card_orbitVar : Fintype.card (OrbitVar k) = 143 := by
  rw [Fintype.card_congr (orbitEquiv k), Fintype.card_subtype]
  decide +kernel

/-- **The formal intersection has dimension 143.** -/
theorem ringKrullDim_intersection :
    ringKrullDim (Ahat k ⧸ (branchPrime k true ⊔ branchPrime k false)) = 143 := by
  rw [ringKrullDim_eq_of_ringEquiv (intersectionEquiv k), ringKrullDim_mvPowerSeries,
    card_orbitVar]
  rfl

end Brent.Formal
