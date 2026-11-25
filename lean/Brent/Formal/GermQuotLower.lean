import Brent.Formal.GermLower

/-!
# Germ lower bounds for quotients of a polynomial ring

`GermLower.le_pointLocalDimension` bounds the local dimension of the Brent scheme at a solution.
This file states the same argument for any ideal `J` of `k[x₁,…,x_N]`: if a family over the germ
`k[t₁,…,tₙ]_(t)` kills `J`, passes through `q` at the origin, and has `n` linearly independent
derivatives, then the local ring of `k[x] ⧸ J` at `q` has dimension at least `n`.
-/

open MvPolynomial
open scoped BigOperators

namespace Brent.GermQuotLower

set_option synthInstance.maxHeartbeats 400000

open Brent.GermLower

variable {k : Type} [Field k] (n : ℕ) {σ : Type} [Fintype σ] [DecidableEq σ]
  (J : Ideal (MvPolynomial σ k)) (q : σ → k) (hJq : J ≤ RingHom.ker (eval q))

/-- Evaluation at `q` on the quotient. -/
noncomputable def evQ : MvPolynomial σ k ⧸ J →+* k := Ideal.Quotient.lift J (eval q) fun _ h => hJq h

theorem evQ_surjective : Function.Surjective (evQ J q hJq) :=
  fun c => ⟨Ideal.Quotient.mk _ (C c), by simp [evQ]⟩

/-- The maximal ideal of `q` in the quotient. -/
noncomputable abbrev mQ : Ideal (MvPolynomial σ k ⧸ J) := RingHom.ker (evQ J q hJq)

instance mQ_isMaximal : (mQ J q hJq).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evQ_surjective J q hJq)

/-- The local ring of `k[x] ⧸ J` at `q`. -/
noncomputable abbrev LocQ := Localization.AtPrime (mQ J q hJq)

variable (fam : σ → Germ k n) (hJfam : J ≤ RingHom.ker (eval₂Hom (algebraMap k (Germ k n)) fam))
  (hres : ∀ x, residue k n (fam x) = q x)

noncomputable def pullQ : MvPolynomial σ k ⧸ J →+* Germ k n :=
  Ideal.Quotient.lift J (eval₂Hom (algebraMap k (Germ k n)) fam) fun _ h => hJfam h

include hres in
theorem residue_pullQ : (residue k n).comp (pullQ n J fam hJfam) = evQ J q hJq := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [pullQ, evQ]
  · intro x
    simp only [RingHom.comp_apply, pullQ, evQ, Ideal.Quotient.lift_mk, eval₂Hom_X', eval_X]
    exact hres x

include hres in
theorem pullQ_unit (z : (mQ J q hJq).primeCompl) : IsUnit (pullQ n J fam hJfam z) := by
  apply isUnit_of_residue_ne_zero
  rw [← RingHom.comp_apply, residue_pullQ n J q hJq fam hJfam hres]
  exact fun h => z.2 h

/-- The local homomorphism to the germ. -/
noncomputable def pull : LocQ J q hJq →+* Germ k n :=
  IsLocalization.lift (M := (mQ J q hJq).primeCompl) (pullQ_unit n J q hJq fam hJfam hres)

theorem pull_algebraMap (z : MvPolynomial σ k ⧸ J) :
    pull n J q hJq fam hJfam hres (algebraMap _ (LocQ J q hJq) z) = pullQ n J fam hJfam z :=
  IsLocalization.lift_eq _ _

theorem pull_mem {a : LocQ J q hJq} (ha : a ∈ IsLocalRing.maximalIdeal (LocQ J q hJq)) :
    pull n J q hJq fam hJfam hres a ∈ IsLocalRing.maximalIdeal (Germ k n) := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (mQ J q hJq).primeCompl a
  dsimp only at ha ⊢
  have hz : z ∈ mQ J q hJq := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (LocQ J q hJq) (mQ J q hJq),
      ← IsLocalization.mk'_spec (LocQ J q hJq) z s]
    exact Ideal.mul_mem_right _ _ ha
  have hspec := congrArg (pull n J q hJq fam hJfam hres)
    (IsLocalization.mk'_spec (LocQ J q hJq) z s)
  rw [map_mul, pull_algebraMap, pull_algebraMap] at hspec
  have hres' := congrArg (residue k n) hspec
  rw [map_mul, ← RingHom.comp_apply (residue k n) (pullQ n J fam hJfam),
    ← RingHom.comp_apply (residue k n) (pullQ n J fam hJfam),
    residue_pullQ n J q hJq fam hJfam hres] at hres'
  have hz0 : evQ J q hJq z = 0 := hz
  have hs0 : evQ J q hJq s ≠ 0 := fun h => s.2 h
  rw [hz0] at hres'
  have : residue k n (pull n J q hJq fam hJfam hres
      (IsLocalization.mk' (LocQ J q hJq) z s)) = 0 :=
    (mul_eq_zero.mp hres').resolve_right hs0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := (hu.map (residue k n)).ne_zero
  contradiction

instance pull_isLocalHom : IsLocalHom (pull n J q hJq fam hJfam hres) where
  map_nonunit a ha := by
    by_contra hna
    exact (IsLocalRing.mem_maximalIdeal _).mp
      (pull_mem n J q hJq fam hJfam hres ((IsLocalRing.mem_maximalIdeal _).mpr hna)) ha

/-- The translated coordinates in the local ring. -/
noncomputable def coord (x : σ) : LocQ J q hJq :=
  algebraMap _ (LocQ J q hJq) (Ideal.Quotient.mk J (X x - C (q x)))

theorem coord_mem (x : σ) : coord J q hJq x ∈ IsLocalRing.maximalIdeal (LocQ J q hJq) := by
  rw [coord, IsLocalization.AtPrime.to_map_mem_maximal_iff (LocQ J q hJq) (mQ J q hJq)]
  change evQ J q hJq _ = 0
  simp [evQ]

theorem germJet_pull_coord (j : Fin n) (x : σ) :
    (germJet k n j (pull n J q hJq fam hJfam hres (coord J q hJq x))).snd =
      (germJet k n j (fam x)).snd := by
  rw [coord, pull_algebraMap]
  simp only [pullQ, Ideal.Quotient.lift_mk, map_sub, eval₂Hom_X', eval₂Hom_C]
  rw [TrivSqZeroExt.snd_sub, germJet_algebraMap_k]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

include hJfam hres in
set_option maxHeartbeats 1000000 in
/-- **Lower bound for `k[x] ⧸ J` at `q`.** -/
theorem le_ringKrullDim_locQ (D : Matrix (Fin n) σ k) (hD : LinearIndependent k D.row)
    (hjet : ∀ j x, (germJet k n j (fam x)).snd = D j x) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (LocQ J q hJq) := by
  suffices key : ringKrullDim (Germ k n) ≤ ringKrullDim (LocQ J q hJq) by
    exact (le_ringKrullDim_affineGerm k n).trans key
  refine ringKrullDim_le_of_maximalIdeal_le (A := LocQ J q hJq) (B := Germ k n)
    (pull n J q hJq fam hJfam hres) ?_
  have hsurj : Function.Surjective D.mulVecLin := by
    have hrank : D.rank = n := by
      rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hD, Fintype.card_fin]
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  have hmB : IsLocalRing.maximalIdeal (Germ k n) = Ideal.span (Set.range (param k n)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  refine hmB.le.trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨a, ha⟩ := hsurj (Pi.single j 1)
  let P := pull n J q hJq fam hJfam hres
  let comb : Germ k n := ∑ l, algebraMap k (Germ k n) (a l) * P (coord J q hJq l)
  have hcomb : comb ∈ (IsLocalRing.maximalIdeal (LocQ J q hJq)).map P := by
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    exact coord_mem J q hJq _
  have hdiff : param k n j - comb ∈ IsLocalRing.maximalIdeal (Germ k n) ^ 2 := by
    apply mem_sq_of_germJet
    · refine Ideal.sub_mem _ (hmB ▸ Ideal.subset_span ⟨j, rfl⟩) ?_
      exact Ideal.sum_mem _ fun l _ =>
        Ideal.mul_mem_left _ _ (pull_mem n J q hJq fam hJfam hres (coord_mem J q hJq _))
    · intro i
      have hai : ∑ l, D i l * a l = (Pi.single j (1 : k) : Fin n → k) i := by
        have h := congrFun ha i
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h
        exact h
      have hterm : ∀ l, (germJet k n i (algebraMap k (Germ k n) (a l) *
          P (coord J q hJq l))).snd = D i l * a l := by
        intro l
        rw [map_mul, germJet_algebraMap_k, TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_mul,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero, germJet_pull_coord,
          hjet, mul_comm]
      rw [map_sub, TrivSqZeroExt.snd_sub, germJet_param, map_sum, TrivSqZeroExt.snd_sum]
      simp only [hterm]
      rw [hai]
      by_cases h : j = i
      · subst h; simp
      · simp [h, Ne.symm h]
  have hsum : param k n j = comb + (param k n j - comb) := by ring
  rw [SetLike.mem_coe, hsum]
  exact Submodule.add_mem_sup hcomb hdiff

end Brent.GermQuotLower
