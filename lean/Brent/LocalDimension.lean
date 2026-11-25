import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

namespace Brent

/-- Nilpotent equations do not change chains of prime ideals. -/
theorem quotient_dimension_of_le_nilradical {A : Type*} [CommRing A]
    (I : Ideal A) (hI : I ≤ nilradical A) :
    ringKrullDim (A ⧸ I) = ringKrullDim A := by
  let e : PrimeSpectrum (A ⧸ I) ≃o PrimeSpectrum A :=
    { Equiv.ofBijective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
        (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hI) with
      map_rel_iff' := Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective .. }
  exact Order.krullDim_eq_of_orderIso e

/-- A finite-order certificate for a system of parameters. If generators in the
maximal ideal kill one full order modulo the following order, Nakayama upgrades
the finite check to containment of a power, and the height theorem bounds the
actual Krull dimension. -/
theorem localDimension_le_of_power_le_span_sup_pow
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {n : ℕ} (f : Fin n → A) (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal A)
    {d : ℕ} (hd : d ≠ 0)
    (h : (IsLocalRing.maximalIdeal A) ^ d ≤
      Ideal.span (Set.range f) ⊔ (IsLocalRing.maximalIdeal A) ^ (d + 1)) :
    ringKrullDim A ≤ n := by
  let m := IsLocalRing.maximalIdeal A
  let I := Ideal.span (Set.range f)
  have hI : I ≤ m := Ideal.span_le.mpr (Set.range_subset_iff.mpr hf)
  have hpow : m ^ d ≤ I := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (m ^ d : Ideal A))
      (I := m) (N := I) (N' := (m ^ d : Ideal A))
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rw [Ideal.smul_eq_mul, ← pow_succ']
      exact h
  have hrad : I.radical = m := by
    apply le_antisymm
    · exact (Ideal.radical_mono hI).trans_eq (Ideal.IsPrime.radical (inferInstance : m.IsPrime))
    · rw [← Ideal.IsPrime.radical (inferInstance : m.IsPrime), ← Ideal.radical_pow (I := m) hd]
      exact Ideal.radical_mono hpow
  have hheight : I.height = m.height := by
    unfold Ideal.height
    have heq := Ideal.radical_minimalPrimes (I := I)
    rw [hrad] at heq
    simp only [← heq]
  have hcard : (Set.range f).encard ≤ n := by
    rw [← Set.image_univ]
    simpa using Set.encard_image_le f Set.univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  change (m.height : WithBot ℕ∞) ≤ n
  rw [← hheight]
  exact WithBot.coe_le_coe.mpr
    ((Ideal.height_le_spanFinrank I (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' hI)).trans
      ((Submodule.spanFinrank_span_le_encard (Set.range f)).trans hcard))

end Brent
