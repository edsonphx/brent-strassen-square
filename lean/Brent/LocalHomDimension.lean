import Brent.LocalDimension

/-!
# Dimension comparison along a local homomorphism

If a local homomorphism of Noetherian local rings `A → B` is surjective on
cotangent spaces (`𝔪_B ⊆ 𝔪_A B + 𝔪_B²`), then `dim B ≤ dim A`. Nakayama gives
`𝔪_A B = 𝔪_B`; a system of parameters of `A` then generates an `𝔪_B`-primary ideal,
and Krull's height theorem bounds `dim B` by its length.

This is the algebraic substitute for the formal inverse argument of the paper
(§3, "From differential rank to the dimension lower bound"): an exact family
`A → B` whose differential is injective forces `dim A ≥ dim B`.
-/

namespace Brent

open IsLocalRing

/-- A local homomorphism of Noetherian local rings that is surjective on cotangent spaces
does not increase Krull dimension. -/
theorem ringKrullDim_le_of_maximalIdeal_le
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (ψ : A →+* B) [IsLocalHom ψ]
    (h : maximalIdeal B ≤ (maximalIdeal A).map ψ ⊔ maximalIdeal B ^ 2) :
    ringKrullDim B ≤ ringKrullDim A := by
  set mA := maximalIdeal A
  set mB := maximalIdeal B
  -- Nakayama: the extended maximal ideal is the maximal ideal.
  have hmap : mA.map ψ ≤ mB := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp hx (isUnit_of_map_unit ψ x hu)
  have hmB : mB ≤ mA.map ψ := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (mB : Ideal B)) (I := mB) (N := mA.map ψ) (N' := mB)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rw [Ideal.smul_eq_mul, ← pow_two]
      exact h
  -- A system of parameters of `A`.
  obtain ⟨J, hJm, hJrank, hJheight⟩ :=
    Ideal.exists_spanRank_eq_and_height_eq mA Ideal.IsPrime.ne_top'
  have hmin : mA ∈ J.minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_eq hJm hJheight.ge
  have hrad : mA ≤ J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun P hP => ?_
    have : P.IsPrime := Ideal.minimalPrimes_isPrime hP
    exact hmin.2 ⟨this, hP.1.2⟩ (le_maximalIdeal this.ne_top)
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (mA : Ideal A))
  have hJfg : J.FG := IsNoetherian.noetherian J
  -- Its extension is `𝔪_B`-primary, so it bounds the dimension of `B`.
  have hpow : mB ^ (N + 1) ≤ J.map ψ := by
    calc mB ^ (N + 1) ≤ mB ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
      _ ≤ (mA.map ψ) ^ N := Ideal.pow_right_mono hmB N
      _ = (mA ^ N).map ψ := (Ideal.map_pow _ _ _).symm
      _ ≤ J.map ψ := Ideal.map_mono hN
  have hJB : J.map ψ ≤ mB := (Ideal.map_mono hJm).trans hmap
  have hradB : (J.map ψ).radical = mB := by
    apply le_antisymm
    · exact (Ideal.radical_mono hJB).trans_eq (Ideal.IsPrime.radical inferInstance)
    · rw [← Ideal.IsPrime.radical (inferInstance : mB.IsPrime),
        ← Ideal.radical_pow (I := mB) (Nat.succ_ne_zero N)]
      exact Ideal.radical_mono hpow
  have hheight : (J.map ψ).height = mB.height := by
    unfold Ideal.height
    have heq := Ideal.radical_minimalPrimes (I := J.map ψ)
    rw [hradB] at heq
    simp only [← heq]
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
  change (mB.height : WithBot ℕ∞) ≤ mA.height
  rw [← hheight, ← hJheight]
  apply WithBot.coe_le_coe.mpr
  calc (J.map ψ).height ≤ (J.map ψ).spanFinrank :=
        Ideal.height_le_spanFinrank _ (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' hJB)
    _ ≤ J.spanFinrank := by exact_mod_cast Ideal.spanFinrank_map_le_of_fg ψ hJfg
    _ = J.height := by
        rw [hJheight]
        have h2 := hJrank
        rw [Submodule.FG.spanRank_eq_spanFinrank hJfg] at h2
        exact_mod_cast h2

end Brent
