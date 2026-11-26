import Brent.CM.RegularCoprime
import Brent.Groebner.MonomialHeight
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! The height of the original ideal, not just its initial monomial ideal.
The regularity proof gives a strictly increasing prime chain below every prime
containing the quadrics. The ideal of all x variables supplies the upper bound. -/
namespace Brent.CM
open MvPolynomial Brent.Groebner Brent.Groebner.Paper Brent.Groebner.MonomialHeight

abbrev QPoly := MvPolynomial (Fin 54 ⊕ Fin 54) (ZMod 3)
noncomputable def qPrefix (n : ℕ) : Ideal QPoly :=
  Ideal.span (Set.range fun j : {j : Fin 54 // j.val < n} => q j)

theorem qPrefix_mono {n m : ℕ} (h : n ≤ m) : qPrefix n ≤ qPrefix m := by
  apply Ideal.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j.val, lt_of_lt_of_le j.property h⟩, rfl⟩

/-- Every prime containing the first n quadrics has height at least n. -/
theorem qPrefix_primeHeight_ge (n : ℕ) (hn : n ≤ 54) (p : Ideal QPoly)
    [p.IsPrime] (hp : qPrefix n ≤ p) : (n : ℕ∞) ≤ p.primeHeight := by
  induction n generalizing p with
  | zero => exact zero_le _
  | succ n ih =>
    let i : Fin 54 := ⟨n, by omega⟩
    have hpre : qPrefix n ≤ p := (qPrefix_mono (Nat.le_succ n)).trans hp
    obtain ⟨r, hr, hrp⟩ := Ideal.exists_minimalPrimes_le hpre
    haveI : r.IsPrime := Ideal.minimalPrimes_isPrime hr
    have hqi : q i ∈ p := hp (Ideal.subset_span ⟨⟨i, Nat.lt_succ_self n⟩, rfl⟩)
    have hnqi : q i ∉ r := by
      intro h
      obtain ⟨y, hy, hprod⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hr h
      apply hy
      exact q_regular i hprod
    have hlt : r < p := lt_of_le_of_ne hrp (fun he => hnqi (he.symm ▸ hqi))
    have hprev := ih (by omega) r hr.1.2
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ r.primeHeight + 1 := by gcongr
      _ ≤ p.primeHeight := Ideal.primeHeight_add_one_le_of_lt hlt

theorem qPrefix_full : qPrefix 54 = Ideal.span (Set.range q) := by
  congr 1
  ext f
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j, j.isLt⟩, rfl⟩

theorem qIdeal_le_xIdeal : Ideal.span (Set.range q) ≤
    varIdeal (ZMod 3) (Set.range (Sum.inl : Fin 54 → Fin 54 ⊕ Fin 54)) := by
  rw [Ideal.span_le]
  rintro _ ⟨ell, rfl⟩
  rw [q]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.sum_mem
  intro j _
  have hx : (X (Sum.inl i) : QPoly) ∈
      varIdeal (ZMod 3) (Set.range (Sum.inl : Fin 54 → Fin 54 ⊕ Fin 54)) :=
    Ideal.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)

/-- The actual homogeneous quadratic ideal has height 54. -/
theorem quadraticIdeal_height_eq_54 : (Ideal.span (Set.range q)).height = 54 := by
  apply le_antisymm
  · calc (Ideal.span (Set.range q)).height ≤
        (varIdeal (ZMod 3) (Set.range (Sum.inl : Fin 54 → Fin 54 ⊕ Fin 54))).height :=
          Ideal.height_mono qIdeal_le_xIdeal
      _ = 54 := by
        rw [Ideal.height_eq_primeHeight, primeHeight_varIdeal_range _ Sum.inl_injective]
  · rw [← qPrefix_full]
    unfold Ideal.height
    refine le_iInf₂ fun J hJ => ?_
    haveI := Ideal.minimalPrimes_isPrime hJ
    exact qPrefix_primeHeight_ge 54 le_rfl J hJ.1.2

end Brent.CM
