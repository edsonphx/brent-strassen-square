import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Equidimensionality of finitely generated domains over a field

For a domain `B` of finite type over a field `k`, every maximal ideal has height equal to the
Krull dimension of `B`, the localization at a maximal ideal has the same dimension, and the
dimension is finite.

The general statements below need no assumption on `k`; the statements requested in `TASKS.md`
(with `[IsAlgClosed k]`) are derived from them at the end.

Route:
* every maximal ideal of `k[X₀, …, X_{n-1}]` has height `n` (induction on `n`, using that the
  contraction of a maximal ideal of `R[X]` to a Jacobson ring `R` is maximal, and
  `Polynomial.height_eq_height_add_one`);
* Noether normalization gives a finite injective `A = k[X₀, …, X_{s-1}] → B`; for a maximal `𝔪`
  of `B`, going-down (A integrally closed, B a domain) gives `ht 𝔪 ≥ ht (𝔪 ∩ A)`, and
  incomparability (comap is strictly monotone on primes for integral extensions) gives `≤`.
-/

namespace Brent.Equidim

open Ideal

section Polynomial

variable (k : Type*) [Field k]

/-- Every maximal ideal of `k[X₀, …, X_{n-1}]` has height `n`, over any field. -/
theorem mvPolynomial_height_of_isMaximal :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have hdim : ringKrullDim (MvPolynomial (Fin 0) k) = 0 := by
      simp [ringKrullDim_eq_zero_of_field]
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [hdim] at h
    have h' : M.height ≤ 0 := by exact_mod_cast h
    simpa using h'
  | succ n ih =>
    intro M hM
    let e : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial (MvPolynomial (Fin n) k) :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin n) k)) := M.map e
    haveI hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hPM : P.height = M.height := e.height_map M
    have hp : (P.under (MvPolynomial (Fin n) k)).IsMaximal := by
      rw [Ideal.under_def, Polynomial.algebraMap_eq]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have h := Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) k)) P
    rw [← hPM, h, ih _ hp]
    push_cast
    rfl

end Polynomial

section General

variable {k B : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

omit [IsDomain B] in
/-- For an integral extension, the height of a prime is at most the height of its contraction. -/
theorem height_le_height_under_of_isIntegral {A : Type*} [CommRing A] [Algebra A B]
    [Algebra.IsIntegral A B] (P : Ideal B) [P.IsPrime] :
    P.height ≤ (P.under A).height := by
  rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight, Ideal.primeHeight,
    Ideal.primeHeight]
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap A B)) := by
    intro p q hpq
    have hpq' : p.asIdeal < q.asIdeal := hpq
    obtain ⟨hle, x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp hpq'
    change p.asIdeal.comap (algebraMap A B) < q.asIdeal.comap (algebraMap A B)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := A) hle ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  exact Order.height_le_height_apply_of_strictMono _ hmono ⟨P, inferInstance⟩

variable (k B) in
include k in
/-- There is a natural number `s` (the dimension of a Noether normalization) such that every
maximal ideal of `B` has height `s`. -/
theorem exists_forall_isMaximal_height_eq :
    ∃ s : ℕ, ∀ m : Ideal B, m.IsMaximal → m.height = s := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  refine ⟨s, fun m hm => ?_⟩
  algebraize [g.toRingHom]
  haveI : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hm' : (m.under (MvPolynomial (Fin s) k)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have h1 := mvPolynomial_height_of_isMaximal k s _ hm'
  apply le_antisymm
  · rw [← h1]
    exact height_le_height_under_of_isIntegral m
  · rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (m.under (MvPolynomial (Fin s) k)) m, h1]
    exact le_self_add

include k in
/-- A1 (any field). -/
theorem height_eq_ringKrullDim_of_isMaximal' (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨s, hs⟩ := exists_forall_isMaximal_height_eq k B
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : m.IsMaximal).ne_top
  · rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro n hn
    rw [hs n hn, hs m inferInstance]

include k in
/-- A2 (any field). -/
theorem ringKrullDim_localization_eq' (m : Ideal B) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim B := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m, height_eq_ringKrullDim_of_isMaximal' (k := k)]

include k in
/-- A3 (any field). -/
theorem ringKrullDim_ne_top' : ringKrullDim B ≠ ⊤ := by
  obtain ⟨s, hs⟩ := exists_forall_isMaximal_height_eq k B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  haveI := hm
  rw [← height_eq_ringKrullDim_of_isMaximal' (k := k) m, hs m hm]
  simp

end General

/-! ### The statements of `TASKS.md` -/

-- `[IsAlgClosed k]` is part of the requested statements but is not needed by the proofs.
set_option linter.unusedSectionVars false

variable {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

include k in
/-- A1. Every maximal ideal of a finitely generated domain over an algebraically closed field
has height equal to the Krull dimension. -/
theorem height_eq_ringKrullDim_of_isMaximal (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B :=
  height_eq_ringKrullDim_of_isMaximal' (k := k) m

include k in
/-- A2. The local ring at a maximal ideal has the same dimension. -/
theorem ringKrullDim_localization_eq (m : Ideal B) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim B :=
  ringKrullDim_localization_eq' (k := k) m

include k in
/-- A3. The dimension is finite. -/
theorem ringKrullDim_ne_top : ringKrullDim B ≠ ⊤ :=
  ringKrullDim_ne_top' (k := k)

/-- A4. Over an infinite field, a polynomial vanishing wherever a nonzero polynomial `f`
does not vanish is zero. -/
theorem eq_zero_of_eval_eq_zero_of_eval_ne_zero {k : Type*} [Field k] [Infinite k]
    {τ : Type*} [Finite τ] {f : MvPolynomial τ k} (hf : f ≠ 0) (g : MvPolynomial τ k)
    (h : ∀ a : τ → k, MvPolynomial.eval a f ≠ 0 → MvPolynomial.eval a g = 0) : g = 0 := by
  have hfg : f * g = 0 := by
    apply MvPolynomial.funext
    intro a
    by_cases ha : MvPolynomial.eval a f = 0
    · simp [ha]
    · simp [h a ha]
  exact (mul_eq_zero.mp hfg).resolve_left hf

end Brent.Equidim

#print axioms Brent.Equidim.height_eq_ringKrullDim_of_isMaximal
#print axioms Brent.Equidim.ringKrullDim_localization_eq
#print axioms Brent.Equidim.ringKrullDim_ne_top
#print axioms Brent.Equidim.eq_zero_of_eval_eq_zero_of_eval_ne_zero