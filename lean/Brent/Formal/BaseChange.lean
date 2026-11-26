import Brent.Formal.PowerSeriesAdic
import Brent.CM.LiftInstance

/-! Coefficientwise base change of centered formal substitutions and their
inverses. No inversion of a nonunit and no finite-order truncation assumption. -/
namespace Brent.Formal
open MvPowerSeries Finsupp
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ]

/-- The coefficient of degree `d` uses only finitely many input monomials,
all of degree at most `d.degree`. -/
noncomputable def exponentBox (n : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun a : σ → Fin (n + 1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (a i).val))

theorem mem_exponentBox {m : σ →₀ ℕ} {n : ℕ} (h : m.degree ≤ n) :
    m ∈ exponentBox n := by
  classical
  apply Finset.mem_image.mpr
  let a : σ → Fin (n + 1) := fun i => ⟨m i, by have := (le_degree i m).trans h; omega⟩
  refine ⟨a, Finset.mem_univ _, ?_⟩
  ext i
  simp [a]

/-- Centered substitution is natural under any coefficient ring homomorphism. -/
theorem map_subst_centered (ρ : R →+* S) {b : σ → MvPowerSeries τ R}
    (hb : ∀ i, constantCoeff (b i) = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.map ρ (subst b f) =
      subst (fun i => MvPowerSeries.map ρ (b i)) (MvPowerSeries.map ρ f) := by
  classical
  let b' : σ → MvPowerSeries τ S := fun i => MvPowerSeries.map ρ (b i)
  have hb' : ∀ i, constantCoeff (b' i) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, b', coeff_map,
      coeff_zero_eq_constantCoeff_apply, hb i, map_zero]
  ext m
  rw [coeff_map, coeff_subst (hasSubst_of_constantCoeff_zero hb),
    coeff_subst (hasSubst_of_constantCoeff_zero hb')]
  have bound {T : Type*} [CommRing T] (a : σ → MvPowerSeries τ T)
      (ha : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries σ T) :
      Function.support (fun d : σ →₀ ℕ =>
        coeff d g • coeff m (d.prod fun i e => a i ^ e)) ⊆ exponentBox m.degree := by
    intro d hd
    by_contra hn
    have hdeg : m.degree < d.degree := lt_of_not_ge (fun h => hn (mem_exponentBox h))
    have hlow : LowZero d.degree (d.prod fun i e => a i ^ e) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum]
      exact prod_lowZero (fun i => lowZero_one_of_constantCoeff (ha i)) d _
    apply hd
    simp [hlow m hdeg]
  rw [finsum_eq_sum_of_support_subset _ (bound b hb f),
    finsum_eq_sum_of_support_subset _ (bound b' hb' (MvPowerSeries.map ρ f)), map_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [smul_eq_mul, map_mul, coeff_map]
  congr 1
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_pow, b']

/-- An inverse coordinate tuple stays an inverse tuple after base change. -/
theorem inverse_tuple_baseChange (ρ : R →+* S)
    (a b : σ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, subst b (a i) = X i)
    (hba : ∀ i, subst a (b i) = X i) :
    (∀ i, subst (fun j => MvPowerSeries.map ρ (b j))
      (MvPowerSeries.map ρ (a i)) = X i) ∧
    (∀ i, subst (fun j => MvPowerSeries.map ρ (a j))
      (MvPowerSeries.map ρ (b i)) = X i) := by
  constructor
  · intro i
    rw [← map_subst_centered ρ hb, hab i]
    simp
  · intro i
    rw [← map_subst_centered ρ ha, hba i]
    simp

/-- Normal substitution, in particular setting the new normal coordinates to
zero after applying the inverse, commutes with reduction modulo three. -/
theorem normal_substitution_mod3
    (b : σ → MvPowerSeries τ Brent.Z3.R0)
    (hb : ∀ i, constantCoeff (b i) = 0)
    (f : MvPowerSeries σ Brent.Z3.R0) :
    MvPowerSeries.map Brent.CM.LiftInstance.rho3 (subst b f) =
      subst (fun i => MvPowerSeries.map Brent.CM.LiftInstance.rho3 (b i))
        (MvPowerSeries.map Brent.CM.LiftInstance.rho3 f) :=
  map_subst_centered _ hb f

end Brent.Formal
