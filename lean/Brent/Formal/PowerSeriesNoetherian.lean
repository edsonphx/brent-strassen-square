import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Fintype.Option

/-!
# Multivariate power series over a Noetherian ring are Noetherian

Splitting off one variable, `R⟦Option σ⟧ ≃+* (R⟦σ⟧)⟦X⟧`, and Mathlib's one-variable
theorem give the result for every finite index type by induction.
-/

open scoped BigOperators

namespace Brent.Formal

open Finsupp

variable {σ : Type*} {R : Type*} [CommRing R]

/-- The coefficient table of `f` along the extra variable. -/
noncomputable def splitFun (f : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n => fun s => MvPowerSeries.coeff (s.optionElim n) f

theorem coeff_splitFun (f : MvPowerSeries (Option σ) R) (n : ℕ) (s : σ →₀ ℕ) :
    MvPowerSeries.coeff s (PowerSeries.coeff n (splitFun f)) =
      MvPowerSeries.coeff (s.optionElim n) f := by
  rw [splitFun, PowerSeries.coeff_mk]
  rfl

theorem optionElim_add (a b : σ →₀ ℕ) (i j : ℕ) :
    a.optionElim i + b.optionElim j = (a + b).optionElim (i + j) := by
  ext x
  cases x <;> simp

theorem optionElim_inj {a b : σ →₀ ℕ} {i j : ℕ} (h : a.optionElim i = b.optionElim j) :
    a = b ∧ i = j := by
  refine ⟨?_, ?_⟩
  · have := congrArg Finsupp.some h; simpa using this
  · have := congrArg (fun d => d none) h; simpa using this

theorem splitFun_mul (f g : MvPowerSeries (Option σ) R) :
    splitFun (f * g) = splitFun f * splitFun g := by
  classical
  ext n s
  rw [coeff_splitFun, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul, coeff_splitFun]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => (x.2.1.optionElim x.1.1, x.2.2.optionElim x.1.2))
    (fun y => ((y.1 none, y.2 none), (y.1.some, y.2.some))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩ h
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at h ⊢
    rw [optionElim_add, h.1, h.2]
  · rintro ⟨y₁, y₂⟩ h
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at h ⊢
    have h1 := congrArg (fun d => d none) h
    have h2 := congrArg Finsupp.some h
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.optionElim_apply_eq_elim,
      Option.elim_none] at h1
    refine ⟨h1, ?_⟩
    rw [← Finsupp.some_add, h2, Finsupp.some_optionElim]
  · rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩ _
    simp
  · rintro ⟨y₁, y₂⟩ _
    simp
  · rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩ _
    rfl

/-- Split off the extra variable. -/
noncomputable def splitEquiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := splitFun
  invFun G := fun d => MvPowerSeries.coeff d.some (PowerSeries.coeff (d none) G)
  left_inv f := by
    funext d
    change MvPowerSeries.coeff d.some (PowerSeries.coeff (d none) (splitFun f)) = f d
    rw [coeff_splitFun, Finsupp.optionElim_some]
    rfl
  right_inv G := by
    ext n s
    rw [coeff_splitFun]
    change MvPowerSeries.coeff (s.optionElim n).some
      (PowerSeries.coeff ((s.optionElim n) none) G) = _
    simp
  map_mul' := splitFun_mul
  map_add' f g := by
    ext n s
    simp only [map_add, coeff_splitFun]

theorem isNoetherianRing_empty [IsNoetherianRing R] (σ : Type*) [IsEmpty σ] :
    IsNoetherianRing (MvPowerSeries σ R) := by
  refine isNoetherianRing_of_surjective R _ MvPowerSeries.C fun f => ⟨MvPowerSeries.constantCoeff f, ?_⟩
  ext d
  have hd : d = 0 := Subsingleton.elim _ _
  subst hd
  simp

/-- **Noetherianity.** Power series in finitely many variables over a Noetherian ring. -/
theorem isNoetherianRing_mvPowerSeries [IsNoetherianRing R] (σ : Type*) [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ R) := by
  have := Fintype.ofFinite σ
  refine Fintype.induction_empty_option
    (P := fun α _ => IsNoetherianRing (MvPowerSeries α R)) ?_ ?_ ?_ σ
  · intro α β _ e h
    exact @isNoetherianRing_of_ringEquiv _ _ _ _ (MvPowerSeries.renameEquiv R e).toRingEquiv h
  · exact isNoetherianRing_empty PEmpty
  · intro α _ h
    exact isNoetherianRing_of_ringEquiv _ splitEquiv.symm

instance instIsNoetherianRing [IsNoetherianRing R] {σ : Type*} [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ R) :=
  isNoetherianRing_mvPowerSeries σ

end Brent.Formal
