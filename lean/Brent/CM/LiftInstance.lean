import Brent.CM.Lift
import Brent.CM.RegularCoprime
import Brent.Z3Basis
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Step E instance: the lifted quadrics are regular over `ℤ₍₃₎` and `ℚ` (lines 521–545)

DRAFT, NOT YET COMPILED.

Paper: *In the local polynomial ring `R₀[z]_(3,z)`, the sequence `3, q̃₁, …, q̃₅₄` is regular by
the regularity of its reduction after the first element. Permute the sequence to put `3`
last. Localizing at `(z)` gives `ℚ[z]_(z)`, where the 54 quadrics remain a regular sequence …
Flat completion gives the same property in `ℚ⟦z⟧`.*

For **any** lift `q̃ᵢ ∈ ℤ₍₃₎[x, y]` of the certified quadrics (`map ρ q̃ᵢ = qᵢ`, `ρ : ℤ₍₃₎ → 𝔽₃`
the residue map), this file proves:

* `isWeaklyRegular_q`: the `qᵢ` are a weakly regular sequence on `𝔽₃[x, y]` (step D, in the
  `IsWeaklyRegular` form);
* `cons_three_regular`: `3, q̃₁, …, q̃₅₄` is weakly regular on `ℤ₍₃₎[x, y]`;
* `lifted_regular_local`: after localizing at the maximal ideal `(3, x, y)` the sequence can be
  permuted, so `q̃₁, …, q̃₅₄` is weakly regular on `ℤ₍₃₎[x, y]_(3,x,y)`;
* `lifted_regular_flat`: it stays weakly regular on every flat module over that local ring
  (the further localization giving `ℚ[z]_(z)`, and the completion).

The general statements are over any ring `R` with a surjection `ρ : R → k` onto a field whose
kernel is `(t)`, `t ≠ 0`, `R` a Noetherian domain. That the paper's `q̃ᵢ` (the quadratic parts of
the lifted residual equations) are such a lift is the lifted elimination, recorded in
`AUDIT_TABLE.md`.
-/

namespace Brent.CM.LiftInstance

open MvPolynomial RingTheory.Sequence

/-! ### `qᵢ` weakly regular over `𝔽₃` -/

section WeaklyRegularOfMem

variable {K : Type*} [CommRing K] {n : ℕ} (g : Fin n → K)

theorem ofList_take_ofFn (i : ℕ) :
    Ideal.ofList ((List.ofFn g).take i) =
      Ideal.span (Set.range fun j : {j : Fin n // (j : ℕ) < i} => g j) := by
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_range, List.mem_take_iff_getElem, List.length_ofFn]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨⟨j, by omega⟩, by simp; omega⟩, ?_⟩
    rw [List.getElem_ofFn]
  · rintro ⟨⟨j, hj⟩, rfl⟩
    refine ⟨j, by omega, ?_⟩
    rw [List.getElem_ofFn]

/-- A sequence with `gᵢ h ∈ (g_j : j < i) → h ∈ (g_j : j < i)` is weakly regular. -/
theorem isWeaklyRegular_of_mem
    (hreg : ∀ (i : Fin n) (h : K),
      g i * h ∈ Ideal.span (Set.range fun j : {j : Fin n // (j : ℕ) < (i : ℕ)} => g j) →
      h ∈ Ideal.span (Set.range fun j : {j : Fin n // (j : ℕ) < (i : ℕ)} => g j)) :
    IsWeaklyRegular K (List.ofFn g) := by
  refine ⟨fun i hi => ?_⟩
  rw [List.length_ofFn] at hi
  have hgi : (List.ofFn g)[i] = g ⟨i, hi⟩ := List.getElem_ofFn (by simpa using hi)
  rw [hgi]
  set I := Ideal.ofList ((List.ofFn g).take i)
  have hI : (I • ⊤ : Submodule K K) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [hI]
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
  rw [← map_smul, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    smul_eq_mul, smul_eq_mul] at hab
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hmem : g ⟨i, hi⟩ * (a - b) ∈ I := by
    rw [mul_sub]
    exact hab
  rw [ofList_take_ofFn] at hmem ⊢
  exact hreg ⟨i, hi⟩ (a - b) hmem

end WeaklyRegularOfMem

open Brent.Groebner.Paper in
/-- **Step D, as a weakly regular sequence:** `q₀, …, q₅₃` on `𝔽₃[x, y]`. -/
theorem isWeaklyRegular_q :
    IsWeaklyRegular (MvPolynomial (Fin 54 ⊕ Fin 54) (ZMod 3)) (List.ofFn q) :=
  isWeaklyRegular_of_mem q fun i _ hh => Brent.CM.q_regular i hh

/-! ### The general lift -/

section General

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {k : Type*} [Field k]
  (ρ : R →+* k) (hρ : Function.Surjective ρ) {t : R} (ht : RingHom.ker ρ = Ideal.span {t})
  (ht0 : t ≠ 0) {σ : Type*} [Fintype σ]

/-- `R[σ]`. -/
abbrev P (R : Type*) [CommRing R] (σ : Type*) := MvPolynomial σ R

include hρ in
theorem map_surjective' : Function.Surjective (MvPolynomial.map ρ : P R σ →+* MvPolynomial σ k) :=
  MvPolynomial.map_surjective ρ hρ

include ht in
theorem ker_map_eq : RingHom.ker (MvPolynomial.map ρ : P R σ →+* MvPolynomial σ k) =
    Ideal.span {C t} := by
  rw [MvPolynomial.ker_map, ht, Ideal.map_span, Set.image_singleton]

include hρ ht in
/-- `R[σ] ⧸ t R[σ] ≅ k[σ]`, as `R[σ]`-modules (`k[σ]` an `R[σ]`-algebra through `map ρ`). -/
noncomputable def quotEquiv :
    letI := (MvPolynomial.map ρ : P R σ →+* MvPolynomial σ k).toAlgebra
    QuotSMulTop (C t : P R σ) (P R σ) ≃ₗ[P R σ] MvPolynomial σ k :=
  letI := (MvPolynomial.map ρ : P R σ →+* MvPolynomial σ k).toAlgebra
  have hI : ((C t : P R σ) • (⊤ : Submodule (P R σ) (P R σ))) =
      RingHom.ker (Algebra.ofId (P R σ) (MvPolynomial σ k)) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    exact (ker_map_eq ρ ht).symm
  ((Ideal.quotientEquivAlgOfEq (P R σ) hI).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId (P R σ) (MvPolynomial σ k))
      (map_surjective' ρ hρ))).toLinearEquiv

include hρ ht ht0 in
/-- **`t, q̃₁, …, q̃_s` is weakly regular on `R[σ]`** when the reductions `qᵢ = map ρ q̃ᵢ` are
weakly regular on `k[σ]`. -/
theorem cons_regular_lift (qt : List (P R σ))
    (hq : IsWeaklyRegular (MvPolynomial σ k) (qt.map (MvPolynomial.map ρ))) :
    IsWeaklyRegular (P R σ) (C t :: qt) := by
  letI := (MvPolynomial.map ρ : P R σ →+* MvPolynomial σ k).toAlgebra
  have hCt : (C t : P R σ) ≠ 0 := by rwa [Ne, MvPolynomial.C_eq_zero]
  have hreg : IsSMulRegular (P R σ) (C t : P R σ) := fun a b h => mul_left_cancel₀ hCt h
  refine IsWeaklyRegular.cons hreg ?_
  rw [(quotEquiv ρ hρ ht).isWeaklyRegular_congr]
  rw [← isWeaklyRegular_map_algebraMap_iff (S := MvPolynomial σ k) (M := MvPolynomial σ k) qt]
  exact hq

/-- The maximal ideal `(t, σ)` of `R[σ]`: the kernel of `R[σ] → k`, `p ↦ ρ (p(0))`. -/
noncomputable def maxIdeal : Ideal (P R σ) :=
  RingHom.ker ((constantCoeff : MvPolynomial σ k →+* k).comp
    (MvPolynomial.map ρ : P R σ →+* MvPolynomial σ k))

instance maxIdeal_isPrime : (maxIdeal ρ (σ := σ)).IsPrime := RingHom.ker_isPrime _

/-- `R[σ]_(t, σ)`. -/
abbrev Loc := Localization.AtPrime (maxIdeal ρ (σ := σ))

include hρ ht ht0 in
/-- **Localize at `(t, σ)` and permute: `q̃₁, …, q̃_s` is weakly regular on `R[σ]_(t, σ)`.** -/
theorem lifted_regular_local (qt : List (P R σ))
    (hq : IsWeaklyRegular (MvPolynomial σ k) (qt.map (MvPolynomial.map ρ)))
    (hq0 : ∀ p ∈ qt, constantCoeff (MvPolynomial.map ρ p) = 0) :
    IsWeaklyRegular (Loc ρ (σ := σ)) (qt.map (algebraMap (P R σ) (Loc ρ (σ := σ)))) := by
  set L := Loc ρ (σ := σ)
  haveI : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (maxIdeal ρ (σ := σ)).primeCompl L inferInstance
  -- flat base change `R[σ] → L`
  have h1 := (cons_regular_lift ρ hρ ht ht0 qt hq).isWeaklyRegular_lTensor (M₂ := L)
  rw [(TensorProduct.rid (P R σ) L).isWeaklyRegular_congr] at h1
  rw [← isWeaklyRegular_map_algebraMap_iff (S := L) (M := L)] at h1
  rw [List.map_cons] at h1
  -- permute in the local ring `L`
  have hmax : ∀ r ∈ algebraMap (P R σ) L (C t) :: qt.map (algebraMap (P R σ) L),
      r ∈ IsLocalRing.maximalIdeal L := by
    intro r hr
    rw [List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L (maxIdeal ρ), maxIdeal,
        RingHom.mem_ker]
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.constantCoeff_C]
      rw [← RingHom.mem_ker, ht]
      exact Ideal.mem_span_singleton_self t
    · rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L (maxIdeal ρ), maxIdeal,
        RingHom.mem_ker, RingHom.comp_apply]
      exact hq0 p hp
  have h2 := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h1
    (List.perm_append_singleton _ _).symm hmax
  exact ((isWeaklyRegular_append_iff L _ _).mp h2).1

include hρ ht ht0 in
/-- **Flat base change** (to `ℚ[z]_(z)` and to the completion): the lifted sequence stays weakly
regular on every flat module over `R[σ]_(t, σ)`. -/
theorem lifted_regular_flat (qt : List (P R σ))
    (hq : IsWeaklyRegular (MvPolynomial σ k) (qt.map (MvPolynomial.map ρ)))
    (hq0 : ∀ p ∈ qt, constantCoeff (MvPolynomial.map ρ p) = 0)
    (M₂ : Type*) [AddCommGroup M₂] [Module (Loc ρ (σ := σ)) M₂]
    [Module.Flat (Loc ρ (σ := σ)) M₂] :
    IsWeaklyRegular M₂ (qt.map (algebraMap (P R σ) (Loc ρ (σ := σ)))) := by
  have h := (lifted_regular_local ρ hρ ht ht0 qt hq hq0).isWeaklyRegular_lTensor (M₂ := M₂)
  exact (TensorProduct.rid (Loc ρ (σ := σ)) M₂).isWeaklyRegular_congr _ |>.mp h

end General

/-! ### `ℤ₍₃₎ → 𝔽₃` -/

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

open Brent.Z3 in
theorem int_unit_mod3 (y : (Ideal.span {(3 : ℤ)}).primeCompl) :
    IsUnit ((Int.castRingHom (ZMod 3)) y) := by
  refine Ne.isUnit fun h => y.2 ?_
  rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Ideal.mem_span_singleton.mpr (by exact_mod_cast h)

open Brent.Z3 in
instance : IsNoetherianRing R0 :=
  IsLocalization.isNoetherianRing (Ideal.span {(3 : ℤ)}).primeCompl R0 inferInstance

open Brent.Z3 in
theorem three_ne_zero_R0 : (3 : R0) ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap ℤ R0) :=
    IsLocalization.injective R0 (Ideal.primeCompl_le_nonZeroDivisors _)
  have : algebraMap ℤ R0 3 = algebraMap ℤ R0 0 := by rw [map_ofNat, map_zero, h]
  exact absurd (hinj this) (by norm_num)

open Brent.Z3 in
/-- The residue map `ρ : ℤ₍₃₎ → 𝔽₃`. -/
noncomputable def rho3 : R0 →+* ZMod 3 :=
  IsLocalization.lift (M := (Ideal.span {(3 : ℤ)}).primeCompl) (S := R0) int_unit_mod3

open Brent.Z3 in
theorem rho3_algebraMap (a : ℤ) : rho3 (algebraMap ℤ R0 a) = (a : ZMod 3) := by
  rw [rho3, IsLocalization.lift_eq]
  rfl

open Brent.Z3 in
theorem rho3_surjective : Function.Surjective rho3 := by
  intro c
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective c
  exact ⟨algebraMap ℤ R0 a, rho3_algebraMap a⟩

open Brent.Z3 in
theorem ker_rho3 : RingHom.ker rho3 = Ideal.span {(3 : R0)} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Ideal.span {(3 : ℤ)}).primeCompl x
    have hspec := IsLocalization.mk'_spec R0 a s
    have h1 := congrArg rho3 hspec
    rw [map_mul, hx, zero_mul, rho3_algebraMap] at h1
    obtain ⟨b, rfl⟩ : (3 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp (by
      exact_mod_cast h1.symm)
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]
    refine Ideal.mul_mem_right _ _ ?_
    rw [map_ofNat]
    exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have : (3 : R0) = algebraMap ℤ R0 3 := by simp
    rw [this, rho3_algebraMap]
    rfl

open Brent.Groebner.Paper in
/-- The quadrics have no constant term. -/
theorem constantCoeff_q (ell : Fin 54) : constantCoeff (q ell) = 0 := by
  rw [q_eq, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MvPolynomial.constantCoeff_monomial, if_neg]
  intro h
  have := congrArg (fun d => d (Sum.inl i)) h
  simp [e_inl] at this

open Brent.Z3 Brent.Groebner.Paper in
/-- **Step E for the 54 quadrics.** For any lift `q̃ᵢ ∈ ℤ₍₃₎[x, y]` of the certified `qᵢ`, the
`q̃ᵢ` form a weakly regular sequence on `ℤ₍₃₎[x, y]_(3,x,y)` and on every flat module over it
(`ℚ[x, y]_(x,y)`, the completion). -/
theorem lifted_quadrics_regular (qt : Fin 54 → MvPolynomial (Fin 54 ⊕ Fin 54) R0)
    (hred : ∀ i, MvPolynomial.map rho3 (qt i) = q i)
    (M₂ : Type*) [AddCommGroup M₂] [Module (Loc rho3 (σ := Fin 54 ⊕ Fin 54)) M₂]
    [Module.Flat (Loc rho3 (σ := Fin 54 ⊕ Fin 54)) M₂] :
    IsWeaklyRegular M₂ ((List.ofFn qt).map
      (algebraMap (P R0 (Fin 54 ⊕ Fin 54)) (Loc rho3 (σ := Fin 54 ⊕ Fin 54)))) := by
  have hmap : (List.ofFn qt).map (MvPolynomial.map rho3) = List.ofFn q := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hred i
  refine lifted_regular_flat rho3 rho3_surjective ker_rho3 three_ne_zero_R0 (List.ofFn qt)
    (by rw [hmap]; exact isWeaklyRegular_q) (fun p hp => ?_) M₂
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  show constantCoeff (MvPolynomial.map rho3 (qt i)) = 0
  rw [hred]
  exact constantCoeff_q i

end Brent.CM.LiftInstance
