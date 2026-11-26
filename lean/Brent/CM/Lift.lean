import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Lifting a regular sequence from `𝔽₃` to `ℤ₍₃₎` and `ℚ` (roadmap step E, §5 lines 521–545)

DRAFT, NOT YET COMPILED.

The paper's argument, abstracted over the ring and the module:

1. `t = 3` is regular on `M = ℤ₍₃₎[z]` and the reductions of `q̃₁, …, q̃₅₄` are regular on
   `M ⧸ 3M = 𝔽₃[z]` (step D), so `3, q̃₁, …, q̃₅₄` is weakly regular on `M` (`cons_regular`).
2. When all these elements lie in the Jacobson radical of the annihilator (after localizing at the
   irrelevant ideal `(3, z)`), the sequence may be permuted: `q̃₁, …, q̃₅₄, 3` is weakly regular,
   so `q̃₁, …, q̃₅₄` is weakly regular on `M` (`regular_of_lift`, `regular_of_lift_local`).
3. Flat base change (`ℤ₍₃₎ → ℚ`) keeps it weakly regular (`regular_of_lift_flat`).

Imports Mathlib only.
-/

namespace Brent.CM.Lift

open RingTheory.Sequence

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Step 1.** `t` regular on `M` and `qs` weakly regular on `M ⧸ tM` give `t :: qs` weakly
regular on `M`. -/
theorem cons_regular {t : R} {qs : List R} (ht : IsSMulRegular M t)
    (hq : IsWeaklyRegular (QuotSMulTop t M) qs) : IsWeaklyRegular M (t :: qs) :=
  IsWeaklyRegular.cons ht hq

/-- **Step 2.** If moreover every element of `t :: qs` lies in the Jacobson radical of the
annihilator of the Noetherian module `M`, then `qs` itself is weakly regular on `M`. -/
theorem regular_of_lift [IsNoetherian R M] {t : R} {qs : List R} (ht : IsSMulRegular M t)
    (hq : IsWeaklyRegular (QuotSMulTop t M) qs)
    (hjac : ∀ r ∈ t :: qs, r ∈ (Module.annihilator R M).jacobson) :
    IsWeaklyRegular M qs := by
  have h1 : IsWeaklyRegular M (qs ++ [t]) :=
    (cons_regular ht hq).of_perm_of_subset_jacobson_annihilator
      (List.perm_append_singleton t qs).symm hjac
  exact ((isWeaklyRegular_append_iff M qs [t]).mp h1).1

/-- **Step 2, local form.** Over a Noetherian local ring (the localization at the irrelevant
ideal `(3, z)`), with `t` and all `qs` in the maximal ideal. -/
theorem regular_of_lift_local [IsLocalRing R] [IsNoetherian R M] {t : R} {qs : List R}
    (ht : IsSMulRegular M t) (hq : IsWeaklyRegular (QuotSMulTop t M) qs)
    (hmax : ∀ r ∈ t :: qs, r ∈ IsLocalRing.maximalIdeal R) :
    IsWeaklyRegular M qs := by
  have h1 : IsWeaklyRegular M (qs ++ [t]) :=
    IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal (cons_regular ht hq)
      (List.perm_append_singleton t qs).symm hmax
  exact ((isWeaklyRegular_append_iff M qs [t]).mp h1).1

/-- **Step 3.** Flat base change: the lifted sequence stays weakly regular on `M₂ ⊗ M` for any
flat `M₂` (for `ℤ₍₃₎ → ℚ`). -/
theorem regular_of_lift_flat [IsNoetherian R M] {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [Module.Flat R M₂] {t : R} {qs : List R} (ht : IsSMulRegular M t)
    (hq : IsWeaklyRegular (QuotSMulTop t M) qs)
    (hjac : ∀ r ∈ t :: qs, r ∈ (Module.annihilator R M).jacobson) :
    IsWeaklyRegular (TensorProduct R M₂ M) qs :=
  (regular_of_lift ht hq hjac).isWeaklyRegular_lTensor

end Brent.CM.Lift
