import Brent.Formal.ReducedTangent
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The reduced variety is singular at Strassen-square

The reduced local ring `A_red` at the recursive point has embedding dimension 251 (F8) and
Krull dimension at most 197 (the upper bound, unchanged by passing to the reduction). A regular
local ring has embedding dimension equal to its Krull dimension. Hence `A_red` is not regular.
-/

namespace Brent.Formal

open IsLocalRing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

variable (k : Type) [Field k]

instance : IsNoetherianRing (Ared k) := inferInstance

theorem ringKrullDim_Ared : ringKrullDim (Ared k) = ringKrullDim (Aalg k) :=
  quotient_dimension_of_le_nilradical _ le_rfl

/-- Any family generating the maximal ideal of `A_red` has at least 251 members. -/
theorem le_card_of_span_eq {n : ℕ} (z : Fin n → Ared k)
    (hspan : Ideal.span (Set.range z) = maximalIdeal (Ared k)) : 251 ≤ n := by
  have hz : ∀ i, z i ∈ maximalIdeal (Ared k) := fun i => by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hgen : maximalIdeal (Ared k) ≤ Ideal.span (Set.range z) ⊔ maximalIdeal (Ared k) ^ 2 := by
    rw [hspan]
    exact le_sup_left
  obtain ⟨_, hle⟩ := hilbertValue_le_of_le_span _ (gradedPiece_one_le_span (residueRed k) z hz hgen)
  rwa [hilbertValue_reduced_one] at hle

/-- **The embedding dimension of `A_red` is at least 251.** Any generating set of the maximal
ideal spans the cotangent space `𝔪 ⧸ 𝔪²`, which has dimension 251. -/
theorem le_spanFinrank_maximalIdeal_Ared : 251 ≤ (maximalIdeal (Ared k)).spanFinrank := by
  have hfg : (maximalIdeal (Ared k)).FG := IsNoetherian.noetherian _
  obtain ⟨S, hcard, hspan⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  have hfin : S.Finite := Set.finite_of_encard_eq_coe hcard
  let t := hfin.toFinset
  have hrange : Set.range (fun i => ((t.equivFin.symm i : t) : Ared k)) = S := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (Set.Finite.mem_toFinset hfin).mp (t.equivFin.symm i).2
    · intro ha
      refine ⟨t.equivFin ⟨a, (Set.Finite.mem_toFinset hfin).mpr ha⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
  have h := le_card_of_span_eq k _ (by rw [hrange]; exact hspan)
  have h2 : (t.card : ℕ∞) = (maximalIdeal (Ared k)).spanFinrank := by
    rw [← hcard, ← hfin.cast_ncard_eq, Set.ncard_eq_toFinset_card S hfin]
  exact h.trans (le_of_eq (by exact_mod_cast h2))

/-- **The embedding dimension exceeds the dimension bound.** -/
theorem not_regular_of_dim_le (hdim : ringKrullDim (Aalg k) ≤ 197) :
    ¬ IsRegularLocalRing (Ared k) := by
  intro hreg
  have h := hreg.spanFinrank_maximalIdeal
  rw [ringKrullDim_Ared] at h
  have h251 := le_spanFinrank_maximalIdeal_Ared k
  have : ((maximalIdeal (Ared k)).spanFinrank : WithBot ℕ∞) ≤ 197 := h ▸ hdim
  have : (maximalIdeal (Ared k)).spanFinrank ≤ 197 := by exact_mod_cast this
  omega

/-- **The reduced Brent variety is singular at Strassen-square (characteristic three).** -/
theorem not_isRegularLocalRing_Ared_charThree [CharP k 3] : ¬ IsRegularLocalRing (Ared k) :=
  not_regular_of_dim_le k (UpperBound.ringKrullDim_le k)

/-- **The reduced Brent variety is singular at Strassen-square (characteristic zero).** -/
theorem not_isRegularLocalRing_Ared_charZero [CharZero k] : ¬ IsRegularLocalRing (Ared k) :=
  not_regular_of_dim_le k (CharZeroBound.ringKrullDim_le k)

end Brent.Formal
