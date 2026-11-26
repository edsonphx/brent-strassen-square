import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Regular.SMul

/-!
# The Hilbert–Samuel function drops along a regular element (roadmap step B, second part)

DRAFT, NOT YET COMPILED.

For a Noetherian ring `B`, an ideal `m` and an element `x` that is regular on `B`, the Artin–Rees
lemma gives `c` with `(mⁿ : x) ⊆ m^(n−c)` for `n ≥ c`, and then

`length (B ⧸ m^(n − c)) + length (B ⧸ ((x) + mⁿ)) ≤ length (B ⧸ mⁿ)`.

This is the inequality `χ_{B/x}(n) ≤ χ_B(n) − χ_B(n − c)` behind `dim A ≤ d(A)`: with
`χ_B` of polynomial type of order `≤ e + 1` (`Brent.CM.PolyType`), `χ_{B/x}` has order `≤ e`
(`Brent.CM.orderLE_of_sub_shift`). Lengths are in `ℕ∞`, so no finiteness hypothesis is needed.

Imports Mathlib only.
-/

namespace Brent.CM

open Ideal

variable {B : Type*} [CommRing B] [IsNoetherianRing B]

/-- **Artin–Rees for a principal ideal.** If `x` is regular, then `(mⁿ : x) ⊆ m^(n − c)` for some
`c` and all `n ≥ c`. -/
theorem exists_colon_pow_le (m : Ideal B) {x : B} (hx : IsSMulRegular B x) :
    ∃ c, ∀ n ≥ c, ∀ y : B, x * y ∈ m ^ n → y ∈ m ^ (n - c) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul m (M := B) (span {x} : Submodule B B)
  refine ⟨c, fun n hn y hy => ?_⟩
  have hmem : x * y ∈ (m ^ n • ⊤ ⊓ span {x} : Submodule B B) := by
    refine ⟨?_, Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x)⟩
    show x * y ∈ (m ^ n • (⊤ : Ideal B))
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hy
  rw [hc n hn] at hmem
  have hle : (m ^ (n - c) • (m ^ c • ⊤ ⊓ span {x}) : Submodule B B) ≤
      (m ^ (n - c) • (span {x} : Ideal B) : Submodule B B) :=
    Submodule.smul_mono le_rfl inf_le_right
  have h2 : x * y ∈ span {x} * m ^ (n - c) := by
    have := hle hmem
    rw [Ideal.smul_eq_mul, mul_comm (m ^ (n - c))] at this
    exact this
  obtain ⟨z, hz, hxz⟩ := Ideal.mem_span_singleton_mul.mp h2
  have : z = y := hx (by simpa [smul_eq_mul] using hxz)
  exact this ▸ hz

theorem mul_mem_ker_factor (m : Ideal B) (x : B) (n : ℕ) (y : B) :
    ((Submodule.mkQ (m ^ n)).comp (LinearMap.mulLeft B x)) y ∈
      LinearMap.ker (Submodule.factor (le_sup_right : m ^ n ≤ span {x} ⊔ m ^ n)) := by
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.factor_mk,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_sup_left (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))

/-- Multiplication by `x`, from `B` onto `((x) + mⁿ) ⧸ mⁿ`, the kernel of
`B ⧸ mⁿ → B ⧸ ((x) + mⁿ)`. -/
noncomputable def mulToKer (m : Ideal B) (x : B) (n : ℕ) :
    B →ₗ[B] LinearMap.ker (Submodule.factor (le_sup_right : m ^ n ≤ span {x} ⊔ m ^ n)) :=
  LinearMap.codRestrict _ ((Submodule.mkQ (m ^ n)).comp (LinearMap.mulLeft B x))
    (mul_mem_ker_factor m x n)

theorem mulToKer_surjective (m : Ideal B) (x : B) (n : ℕ) :
    Function.Surjective (mulToKer m x n) := by
  rintro ⟨q, hq⟩
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [LinearMap.mem_ker, Submodule.factor_mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_sup] at hq
  obtain ⟨u, hu, v, hv, rfl⟩ := hq
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  refine ⟨y, Subtype.ext ?_⟩
  simp only [mulToKer, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have : x * y - (y * x + v) = -v := by ring
  rw [this]
  exact Submodule.neg_mem _ hv

theorem ker_mulToKer_le (m : Ideal B) {x : B} {n c : ℕ}
    (hc : ∀ y : B, x * y ∈ m ^ n → y ∈ m ^ (n - c)) :
    LinearMap.ker (mulToKer m x n) ≤ m ^ (n - c) := by
  intro y hy
  rw [mulToKer, LinearMap.ker_codRestrict, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  exact hc y hy

/-- **The Hilbert–Samuel function drops along a regular element.** For `x` regular on the
Noetherian ring `B` there is `c` with, for all `n ≥ c`,
`length (B ⧸ m^(n − c)) + length (B ⧸ ((x) + mⁿ)) ≤ length (B ⧸ mⁿ)`. -/
theorem length_quot_add_le (m : Ideal B) {x : B} (hx : IsSMulRegular B x) :
    ∃ c, ∀ n ≥ c,
      Module.length B (B ⧸ m ^ (n - c)) + Module.length B (B ⧸ (span {x} ⊔ m ^ n)) ≤
        Module.length B (B ⧸ m ^ n) := by
  obtain ⟨c, hc⟩ := exists_colon_pow_le m hx
  refine ⟨c, fun n hn => ?_⟩
  set g := Submodule.factor (le_sup_right : m ^ n ≤ span {x} ⊔ m ^ n)
  have hexact := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _) (Submodule.factor_surjective _)
    (LinearMap.exact_subtype_ker_map g)
  rw [hexact]
  gcongr
  -- `length (B ⧸ m^(n−c)) ≤ length (B ⧸ ker) = length (ker g)`
  have e := (mulToKer m x n).quotKerEquivOfSurjective (mulToKer_surjective m x n)
  rw [← e.length_eq]
  exact Module.length_le_of_surjective
    (Submodule.factor (ker_mulToKer_le m (hc n hn)))
    (Submodule.factor_surjective _)

end Brent.CM
