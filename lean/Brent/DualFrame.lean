import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinates dual to a tangent frame

If `v₁,…,vₙ` are independent vectors orthogonal to a row space `R` of complementary
dimension, then there are vectors `wᵢ` with `e_x - Σᵢ vᵢ(x) wᵢ ∈ R` for every
coordinate `x`. Applied to the Jacobian row space and the 251 certified frame vectors,
this gives tangent coordinates `zᵢ` with `y_x ≡ Σᵢ vᵢ(x) zᵢ` modulo `𝔪²`.
-/

open scoped BigOperators

namespace Brent

theorem exists_dual_frame {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] {n : ℕ}
    (R : Submodule k (ι → k)) (v : Fin n → ι → k) (hv : LinearIndependent k v)
    (horth : ∀ r ∈ R, ∀ i, ∑ x, v i x * r x = 0)
    (hdim : Module.finrank k R + n = Fintype.card ι) :
    ∃ w : Fin n → ι → k, ∀ x, Pi.single x 1 - ∑ i, v i x • w i ∈ R := by
  let V : Matrix (Fin n) ι k := v
  have hrank : V.rank = n := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact (finrank_span_eq_card hv).trans (Fintype.card_fin n)
  have hsurj : Function.Surjective V.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  have hker : Module.finrank k (LinearMap.ker V.mulVecLin) + n = Fintype.card ι := by
    have h := V.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_fintype_fun_eq_card] at h
    change V.rank + _ = _ at h
    omega
  have hle : R ≤ LinearMap.ker V.mulVecLin := by
    intro r hr
    rw [LinearMap.mem_ker]
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact horth r hr i
  have heq : R = LinearMap.ker V.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  choose w hw using fun i : Fin n => hsurj (Pi.single i 1)
  refine ⟨w, fun x => ?_⟩
  rw [heq, LinearMap.mem_ker, map_sub, map_sum]
  funext j
  simp only [map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, hw, smul_eq_mul,
    Pi.zero_apply]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j]
  · simp [V]
  · intro i _ hij; simp [Ne.symm hij]
  · simp

end Brent
