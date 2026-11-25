import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi

open scoped BigOperators

namespace Brent

section RowSpan
variable {K κ : Type*} [Field K] {n : ℕ}

/-- Subtracting earlier reduced rows leaves the span unchanged, even when
a reduced row is zero. The earlier-row predicate is part of the certificate
soundness condition. -/
theorem rowSpan_eq_of_elimination (original reduced : Fin n → (κ → K))
    (factor : Fin n → Fin n → K)
    (step : ∀ i, reduced i = original i -
      ∑ j ∈ Finset.univ.filter (· < i), factor i j • reduced j) :
    Submodule.span K (Set.range original) = Submodule.span K (Set.range reduced) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : original i = reduced i +
        (∑ j ∈ Finset.univ.filter (· < i), factor i j • reduced j) := by rw [step i, sub_add_cancel]
    rw [hi]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  · rw [Submodule.span_le]
    have h : ∀ i, reduced i ∈ Submodule.span K (Set.range original) := by
      intro i
      induction i using WellFoundedLT.induction with
      | ind i ih =>
        rw [step i]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
          (Submodule.sum_mem _ fun j hj =>
            Submodule.smul_mem _ _ (ih j (Finset.mem_filter.mp hj).2))
    rintro _ ⟨i, rfl⟩
    exact h i

/-- Evaluating the rows at ordered pivot coordinates certifies independence
when the resulting matrix is triangular with nonzero diagonal. -/
theorem linearIndependent_of_pivots {r : ℕ} (rows : Fin r → κ → K)
    (pivot : Fin r → κ) (diag : ∀ i, rows i (pivot i) ≠ 0)
    (zero : ∀ i j, j < i → rows i (pivot j) = 0) :
    LinearIndependent K rows := by
  let M : Matrix (Fin r) (Fin r) K := fun i j => rows i (pivot j)
  have hM : M.BlockTriangular id := fun i j h => zero i j h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hM]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => diag i)
  let restrict : (κ → K) →ₗ[K] (Fin r → K) :=
    { toFun := fun f i => f (pivot i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp restrict (Matrix.linearIndependent_rows_of_det_ne_zero hdet)

end RowSpan
end Brent
