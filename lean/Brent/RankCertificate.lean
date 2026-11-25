import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Brent.SparseRow

open scoped BigOperators

namespace Brent

section RowSpan
variable {K κ : Type*} [Field K] {n : ℕ}

/-- Subtracting earlier reduced rows leaves the span unchanged, even when
a reduced row is zero. The earlier-row predicate is part of the certificate
soundness condition. -/
theorem rowSpan_eq_of_elimination (original reduced : Fin n → (κ → K))
    (steps : Fin n → List (Fin n × K))
    (earlier : ∀ i, ∀ a ∈ steps i, a.1 < i)
    (step : ∀ i, reduced i = original i -
      ((steps i).map fun (j, a) => a • reduced j).sum) :
    Submodule.span K (Set.range original) = Submodule.span K (Set.range reduced) := by
  have sum_mem (S : Submodule K (κ → K)) (i : Fin n)
      (h : ∀ a ∈ steps i, reduced a.1 ∈ S) :
      ((steps i).map fun (j, a) => a • reduced j).sum ∈ S := by
    apply list_sum_mem
    intro v hmem
    obtain ⟨⟨j, a⟩, ha, rfl⟩ := List.mem_map.mp hmem
    exact S.smul_mem a (h _ ha)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : original i = reduced i +
        ((steps i).map fun (j, a) => a • reduced j).sum := by rw [step i, sub_add_cancel]
    rw [hi]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      (sum_mem _ i fun a _ => Submodule.subset_span ⟨a.1, rfl⟩)
  · rw [Submodule.span_le]
    have h : ∀ i, reduced i ∈ Submodule.span K (Set.range original) := by
      intro i
      induction i using WellFoundedLT.induction with
      | ind i ih =>
        rw [step i]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
          (sum_mem _ i fun a ha => ih a.1 (earlier i a ha))
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

/-- The exact row rank, given a checked elimination and its nonzero pivots. -/
theorem rowRank_eq_of_elimination {r : ℕ}
    (original reduced : Fin n → (κ → K))
    (steps : Fin n → List (Fin n × K))
    (earlier : ∀ i, ∀ a ∈ steps i, a.1 < i)
    (step : ∀ i, reduced i = original i -
      ((steps i).map fun (j, a) => a • reduced j).sum)
    (select : Fin r → Fin n) (pivot : Fin r → κ)
    (diag : ∀ i, reduced (select i) (pivot i) ≠ 0)
    (zero : ∀ i j, j < i → reduced (select i) (pivot j) = 0)
    (cover : ∀ i, reduced i = 0 ∨ ∃ j, select j = i) :
    Module.finrank K (Submodule.span K (Set.range original)) = r := by
  rw [rowSpan_eq_of_elimination original reduced steps earlier step]
  have hspan : Submodule.span K (Set.range reduced) =
      Submodule.span K (Set.range (reduced ∘ select)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain h | ⟨j, rfl⟩ := cover i
      · rw [h]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨j, rfl⟩
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨select j, rfl⟩
  rw [hspan]
  exact (finrank_span_eq_card (linearIndependent_of_pivots (reduced ∘ select) pivot diag zero)).trans
    (Fintype.card_fin r)

end RowSpan
end Brent
