import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation

namespace Brent

/-- The matching in Appendix A.2, with zero-based indices. -/
def quadraticMatching : Fin 54 → Fin 54 :=
  ![19, 2, 31, 1, 5, 48, 50, 30, 28,
    20, 44, 15, 8, 12, 42, 38, 35, 11,
    21, 16, 43, 18, 3, 45, 53, 26, 17,
    52, 7, 39, 22, 34, 36, 49, 40, 13,
    47, 25, 41, 29, 10, 37, 46, 32, 23,
    51, 0, 4, 6, 33, 24, 14, 27, 9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem quadraticMatching_injective : Function.Injective quadraticMatching := by
  have h : ∀ i j : Fin 54, quadraticMatching i = quadraticMatching j → i = j := by decide
  exact fun _ _ => h _ _

theorem quadraticMatching_bijective : Function.Bijective quadraticMatching :=
  ⟨quadraticMatching_injective,
    Finite.injective_iff_surjective.mp quadraticMatching_injective⟩

/-- The proposed leading supports use disjoint pairs of variables. -/
theorem quadraticMatching_disjoint :
    ∀ ⦃i j : Fin 54⦄, i ≠ j →
      Disjoint ({Sum.inl i, Sum.inr (quadraticMatching i)} : Set (Fin 54 ⊕ Fin 54))
        {Sum.inl j, Sum.inr (quadraticMatching j)} := by
  intro i j hij
  have hright : quadraticMatching i ≠ quadraticMatching j :=
    fun he => hij (quadraticMatching_injective he)
  simp [Set.disjoint_left, hij, hright]

end Brent
