import Brent.Census.Minors
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra

/-!
# Task 1 (F18): matrix rank is invariant under field extension

DRAFT, NOT YET COMPILED. (Revision 2: the first version used tensor-product lemma names that do
not exist at the pinned Mathlib; this one goes through minors.)

The census computes ranks of integer matrices over `ℚ` and `ZMod 3`. The goal requires every
field of characteristic 3 or 0. Every field of characteristic 0 is a `ℚ`-algebra and every field
of characteristic 3 is a `ZMod 3`-algebra, so it suffices that the rank of a matrix does not
change under a field extension `F → K` (`rank_map_algebraMap`).

Proof: `rank ≤ r` iff every `(r + 1)`-minor vanishes (`Minors.rank_le_iff_minors`), and a minor
of the mapped matrix is the image of the minor under the injective map `F → K`.
-/

namespace Brent.Census.FieldTransfer

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- **Rank is invariant under field extension.** -/
theorem rank_map_algebraMap (M : Matrix m n F) :
    (M.map (algebraMap F K)).rank = M.rank := by
  have key : ∀ r, (M.map (algebraMap F K)).rank ≤ r ↔ M.rank ≤ r := by
    intro r
    rw [Minors.rank_le_iff_minors, Minors.rank_le_iff_minors]
    refine forall_congr' fun f => forall_congr' fun g => ?_
    have hdet : ((M.map (algebraMap F K)).submatrix f g).det =
        algebraMap F K (M.submatrix f g).det := by
      rw [RingHom.map_det]
      rfl
    rw [hdet, map_eq_zero_iff _ (algebraMap F K).injective]
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

/-- An integer matrix has the same rank in every field of characteristic zero as over `ℚ`. -/
theorem rank_intCast_charZero (K : Type*) [Field K] [CharZero K] (M : Matrix m n ℤ) :
    (M.map (Int.cast : ℤ → K)).rank = (M.map (Int.cast : ℤ → ℚ)).rank := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  rw [← rank_map_algebraMap (K := K) (M.map (Int.cast : ℤ → ℚ)), Matrix.map_map]
  congr 1
  ext i j
  simp

/-- An integer matrix has the same rank in every field of characteristic three as over `ZMod 3`. -/
theorem rank_intCast_charThree (K : Type*) [Field K] [CharP K 3] (M : Matrix m n ℤ) :
    (M.map (Int.cast : ℤ → K)).rank = (M.map (Int.cast : ℤ → ZMod 3)).rank := by
  letI : Algebra (ZMod 3) K := ZMod.algebra K 3
  rw [← rank_map_algebraMap (K := K) (M.map (Int.cast : ℤ → ZMod 3)), Matrix.map_map]
  congr 1
  ext i j
  simp

/-- **Both characteristics at once**: a rank computed over `ℚ` and over `ZMod 3` holds in every
field of characteristic three or zero. -/
theorem rank_intCast_eq (K : Type*) [Field K] (hK : CharP K 3 ∨ CharZero K) (M : Matrix m n ℤ)
    (r : ℕ) (hQ : (M.map (Int.cast : ℤ → ℚ)).rank = r)
    (h3 : (M.map (Int.cast : ℤ → ZMod 3)).rank = r) :
    (M.map (Int.cast : ℤ → K)).rank = r := by
  rcases hK with hK | hK
  · rw [rank_intCast_charThree K M, h3]
  · rw [rank_intCast_charZero K M, hQ]

end Brent.Census.FieldTransfer
