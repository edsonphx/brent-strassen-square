import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.CharP.Algebra

/-!
# Task 1 (F18): matrix rank is invariant under field extension

DRAFT, NOT YET COMPILED.

The census computes ranks of integer matrices over `ℚ` and `ZMod 3`. The paper's statement
("over both ℚ and 𝔽₃") is meant for the two characteristics, and the goal requires every
field of characteristic 3 or 0. Every field of characteristic 0 is a `ℚ`-algebra and every
field of characteristic 3 is a `ZMod 3`-algebra, so it suffices that the rank of a matrix does
not change under a field extension `F → K` (`rank_map_algebraMap`). For an integer matrix this
gives `rank_intCast_charZero` and `rank_intCast_charThree`.

Proof: `K ⊗_F (n → F) ≃ (n → K)` (`TensorProduct.piScalarRight`) carries `M.mulVecLin.baseChange K`
to `(M.map (algebraMap F K)).mulVecLin`. The range of a base change is the base change of the
range, which has the same dimension because `K` is flat over the field `F`
(`Module.finrank_baseChange`).
-/

open TensorProduct

namespace Brent.Census.FieldTransfer

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The square that relates the base-changed linear map to the mapped matrix. -/
theorem mulVecLin_map_comp (M : Matrix m n F) :
    (M.map (algebraMap F K)).mulVecLin ∘ₗ (piScalarRight F K K n).toLinearMap =
      (piScalarRight F K K m).toLinearMap ∘ₗ (M.mulVecLin.baseChange K) := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext x j i
  simp [piScalarRight_tmul, Matrix.mulVec, dotProduct, Pi.single_apply, Algebra.smul_def,
    mul_comm]

/-- The range of the base change of `f` has the dimension of the range of `f`. -/
theorem finrank_range_baseChange {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V] (f : V →ₗ[F] W) :
    Module.finrank K (LinearMap.range (f.baseChange K)) = Module.finrank F (LinearMap.range f) := by
  -- `f = ι ∘ f'` with `f'` onto the range and `ι` injective.
  set ι := (LinearMap.range f).subtype
  set f' := f.rangeRestrict
  have hf : f = ι ∘ₗ f' := (LinearMap.range f).subtype_comp_codRestrict f _ |>.symm
  have hι : Function.Injective (ι.baseChange K) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι (Submodule.injective_subtype _)
  have hf' : Function.Surjective (f'.baseChange K) :=
    LinearMap.lTensor_surjective K (LinearMap.surjective_rangeRestrict f)
  have hrange : LinearMap.range (f.baseChange K) = LinearMap.range (ι.baseChange K) := by
    rw [hf, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr hf')]
  rw [hrange, LinearMap.finrank_range_of_inj hι, Module.finrank_baseChange]

/-- **Rank is invariant under field extension.** -/
theorem rank_map_algebraMap (M : Matrix m n F) :
    (M.map (algebraMap F K)).rank = M.rank := by
  unfold Matrix.rank
  have h := congrArg LinearMap.range (mulVecLin_map_comp (K := K) M)
  rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top] at h
  rw [h, LinearEquiv.finrank_map_eq, finrank_range_baseChange]

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
