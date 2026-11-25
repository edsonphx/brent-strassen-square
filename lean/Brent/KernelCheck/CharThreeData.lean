import Brent.QuadraticExpansion
import Brent.EmbeddingDimension
import Brent.KernelCheck.FamilyQuadratics
import Brent.KernelCheck.SquareJacobianRank

/-!
# The certified data over an arbitrary field of characteristic three

The covectors and the quadratic coefficient tables are certified over `ZMod 3`, and the
tangent frame over `ℤ`. This file transports them to any field `k` of characteristic three.
-/

open scoped BigOperators

namespace Brent.CharThree

open TangentData QuadraticData

theorem Decomposition.map_map' {R S T α ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (d : Decomposition R α ι) :
    (d.map f).map g = d.map (g.comp f) := rfl

theorem polarizedEntry_map {R S α ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    (f : R →+* S) (p x y : Decomposition R α ι) (a b c : α × α) :
    (p.map f).polarizedEntry (x.map f) (y.map f) a b c = f (p.polarizedEntry x y a b c) := by
  rw [Decomposition.polarizedEntry_eq_bilinear, Decomposition.polarizedEntry_eq_bilinear,
    Decomposition.bilinearEntry_map, Decomposition.bilinearEntry_map, map_add]

variable (k : Type) [Field k] [CharP k 3]

noncomputable def castK : ZMod 3 →+* k := ZMod.castHom (dvd_refl 3) k

theorem castK_comp_int : (castK k).comp (Int.castRingHom (ZMod 3)) = Int.castRingHom k :=
  RingHom.ext_int _ _

theorem strassenSquare_map : (strassenSquare (ZMod 3)).map (castK k) = strassenSquare k := by
  rw [strassenSquare, strassenSquare, Decomposition.map_map', castK_comp_int]

theorem frameDirection_map (i : Fin 251) :
    (frameDirection (ZMod 3) i).map (castK k) = frameDirection k i := by
  apply Decomposition.eq_of_components <;> funext s a <;>
    simp [frameDirection, Decomposition.map]

/-- The certified covectors over `k`. -/
noncomputable def lam (ell : Fin 54) (e : EquationIndex SquareVertex) : k :=
  castK k (functionalEntry ell (squareEquationNumber e))

/-- The tangent frame over `k`, as functions of the variables. -/
noncomputable def frameVec (i : Fin 251) : Variable SquareVertex SquareSummand → k :=
  (frameDirection k i).coordinates

theorem annihilate (ell : Fin 54) (x : Variable SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex,
      (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2 * lam k ell e = 0 := by
  have h := congrArg (castK k) (archived_covectors_annihilate ell x)
  rw [map_sum, map_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_mul, ← Decomposition.jacobianColumn_map, strassenSquare_map]
  rfl

theorem polar_value (ell : Fin 54) (i j : Fin 251) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare k).polarizedEntry
      (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2 * lam k ell e =
      castK k (projectedPolar ell i j) := by
  rw [projectedPolar, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_mul, ← polarizedEntry_map, strassenSquare_map, frameDirection_map, frameDirection_map]
  rfl

theorem square_value (ell : Fin 54) (i : Fin 251) :
    ∑ e : EquationIndex SquareVertex, (strassenSquare k).quadraticEntry
      (frameDirection k i) e.1 e.2.1 e.2.2 * lam k ell e = 0 := by
  have h := congrArg (castK k) (archived_square_zero ell i)
  rw [map_sum, map_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_mul, Decomposition.quadraticEntry_eq_bilinear, Decomposition.quadraticEntry_eq_bilinear,
    ← Decomposition.bilinearEntry_map, strassenSquare_map, frameDirection_map]
  rfl

/-- The row space of the Jacobian over `k`. -/
noncomputable def rowSpace : Submodule k (Variable SquareVertex SquareSummand → k) :=
  Submodule.span k (Set.range fun e : EquationIndex SquareVertex =>
    fun x => (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2)

omit [CharP k 3] in
theorem rowSpace_finrank : Module.finrank k (rowSpace k) = 2101 := by
  let Mat : Matrix (Variable SquareVertex SquareSummand) (EquationIndex SquareVertex) k :=
    fun x e => (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2
  have h1 := Mat.rank_eq_finrank_span_cols
  have h2 := Mat.rank_eq_finrank_span_row
  rw [← square_jacobian_rank k]
  exact h1.symm.trans h2

omit [CharP k 3] in
theorem frame_orthogonal (i : Fin 251) (e : EquationIndex SquareVertex) :
    ∑ x, frameVec k i x * (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2 = 0 := by
  have h := congrArg (Int.castRingHom k) (archived_frame_tangent i e)
  rw [map_sum, map_zero] at h
  rw [← squareVariableNumber.symm.sum_comp]
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, frameVec, frameDirection_coordinates, Equiv.apply_symm_apply,
    ← Decomposition.jacobianColumn_map, eq_intCast]
  rfl

omit [CharP k 3] in
theorem frame_independent : LinearIndependent k (frameVec k) := by
  have full : LinearIndependent k (fun i : Fin 251 =>
      SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i)) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin 251) = Module.finrank k (Submodule.span k
      (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i))))
    rw [archived_frame_rank, Fintype.card_fin]
  let L : (Fin 2352 → k) →ₗ[k] (Variable SquareVertex SquareSummand → k) :=
    (LinearEquiv.funCongrLeft k k squareVariableNumber).toLinearMap
  have hL := full.map' L (LinearEquiv.ker _)
  convert hL using 1
  funext i x
  simp [L, frameVec, frameDirection_coordinates, SparseRow.decode, LinearEquiv.funCongrLeft_apply]

end Brent.CharThree
