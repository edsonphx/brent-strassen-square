import Brent.HilbertFunction
import Brent.KernelCheck.CharZero
import Mathlib.Algebra.DualNumber

/-!
# The Hilbert values `H(0) = 1` and `H(1) = 251`

Every tangent vector `v` (with `J v = 0`) gives a first-order jet `A → k[ε]`, sending
`g ↦ g(p + ε v)`. The constant part is the residue map, and the `ε`-parts of the 251 frame
jets are linear functionals that vanish on `𝔪²` and separate the classes of the
coordinates. Together with the 251 generators `zᵢ`, this gives `dim 𝔪/𝔪² = 251`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.HilbertInitial

open TangentData QuadraticData CharThree UpperBound

variable (k : Type) [Field k]

theorem dual_mul_eq_zero {u w : DualNumber k} (hu : u.fst = 0) (hw : w.fst = 0) : u * w = 0 :=
  TrivSqZeroExt.ext (by simp [hu]) (by simp [hu, hw])

variable (v : Variable SquareVertex SquareSummand → k)

/-- Evaluation at `p + ε v`. -/
noncomputable def polyJet : MvPolynomial (Variable SquareVertex SquareSummand) k →ₐ[k] DualNumber k :=
  aeval fun x => algebraMap k (DualNumber k) ((strassenSquare k).coordinates x) + v x • DualNumber.eps

theorem fst_polyJet (g : MvPolynomial (Variable SquareVertex SquareSummand) k) :
    (polyJet k v g).fst = eval (strassenSquare k).coordinates g := by
  have h : (TrivSqZeroExt.fstHom k k k).comp (polyJet k v) =
      aeval (strassenSquare k).coordinates := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [polyJet, TrivSqZeroExt.algebraMap_eq_inl]
  have := congrArg (fun f => f g) h
  simpa [coe_aeval_eq_eval] using this

theorem polyJet_lin (x : Variable SquareVertex SquareSummand) :
    polyJet k v (X x - C ((strassenSquare k).coordinates x)) = v x • DualNumber.eps := by
  rw [map_sub, polyJet, aeval_X, aeval_C, add_sub_cancel_left]

theorem fst_polyJet_of_mem {g : MvPolynomial (Variable SquareVertex SquareSummand) k}
    (hg : g ∈ M0 k) : (polyJet k v g).fst = 0 := by
  rw [fst_polyJet]; exact hg

theorem polyJet_sq {g : MvPolynomial (Variable SquareVertex SquareSummand) k}
    (hg : g ∈ M0 k ^ 2) : polyJet k v g = 0 := by
  have hle : M0 k ^ 2 ≤ RingHom.ker (polyJet k v) := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    rw [RingHom.mem_ker, map_mul]
    exact dual_mul_eq_zero k (fst_polyJet_of_mem k v ha) (fst_polyJet_of_mem k v hb)
  exact hle hg

variable (hv : ∀ e : EquationIndex SquareVertex, ∑ x, J k x e * v x = 0)
include hv

theorem polyJet_brent : brentIdeal k SquareVertex SquareSummand ≤ RingHom.ker (polyJet k v) := by
  rw [brentIdeal, Ideal.span_le]
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  have h := Decomposition.equation_eq_expansion (strassenSquare_solves k) a b c
  change polyJet k v (equation k SquareVertex SquareSummand a b c) = 0
  rw [h, map_add, map_add, polyJet_sq k v (quad_mem k (a, b, c)),
    polyJet_sq k v (Ideal.pow_le_pow_right (by norm_num) (cubic_mem k (a, b, c))), add_zero,
    add_zero, jac_poly k (a, b, c), map_sum]
  have e : ∀ x, polyJet k v ((X x - C ((strassenSquare k).coordinates x)) * C (J k x (a, b, c))) =
      (J k x (a, b, c) * v x) • DualNumber.eps := by
    intro x
    rw [map_mul, polyJet_lin, polyJet, aeval_C, TrivSqZeroExt.algebraMap_eq_inl, mul_comm,
      mul_smul]
    ext <;> simp [mul_comm]
  simp only [e, ← Finset.sum_smul, hv (a, b, c), zero_smul]

/-- The jet on the coordinate ring. -/
noncomputable def quotJet :
    CoordinateRing k SquareVertex SquareSummand →ₐ[k] DualNumber k :=
  Ideal.Quotient.liftₐ (brentIdeal k SquareVertex SquareSummand) (polyJet k v)
    fun g hg => polyJet_brent k v hv hg

theorem quotJet_unit (s : (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl) :
    IsUnit (quotJet k v hv s) := by
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (s : CoordinateRing k SquareVertex SquareSummand)
  have hs := s.2
  rw [← hg] at hs ⊢
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
  intro h0
  apply hs
  change pointEvaluation (strassenSquare k) (strassenSquare_solves k) (Ideal.Quotient.mk _ g) = 0
  rw [quotJet, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at h0
  rw [pointEvaluation, Ideal.Quotient.lift_mk, ← fst_polyJet k v g]
  exact h0

/-- The jet on the local ring. -/
noncomputable def localJet : A k →ₐ[k] DualNumber k :=
  IsLocalization.liftAlgHom (M := (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl)
    (f := quotJet k v hv) (quotJet_unit k v hv)

theorem localJet_φ (g : MvPolynomial (Variable SquareVertex SquareSummand) k) :
    localJet k v hv (φ k g) = polyJet k v g := by
  rw [localJet, IsLocalization.liftAlgHom_apply, φ, toPointLocalRing_apply, IsLocalization.lift_eq]
  rfl

theorem localJet_y (x : Variable SquareVertex SquareSummand) :
    localJet k v hv (y k x) = v x • DualNumber.eps := by
  rw [y, localJet_φ, polyJet_lin]

theorem fst_localJet_of_mem {a : A k} (ha : a ∈ maximalIdeal (A k)) :
    (localJet k v hv a).fst = 0 := by
  have hle : maximalIdeal (A k) ≤
      RingHom.ker ((TrivSqZeroExt.fstHom k k k).comp (localJet k v hv)).toRingHom := by
    rw [maximalIdeal_eq, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    simp [localJet_y]
  exact hle ha

theorem localJet_sq {a : A k} (ha : a ∈ maximalIdeal (A k) ^ 2) : localJet k v hv a = 0 := by
  have hle : maximalIdeal (A k) ^ 2 ≤ RingHom.ker (localJet k v hv).toRingHom := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    rw [RingHom.mem_ker, map_mul]
    exact dual_mul_eq_zero k (fst_localJet_of_mem k v hv ha) (fst_localJet_of_mem k v hv hb)
  exact hle ha

omit hv

theorem zero_tangent : ∀ e : EquationIndex SquareVertex, ∑ x, J k x e * (0 : Variable SquareVertex SquareSummand → k) x = 0 :=
  fun e => by simp

theorem frame_tangent (i : Fin 251) :
    ∀ e : EquationIndex SquareVertex, ∑ x, J k x e * frameVec k i x = 0 := fun e => by
  rw [← frame_orthogonal k i e]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The residue map. -/
noncomputable def residue : A k →ₐ[k] k :=
  (TrivSqZeroExt.fstHom k k k).comp (localJet k 0 (zero_tangent k))

/-- The 251 frame derivatives. -/
noncomputable def frameDerivative : A k →ₗ[k] (Fin 251 → k) :=
  LinearMap.pi fun i =>
    (TrivSqZeroExt.sndHom k k).comp (localJet k (frameVec k i) (frame_tangent k i)).toLinearMap

theorem frameDerivative_sq {a : A k} (ha : a ∈ maximalIdeal (A k) ^ (1 + 1)) :
    frameDerivative k a = 0 := by
  funext i
  simp [frameDerivative, localJet_sq k _ _ ha]

theorem frameDerivative_y (x : Variable SquareVertex SquareSummand) :
    frameDerivative k (y k x) = fun i => frameVec k i x := by
  funext i
  simp [frameDerivative, localJet_y]

theorem frame_columns_span :
    Submodule.span k (Set.range fun x : Variable SquareVertex SquareSummand =>
      fun i : Fin 251 => frameVec k i x) = ⊤ := by
  let Mat : Matrix (Fin 251) (Variable SquareVertex SquareSummand) k := fun i x => frameVec k i x
  have hrow : Mat.rank = 251 := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank k (Submodule.span k (Set.range (frameVec k))) = 251
    rw [finrank_span_eq_card (frame_independent k), Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_cols] at hrow
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  exact hrow

/-- **Hilbert value in degree zero.** -/
theorem hilbertValue_zero : hilbertValue k (A k) 0 = 1 :=
  Brent.hilbertValue_zero (residue k)

/-- **Hilbert value in degree one.** The tangent space has dimension 251. -/
theorem hilbertValue_one : hilbertValue k (A k) 1 = 251 := by
  obtain ⟨hfin, hle⟩ := hilbertValue_le_of_le_span _
    (gradedPiece_one_le_span (residue k) (z k) (z_mem k) (CharZeroBound.gen_z k))
  haveI := hfin
  refine le_antisymm hle (le_hilbertValue (frameDerivative k) (fun a ha => frameDerivative_sq k ha)
    (y k) (fun x => by rw [pow_one]; exact y_mem k x) ?_)
  simp only [frameDerivative_y]
  exact frame_columns_span k

end Brent.HilbertInitial
