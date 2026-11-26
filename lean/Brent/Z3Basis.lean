import Brent.BranchTangents
import Brent.KernelCheck.SquareJacobianRank
import Brent.EmbeddingDimension
import Brent.Census.Minors
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Prime.Int

/-!
# The frozen tangent vectors are a `ℤ₍₃₎`-basis of the kernel (`paper.tex` lines 505–520)

DRAFT, NOT YET COMPILED.

"Thus both kernels are free direct summands and every modular kernel vector lifts to a vector in
the corresponding kernel over `R₀`. The 251 frozen tangent vectors lift a basis modulo 3. Their
coordinate matrix in any `R₀`-basis of the kernel has determinant a unit, so they form an
`R₀`-basis as well."

`R₀ = ℤ₍₃₎ = Localization.AtPrime (span {3})`. `InKer R v` says `J v = 0` over `R`, with the
integer Jacobian `JInt`. Results:

* `kernel_basis_Z3`: the 251 frame vectors are linearly independent over `R₀` and span the
  kernel of `J` over `R₀` (a basis, so the kernel is free).
* `kernel_retract_Z3`: an `R₀`-linear projection onto the kernel, which makes the kernel a direct
  summand.
* `kernel_lift_mod3`: every kernel vector over `𝔽₃` lifts to an integral kernel vector, hence to
  one over `R₀`.

The proof follows the paper: a 251-minor of the frame that is nonzero modulo 3 (it exists because
the frame is independent over `𝔽₃`) is a unit in `R₀`. Over the fraction field the frame spans the
kernel (dimension 251, `square_jacobian_nullity`). Inverting that minor puts the coefficients in
`R₀`.
-/

open scoped BigOperators

namespace Brent.Z3

open Brent Brent.TangentData

abbrev V := Variable SquareVertex SquareSummand
abbrev E := EquationIndex SquareVertex

/-- The integer coordinates of the `i`-th frozen tangent vector. -/
def fInt (i : Fin 251) (x : V) : ℤ := SparseRow.coefficient (squareVariableNumber x).val (frame i)

/-- The integer Jacobian. -/
def JInt (e : E) (x : V) : ℤ := strassenSquareInt.jacobianColumn x e.1 e.2.1 e.2.2

/-- `J v = 0` over `R`. -/
def InKer (R : Type*) [CommRing R] (v : V → R) : Prop := ∀ e, ∑ x, (JInt e x : R) * v x = 0

/-- The frame over `R`. -/
def fR (R : Type*) [CommRing R] (i : Fin 251) : V → R := fun x => (fInt i x : R)

theorem frame_inKer (R : Type*) [CommRing R] (i : Fin 251) : InKer R (fR R i) := by
  intro e
  have h' : ∑ x, fInt i x * JInt e x = 0 :=
    (Fintype.sum_equiv squareVariableNumber _ _ (fun x => by
      simp [fInt, JInt])).trans (archived_frame_tangent i e)
  calc ∑ x, (JInt e x : R) * fR R i x = ((∑ x, fInt i x * JInt e x : ℤ) : R) := by
        push_cast
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ = 0 := by rw [h', Int.cast_zero]

theorem inKer_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {v : V → R}
    (hv : InKer R v) : InKer S (f ∘ v) := by
  intro e
  have := congrArg f (hv e)
  rw [map_sum, map_zero] at this
  simpa only [map_mul, map_intCast, Function.comp_apply] using this

section Field

variable (K : Type*) [Field K]

theorem jacobian_cast (e : E) (x : V) :
    (strassenSquare K).jacobianColumn x e.1 e.2.1 e.2.2 = (JInt e x : K) := by
  rw [JInt, strassenSquare, Decomposition.jacobianColumn_map, eq_intCast]

theorem inKer_iff (v : V → K) : InKer K v ↔ v ∈ LinearMap.ker (squareDifferential K) := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [InKer, squareDifferential, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    jacobian_cast, Pi.zero_apply]

theorem frame_independent_field : LinearIndependent K (fR K) := by
  apply LinearIndependent.of_comp (LinearMap.funLeft K K squareVariableNumber.symm)
  convert frameVec_independent K using 1
  funext i j
  simp [LinearMap.funLeft_apply, fR, fInt, frameVec, SparseRow.decode]

/-- Over every field the frame spans the kernel of `J`. -/
theorem kernel_span_field (v : V → K) (hv : InKer K v) :
    v ∈ Submodule.span K (Set.range (fR K)) := by
  have le : Submodule.span K (Set.range (fR K)) ≤ LinearMap.ker (squareDifferential K) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (inKer_iff K _).mp (frame_inKer K i)
  have eq := Submodule.eq_of_le_of_finrank_eq le (by
    rw [finrank_span_eq_card (frame_independent_field K), Fintype.card_fin,
      square_jacobian_nullity])
  rw [eq]
  exact (inKer_iff K v).mp hv

end Field

/-! ### The abstract argument over a domain with a unit minor -/

section Domain

variable (R : Type*) [CommRing R] [IsDomain R]

/-- The `251 × 251` minor of the frame on the coordinates `S a` and frame indices `g b`. -/
def minorInt (S : Fin 251 → V) (g : Fin 251 → Fin 251) : Matrix (Fin 251) (Fin 251) ℤ :=
  Matrix.of fun a b => fInt (g b) (S a)

theorem span_of_unit_minor (S : Fin 251 → V) (g : Fin 251 → Fin 251)
    (hS : IsUnit ((minorInt S g).map (Int.cast : ℤ → R)).det) (v : V → R) (hv : InKer R v) :
    ∑ b, (((minorInt S g).map (Int.cast : ℤ → R))⁻¹ *ᵥ fun a => v (S a)) b • fR R (g b) = v := by
  classical
  set W := (minorInt S g).map (Int.cast : ℤ → R) with hW
  let K := FractionRing R
  let ι : R →+* K := algebraMap R K
  have hι : Function.Injective ι := IsFractionRing.injective R K
  -- Over `K`, `v` is a combination of the frame.
  obtain ⟨cK, hcK⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (kernel_span_field K (ι ∘ v) (inKer_map ι hv))
  -- Every frame vector is a combination of the reindexed family `g` (because `g` is a bijection
  -- when the minor is a unit; we only need the evaluation at the rows `S`).
  set vS : Fin 251 → R := fun a => v (S a) with hvS
  have WK : IsUnit (W.map ι).det := by
    have h : (W.map ι).det = ι W.det := (RingHom.map_det ι W).symm
    rw [h]
    exact hS.map ι
  -- `W` maps `W⁻¹ vS` to `vS`.
  have hWc : W *ᵥ (W⁻¹ *ᵥ vS) = vS := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hS, Matrix.one_mulVec]
  -- The `K`-coefficients, reindexed by `g`, also solve `W c = vS` over `K`.
  have hg : Function.Injective g := by
    intro b b' hbb'
    by_contra hne
    apply hS.ne_zero
    apply Matrix.det_zero_of_column_eq hne
    intro a
    simp [hW, minorInt, hbb']
  have hgb : Function.Bijective g := Finite.injective_iff_bijective.mp hg
  let σ := Equiv.ofBijective g hgb
  -- `ι ∘ v = ∑ b, cK (g b) • fR K (g b)`.
  have hcK' : ∑ b, cK (σ b) • fR K (σ b) = ι ∘ v := by
    rw [← hcK]
    exact Equiv.sum_comp σ (fun i => cK i • fR K i)
  have hWK : (W.map ι) *ᵥ (fun b => cK (σ b)) = ι ∘ vS := by
    funext a
    have := congrFun hcK' (S a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hW, minorInt, Matrix.of_apply,
      Function.comp_apply, vS]
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [fR, σ, mul_comm]
  have hWK' : (W.map ι) *ᵥ (ι ∘ (W⁻¹ *ᵥ vS)) = ι ∘ vS := by
    funext a
    rw [Function.comp_apply]
    conv_rhs => rw [← hWc]
    exact (RingHom.map_mulVec ι W _ a).symm
  -- `W.map ι` is invertible, so the two coefficient vectors agree over `K`.
  have coeff : ι ∘ (W⁻¹ *ᵥ vS) = fun b => cK (σ b) := by
    have h1 := congrArg (fun z => (W.map ι)⁻¹ *ᵥ z) (hWK'.trans hWK.symm)
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ WK, Matrix.one_mulVec] using h1
  -- Conclude coordinatewise, using injectivity of `ι`.
  funext x
  apply hι
  have hx := congrFun hcK' x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hx
  rw [Finset.sum_apply, map_sum, ← hx]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  have hb := congrFun coeff b
  simp only [Function.comp_apply] at hb
  simp only [fR, map_intCast, hb, σ, Equiv.ofBijective_apply]

theorem independent_of_unit_minor (S : Fin 251 → V) (g : Fin 251 → Fin 251)
    (hS : IsUnit ((minorInt S g).map (Int.cast : ℤ → R)).det) : LinearIndependent R (fR R) := by
  -- Independence over the fraction field transfers to `R` by injectivity.
  let K := FractionRing R
  let ι : R →+* K := algebraMap R K
  have hι : Function.Injective ι := IsFractionRing.injective R K
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hK := Fintype.linearIndependent_iff.mp (frame_independent_field K) (ι ∘ c) (by
    funext x
    have := congrArg ι (congrFun hc x)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_zero,
      Pi.zero_apply] at this
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, fR,
      map_intCast, Pi.zero_apply] using this)
  intro i
  exact hι (by simpa using hK i)

end Domain

/-! ### `R₀ = ℤ₍₃₎` -/

instance : (Ideal.span {(3 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three

/-- `R₀ = ℤ₍₃₎`. -/
abbrev R0 := Localization.AtPrime (Ideal.span {(3 : ℤ)})

instance : IsDomain R0 :=
  IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)

/-- A frame minor that is nonzero modulo 3. -/
theorem exists_minor_mod3 : ∃ (S : Fin 251 → V) (g : Fin 251 → Fin 251),
    ¬ (3 : ℤ) ∣ (minorInt S g).det := by
  classical
  let M : Matrix V (Fin 251) (ZMod 3) := Matrix.of fun x i => (fInt i x : ZMod 3)
  have hrank : 251 ≤ M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have hcols : M.col = fR (ZMod 3) := by
      funext i x
      rfl
    rw [hcols, finrank_span_eq_card (frame_independent_field (ZMod 3)), Fintype.card_fin]
  obtain ⟨S, g, hdet⟩ := Census.Minors.exists_minor_ne_zero M hrank
  refine ⟨S, g, fun h3 => hdet ?_⟩
  have hmap : M.submatrix S g = (minorInt S g).map (Int.cast : ℤ → ZMod 3) := by
    ext a b
    rfl
  rw [hmap, ← Int.cast_det]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3

theorem isUnit_minor_R0 {S : Fin 251 → V} {g : Fin 251 → Fin 251}
    (h3 : ¬ (3 : ℤ) ∣ (minorInt S g).det) :
    IsUnit ((minorInt S g).map (Int.cast : ℤ → R0)).det := by
  rw [← Int.cast_det]
  have hmem : (minorInt S g).det ∈ (Ideal.span {(3 : ℤ)}).primeCompl := by
    intro h
    exact h3 (Ideal.mem_span_singleton.mp h)
  have := IsLocalization.map_units R0 (⟨_, hmem⟩ : (Ideal.span {(3 : ℤ)}).primeCompl)
  simpa [algebraMap_int_eq, eq_intCast] using this

/-- Lines 505–520: the 251 frozen tangent vectors form an `R₀`-basis of the kernel of `J` over
`R₀ = ℤ₍₃₎`. -/
theorem kernel_basis_Z3 :
    LinearIndependent R0 (fR R0) ∧
      ∀ v : V → R0, InKer R0 v → v ∈ Submodule.span R0 (Set.range (fR R0)) := by
  obtain ⟨S, g, h3⟩ := exists_minor_mod3
  have hS := isUnit_minor_R0 h3
  refine ⟨independent_of_unit_minor R0 S g hS, fun v hv => ?_⟩
  rw [← span_of_unit_minor R0 S g hS v hv]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The kernel of `J` over `R₀` as a submodule. -/
def kerZ3 : Submodule R0 (V → R0) where
  carrier := {v | InKer R0 v}
  add_mem' {a b} ha hb e := by
    have h1 := ha e
    have h2 := hb e
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  zero_mem' e := by simp
  smul_mem' c v hv e := by
    have h := hv e
    calc ∑ x, (JInt e x : R0) * (c • v) x = c * ∑ x, (JInt e x : R0) * v x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
      _ = 0 := by rw [h, mul_zero]

/-- The kernel over `R₀` is free, with the frozen frame as a basis. -/
noncomputable def kernelBasisZ3 : Basis (Fin 251) R0 kerZ3 :=
  Basis.mk (v := fun i => ⟨fR R0 i, frame_inKer R0 i⟩)
    (LinearIndependent.of_comp kerZ3.subtype kernel_basis_Z3.1)
    (by
      rintro ⟨v, hv⟩ -
      obtain ⟨S, g, h3⟩ := exists_minor_mod3
      have hc := span_of_unit_minor R0 S g (isUnit_minor_R0 h3) v hv
      have hw : (⟨v, hv⟩ : kerZ3) = ∑ b, (((minorInt S g).map (Int.cast : ℤ → R0))⁻¹ *ᵥ
          fun a => v (S a)) b • (⟨fR R0 (g b), frame_inKer R0 (g b)⟩ : kerZ3) := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        exact hc.symm
      rw [hw]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨g b, rfl⟩))

/-- Lines 515–516: the kernel over `R₀` is a direct summand: an `R₀`-linear projection of
`R₀^2352` onto it fixes every kernel vector. -/
theorem kernel_retract_Z3 : ∃ P : (V → R0) →ₗ[R0] (V → R0),
    (∀ v, P v ∈ kerZ3) ∧ ∀ v ∈ kerZ3, P v = v := by
  obtain ⟨S, g, h3⟩ := exists_minor_mod3
  have hS := isUnit_minor_R0 h3
  let L3 : (Fin 251 → R0) →ₗ[R0] (V → R0) :=
    { toFun := fun c => ∑ b, c b • fR R0 (g b)
      map_add' := fun c d => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  refine ⟨L3 ∘ₗ Matrix.mulVecLin ((minorInt S g).map (Int.cast : ℤ → R0))⁻¹ ∘ₗ
    LinearMap.funLeft R0 R0 S, fun v => ?_, fun v hv => ?_⟩
  · exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (frame_inKer R0 (g b))
  · exact span_of_unit_minor R0 S g hS v hv

/-- Lines 516–517: every kernel vector over `𝔽₃` lifts to an integral kernel vector, and hence to
one over `R₀`. -/
theorem kernel_lift_mod3 (w : V → ZMod 3) (hw : InKer (ZMod 3) w) :
    ∃ v : V → ℤ, InKer ℤ v ∧ InKer R0 (fun x => (v x : R0)) ∧
      (fun x => (v x : ZMod 3)) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp
    (kernel_span_field (ZMod 3) w hw)
  let v : V → ℤ := fun x => ∑ i, ((c i).val : ℤ) * fInt i x
  have hv : InKer ℤ v := by
    intro e
    have hf : ∀ i, ∑ x, JInt e x * fInt i x = 0 := fun i => by
      simpa only [fR, Int.cast_id] using frame_inKer ℤ i e
    simp only [Int.cast_id, v, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc ∑ x, JInt e x * (((c i).val : ℤ) * fInt i x)
        = ((c i).val : ℤ) * ∑ x, JInt e x * fInt i x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [hf i, mul_zero]
  refine ⟨v, hv, inKer_map (Int.castRingHom R0) hv, ?_⟩
  rw [← hc]
  funext x
  simp only [v, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fR]

end Brent.Z3
