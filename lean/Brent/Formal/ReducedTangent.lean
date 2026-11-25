import Brent.Formal.Branches
import Brent.KernelCheck.HilbertInitial

/-!
# The reduced tangent dimension is 251

Let `A_red = A ⧸ nil(A)`, for `A` the local ring of the Brent variety at the recursive point.
Its tangent space `𝔪/𝔪²` has dimension at most 251, because the 251 tangent coordinates
generate `𝔪` modulo `𝔪²`. For the lower bound, the two branch maps `A → Â → k⟦c,x⟧` and
`A → Â → k⟦c,y⟧` land in domains, so they factor through `A_red`. The linear coefficients
along the 197 + 197 chart variables give 251 functionals that vanish on `𝔪²`. On the
translated coordinates they are the 251 frame vectors, which are independent.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries IsLocalRing TangentData

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

variable (k : Type) [Field k]

/-- A direct instance; the search through the quotient `CoordinateRing` fails otherwise. -/
noncomputable instance instCommRingAalg : CommRing (Aalg k) := inferInstance

/-- The reduced local ring at the recursive point. -/
abbrev Ared := Aalg k ⧸ nilradical (Aalg k)

/-- The quotient map. -/
noncomputable abbrev πr : Aalg k →+* Ared k := Ideal.Quotient.mk _

theorem nilradical_le_max : nilradical (Aalg k) ≤ maximalIdeal (Aalg k) :=
  nilradical_le_prime _

instance : Nontrivial (Ared k) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (nilradical_le_max k))

instance : IsLocalRing (Ared k) :=
  IsLocalRing.of_surjective' (πr k) Ideal.Quotient.mk_surjective

theorem map_max_red : Ideal.map (πr k) (maximalIdeal (Aalg k)) = maximalIdeal (Ared k) := by
  have hmax : (Ideal.comap (πr k) (maximalIdeal (Ared k))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← IsLocalRing.eq_maximalIdeal hmax,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- The branch map on reduced germs. -/
noncomputable def ρ (left : Bool) : Ared k →+* MvPowerSeries (BranchVar k left) k :=
  Ideal.Quotient.lift _ ((branchMap k left).comp (ψ k)) fun _ ha =>
    ((mem_nilradical.mp ha).map _).eq_zero

theorem ρ_mk (left : Bool) (a : Aalg k) : ρ k left (πr k a) = branchMap k left (ψ k a) := rfl

theorem kill_Φ_C (left : Bool) (r : k) : kill k left (Φ k (C r)) = C r := by
  rw [Φ_apply, ← substAlgHom_apply (hasSubst_H k), algHom_C, kill_C]

theorem ρ_algebraMap (left : Bool) (r : k) : ρ k left (algebraMap k (Ared k) r) = C r := by
  change ρ k left (πr k (algebraMap k (Aalg k) r)) = C r
  rw [ρ_mk,
    ← (toPointLocalRing (strassenSquare k) (strassenSquare_solves k)).commutes r,
    MvPolynomial.algebraMap_eq, ψ_toPoint, ψ0, MvPolynomial.eval₂Hom_C, branchMap_mk, kill_Φ_C]

theorem ρ_max (left : Bool) {a : Ared k} (ha : a ∈ maximalIdeal (Ared k)) :
    constantCoeff (ρ k left a) = 0 := by
  rw [← map_max_red] at ha
  obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
  have hψ := ψ_mem k ha'
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (ψ k a')
  have h0 : constantCoeff f = 0 := by
    by_contra h
    rw [← hf] at hψ
    exact hψ ((isUnit_mkA_iff k f).mpr h)
  rw [ρ_mk, ← hf]
  change constantCoeff (branchMap k left (mkA k f)) = 0
  rw [branchMap_mk, constantCoeff_kill, Φ_apply]
  exact constantCoeff_subst_eq_zero (hasSubst_H k) (constantCoeff_H k) h0

/-- The chart used for a frame direction. -/
def chart (i : Fin 251) : Bool := decide (i.val < 197)

theorem inChart_chart (i : Fin 251) : InChart i (chart i) := by
  unfold chart InChart
  by_cases h : i.val < 197
  · simp [h]
  · simp [h]; omega

/-- The chart variable of a frame direction. -/
def chartVar (i : Fin 251) : BranchVar k (chart i) := ⟨Sum.inl i, inChart_chart i⟩

/-- **The 251 reduced tangent functionals.** -/
noncomputable def Λ : Ared k →ₗ[k] (Fin 251 → k) where
  toFun a i := coeff (Finsupp.single (chartVar k i) 1) (ρ k (chart i) a)
  map_add' a b := by
    funext i
    simp only [map_add, Pi.add_apply]
  map_smul' r a := by
    funext i
    simp only [Algebra.smul_def, map_mul, ρ_algebraMap, coeff_C_mul, RingHom.id_apply,
      Pi.smul_apply]
    rfl

theorem Λ_apply (a : Ared k) (i : Fin 251) :
    Λ k a i = coeff (Finsupp.single (chartVar k i) 1) (ρ k (chart i) a) := rfl

theorem Λ_sq {a : Ared k} (ha : a ∈ maximalIdeal (Ared k) ^ (1 + 1)) : Λ k a = 0 := by
  rw [pow_succ, pow_one] at ha
  refine Submodule.mul_induction_on ha (fun m hm n hn => ?_) (fun x y hx hy => ?_)
  · funext i
    rw [Λ_apply, map_mul, coeff_single_mul, ρ_max k _ hm, ρ_max k _ hn, zero_mul, mul_zero,
      add_zero]
    rfl
  · rw [map_add, hx, hy, add_zero]

theorem Λ_y (x : Var) :
    Λ k (πr k (UpperBound.y k x)) = fun i => CharThree.frameVec k i x := by
  funext i
  rw [Λ_apply, ρ_mk, UpperBound.y, ψ_toPoint]
  have h : ψ0 k (MvPolynomial.X x - MvPolynomial.C ((strassenSquare k).coordinates x)) = X x := by
    simp [ψ0, pt]
  rw [h, branchMap_mk, Φ_apply, subst_X (hasSubst_H k), kill, coeff_killCompl,
    Finsupp.embDomain_single]
  change coeff (Finsupp.single (Sum.inl i) 1) (H k x) = _
  rw [coeff_H, B_inl]
  rfl

/-- The residue map of `A_red`. -/
noncomputable def residueRed : Ared k →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (HilbertInitial.residue k) fun _ ha =>
    ((mem_nilradical.mp ha).map _).eq_zero

/-- **The reduced tangent dimension is 251.** -/
theorem hilbertValue_reduced_one : hilbertValue k (Ared k) 1 = 251 := by
  have hgen : maximalIdeal (Ared k) ≤
      Ideal.span (Set.range (πr k ∘ UpperBound.z k)) ⊔ maximalIdeal (Ared k) ^ 2 := by
    rw [← map_max_red]
    refine (Ideal.map_mono (CharZeroBound.gen_z k)).trans (le_of_eq ?_)
    simp only [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.range_comp]
  have hz : ∀ i, (πr k ∘ UpperBound.z k) i ∈ maximalIdeal (Ared k) := fun i => by
    rw [← map_max_red]
    exact Ideal.mem_map_of_mem _ (UpperBound.z_mem k i)
  obtain ⟨hfin, hle⟩ := hilbertValue_le_of_le_span _
    (gradedPiece_one_le_span (residueRed k) _ hz hgen)
  haveI := hfin
  refine le_antisymm hle (le_hilbertValue (Λ k) (fun a ha => Λ_sq k ha)
    (fun x => πr k (UpperBound.y k x)) (fun x => ?_) ?_)
  · rw [pow_one, ← map_max_red]
    exact Ideal.mem_map_of_mem _ (UpperBound.y_mem k x)
  · simp only [Λ_y]
    exact HilbertInitial.frame_columns_span k

end Brent.Formal
