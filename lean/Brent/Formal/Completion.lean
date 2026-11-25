import Brent.Formal.ReducedTangent
import Brent.Formal.PowerSeriesAdic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# `SquareCompletion ≃+* Â`

`Â = k⟦z⟧ ⧸ (centered Brent equations)` is complete for its maximal ideal, and the map
`ψ : A → Â` from the algebraic local ring induces isomorphisms `A ⧸ 𝔪ⁿ ≃ Â ⧸ 𝔪̂ⁿ` for every `n`.
Hence the `𝔪`-adic completion of `A` (the ring `SquareCompletion` of the paper) is `Â`, and
the F6/F7 statements about `Â` transfer to `SquareCompletion`.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries IsLocalRing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

variable (k : Type) [Field k]

/-! ### `Â` is complete -/

theorem maximalIdeal_Ahat_eq_map : maximalIdeal (Ahat k) = (mX Var k).map (mkA k) := by
  rw [maximalIdeal_Ahat, mX, Ideal.map_span, ← Set.range_comp]
  rfl

theorem maximalIdeal_Ahat_pow (n : ℕ) :
    maximalIdeal (Ahat k) ^ n = (mX Var k ^ n).map (mkA k) := by
  rw [maximalIdeal_Ahat_eq_map, Ideal.map_pow]

theorem mem_maximalIdeal_Ahat_pow {n : ℕ} {a : Ahat k} :
    a ∈ maximalIdeal (Ahat k) ^ n ↔ ∃ f ∈ mX Var k ^ n, mkA k f = a := by
  rw [maximalIdeal_Ahat_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]

theorem pow_smul_top_Ahat (n : ℕ) :
    (maximalIdeal (Ahat k) ^ n • ⊤ : Submodule (Ahat k) (Ahat k)) =
      (maximalIdeal (Ahat k) ^ n : Ideal (Ahat k)) := by
  rw [smul_eq_mul, Ideal.mul_top]

/- The module structure is stated explicitly: instance search on the quotient `Ahat k` finds the
quotient-module structure, which is not reducibly the one Mathlib's adic API uses. -/
instance instIsPrecompleteAhat :
    @IsPrecomplete (Ahat k) _ (maximalIdeal (Ahat k)) (Ahat k) _ Semiring.toModule := by
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, pow_smul_top_Ahat] at hf ⊢
  have hd : ∀ n, f (n + 1) - f n ∈ maximalIdeal (Ahat k) ^ n := fun n => by
    have := hf (Nat.le_succ n)
    rw [← neg_sub] at this
    exact neg_mem_iff.mp this
  choose d hd hdmk using fun n => (mem_maximalIdeal_Ahat_pow k).mp (hd n)
  obtain ⟨a0, ha0⟩ := Ideal.Quotient.mk_surjective (f 0)
  let F : ℕ → MvPowerSeries Var k := fun n => a0 + ∑ i ∈ Finset.range n, d i
  have hF : ∀ n, F (n + 1) - F n = d n := fun n => by
    simp only [F, Finset.sum_range_succ]
    ring
  have hFmk : ∀ n, mkA k (F n) = f n := by
    intro n
    induction n with
    | zero => simp [F, ha0]
    | succ n ih =>
      rw [show F (n + 1) = F n + d n by rw [← hF]; ring, map_add, ih, hdmk]
      ring
  obtain ⟨L, hL⟩ := exists_limit F fun n => (hF n).symm ▸ hd n
  refine ⟨mkA k L, fun n => ?_⟩
  rw [← neg_mem_iff, neg_sub, mem_maximalIdeal_Ahat_pow]
  exact ⟨L - F n, hL n, by rw [map_sub, hFmk]⟩

instance instIsAdicCompleteAhat :
    @IsAdicComplete (Ahat k) _ (maximalIdeal (Ahat k)) (Ahat k) _ Semiring.toModule := {}


/-! ### Translations of the polynomial ring -/

/-- `z ↦ z - p`. -/
noncomputable def tMinus : MvPolynomial Var k →ₐ[k] MvPolynomial Var k :=
  MvPolynomial.aeval fun x => MvPolynomial.X x - MvPolynomial.C (pt k x)

/-- `z ↦ z + p`. -/
noncomputable def tPlus : MvPolynomial Var k →ₐ[k] MvPolynomial Var k :=
  MvPolynomial.aeval fun x => MvPolynomial.X x + MvPolynomial.C (pt k x)

theorem tMinus_tPlus (p : MvPolynomial Var k) : tMinus k (tPlus k p) = p := by
  have : (tMinus k).comp (tPlus k) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [tMinus, tPlus]
  exact congrArg (fun φ : MvPolynomial Var k →ₐ[k] MvPolynomial Var k => φ p) this

theorem ψ0_tMinus (p : MvPolynomial Var k) :
    ψ0 k (tMinus k p) = (p : MvPowerSeries Var k) := by
  have : (ψ0 k).comp (tMinus k).toRingHom = MvPolynomial.coeToMvPowerSeries.ringHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tMinus, ψ0]
    · intro x
      simp [tMinus, ψ0]
  exact congrArg (fun φ : MvPolynomial Var k →+* MvPowerSeries Var k => φ p) this

theorem ψ0_eq_coe_tPlus (p : MvPolynomial Var k) :
    ψ0 k p = ((tPlus k p : MvPolynomial Var k) : MvPowerSeries Var k) := by
  have : (ψ0 k) = MvPolynomial.coeToMvPowerSeries.ringHom.comp (tPlus k).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tPlus, ψ0]
    · intro x
      simp [tPlus, ψ0, add_comm]
  exact congrArg (fun φ : MvPolynomial Var k →+* MvPowerSeries Var k => φ p) this

/-! ### The truncations -/

/-- The structure map of the algebraic local ring. -/
noncomputable abbrev toA : MvPolynomial Var k →ₐ[k] Aalg k :=
  toPointLocalRing (strassenSquare k) (strassenSquare_solves k)

theorem pow_le_comap (n : ℕ) :
    maximalIdeal (Aalg k) ^ n ≤ (maximalIdeal (Ahat k) ^ n).comap (ψ k) :=
  fun _ h => ψ_mem_pow k h

/-- `A ⧸ 𝔪ⁿ → Â ⧸ 𝔪̂ⁿ`. -/
noncomputable def truncMap (n : ℕ) :
    Aalg k ⧸ maximalIdeal (Aalg k) ^ n →+* Ahat k ⧸ maximalIdeal (Ahat k) ^ n :=
  Ideal.quotientMap _ (ψ k) (pow_le_comap k n)

theorem truncMap_mk (n : ℕ) (a : Aalg k) :
    truncMap k n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ψ k a) :=
  Ideal.quotientMap_mk

theorem truncMap_surjective (n : ℕ) : Function.Surjective (truncMap k n) := by
  classical
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk _ (toA k (tMinus k (trunc' k (box n) f))), ?_⟩
  rw [truncMap_mk, ψ_toPoint, ψ0_tMinus, Ideal.Quotient.eq, ← map_sub,
    mem_maximalIdeal_Ahat_pow]
  refine ⟨_, ?_, rfl⟩
  rw [← neg_mem_iff, neg_sub]
  exact sub_trunc_mem n f

theorem toA_equation (abc : EquationIndex SquareVertex) :
    toA k (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2) = 0 := by
  have : Ideal.Quotient.mk (brentIdeal k SquareVertex SquareSummand)
      (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨abc, rfl⟩)
  rw [toPointLocalRing_apply, this, map_zero]

/-- The translated variable ideal maps into the maximal ideal. -/
theorem toA_tMinus_mem_pow (n : ℕ) {q : MvPolynomial Var k}
    (hq : q ∈ MvPolynomial.idealOfVars Var k ^ n) :
    toA k (tMinus k q) ∈ maximalIdeal (Aalg k) ^ n := by
  have hle : (MvPolynomial.idealOfVars Var k).map (tMinus k) ≤
      RingHom.ker (MvPolynomial.eval (strassenSquare k).coordinates) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    simp [tMinus, pt]
  have h1 : tMinus k q ∈ RingHom.ker (MvPolynomial.eval (strassenSquare k).coordinates) ^ n := by
    refine Ideal.pow_right_mono hle n ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hq
  have h2 := Ideal.mem_map_of_mem (toA k) h1
  rwa [Ideal.map_pow, ← maximalIdeal_pointLocalRing] at h2

/-- **The core lemma.** A polynomial whose image in `Â` lies in `𝔪̂ⁿ` lies in `𝔪ⁿ` in `A`. -/
theorem toA_mem_pow_of_ψ {n : ℕ} (p : MvPolynomial Var k)
    (hp : ψ k (toA k p) ∈ maximalIdeal (Ahat k) ^ n) : toA k p ∈ maximalIdeal (Aalg k) ^ n := by
  classical
  rw [ψ_toPoint, mem_maximalIdeal_Ahat_pow] at hp
  obtain ⟨f, hf, hfp⟩ := hp
  have hmem : ψ0 k p - f ∈ brentPS k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hfp, sub_self]
  rw [brentPS, Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨g, hg⟩ := hmem
  let P : EquationIndex SquareVertex → MvPolynomial Var k :=
    fun e => tMinus k (trunc' k (box n) (g e))
  let E : EquationIndex SquareVertex → MvPolynomial Var k :=
    fun e => equation k SquareVertex SquareSummand e.1 e.2.1 e.2.2
  have hE : ∀ e, ψ0 k (E e) = eqPS k e := fun _ => rfl
  let r := p - ∑ e, P e * E e
  have hr : ψ0 k r ∈ mX Var k ^ n := by
    have : ψ0 k r = f + ∑ e, (g e - ψ0 k (P e)) * eqPS k e := by
      simp only [r, map_sub, map_sum, map_mul, hE, sub_mul, Finset.sum_sub_distrib]
      rw [hg]
      ring
    rw [this]
    refine add_mem hf (Ideal.sum_mem _ fun e _ => Ideal.mul_mem_right _ _ ?_)
    simp only [P, ψ0_tMinus]
    exact sub_trunc_mem n (g e)
  rw [ψ0_eq_coe_tPlus] at hr
  have hq := toA_tMinus_mem_pow k n (mem_pow_idealOfVars_of_coe hr)
  rw [tMinus_tPlus] at hq
  have : toA k r = toA k p := by
    simp only [r, map_sub, map_sum, map_mul, E, toA_equation, mul_zero, Finset.sum_const_zero]
    exact sub_zero _
  rwa [this] at hq

theorem mem_pow_of_ψ {n : ℕ} {a : Aalg k} (ha : ψ k a ∈ maximalIdeal (Ahat k) ^ n) :
    a ∈ maximalIdeal (Aalg k) ^ n := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  dsimp only at ha ⊢
  have hspec := IsLocalization.mk'_spec (Aalg k) (Ideal.Quotient.mk _ p) s
  have hu : IsUnit (algebraMap _ (Aalg k) (s : SquareCoordinateRing k)) :=
    IsLocalization.map_units (Aalg k) s
  have hp : toA k p ∈ maximalIdeal (Aalg k) ^ n := by
    refine toA_mem_pow_of_ψ k p ?_
    rw [toPointLocalRing_apply, ← hspec, map_mul]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨u, hu⟩ := hu
  have : IsLocalization.mk' (Aalg k) (Ideal.Quotient.mk _ p) s = toA k p * ↑u⁻¹ := by
    rw [toPointLocalRing_apply, ← hspec, ← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hp

/-- **`A ⧸ 𝔪ⁿ ≃ Â ⧸ 𝔪̂ⁿ`.** -/
noncomputable def truncEquiv (n : ℕ) :
    Aalg k ⧸ maximalIdeal (Aalg k) ^ n ≃+* Ahat k ⧸ maximalIdeal (Ahat k) ^ n :=
  RingEquiv.ofBijective (truncMap k n)
    ⟨Ideal.quotientMap_injective' fun _ h => mem_pow_of_ψ k h, truncMap_surjective k n⟩


/-- The `𝔪`-adic completion of `A`, with `A` acting on itself through the ring structure.
(The default instance search finds the `OreLocalization` module structure instead, which is
definitionally but not reducibly equal, and hides the ring structure of the completion.) -/
abbrev Acompl : Type :=
  @AdicCompletion (Aalg k) _ (maximalIdeal (Aalg k)) (Aalg k) _ Semiring.toModule

theorem truncEquiv_apply (n : ℕ) (x : Aalg k ⧸ maximalIdeal (Aalg k) ^ n) :
    truncEquiv k n x = truncMap k n x := rfl

theorem truncMap_factorPow {m n : ℕ} (hle : m ≤ n) (x : Aalg k ⧸ maximalIdeal (Aalg k) ^ n) :
    truncMap k m (Ideal.Quotient.factorPow _ hle x) =
      Ideal.Quotient.factorPow _ hle (truncMap k n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, truncMap_mk]

theorem evalₐ_factorPow {m n : ℕ} (hle : m ≤ n) (y : Acompl k) :
    Ideal.Quotient.factorPow _ hle (AdicCompletion.evalₐ _ n y) = AdicCompletion.evalₐ _ m y := by
  obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk _ hle]

/-- The maps `Â → Â ⧸ 𝔪̂ⁿ ≃ A ⧸ 𝔪ⁿ`. -/
noncomputable def toFamily (n : ℕ) : Ahat k →+* Aalg k ⧸ maximalIdeal (Aalg k) ^ n :=
  (truncEquiv k n).symm.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal (Ahat k) ^ n))

theorem toFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal (Aalg k)) hle).comp (toFamily k n) = toFamily k m := by
  ext b
  apply (truncEquiv k m).injective
  simp only [toFamily, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, RingEquiv.apply_symm_apply]
  rw [truncEquiv_apply, truncMap_factorPow, ← truncEquiv_apply, RingEquiv.apply_symm_apply,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The maps `A^ → A ⧸ 𝔪ⁿ ≃ Â ⧸ 𝔪̂ⁿ`. -/
noncomputable def fromFamily (n : ℕ) : Acompl k →+* Ahat k ⧸ maximalIdeal (Ahat k) ^ n :=
  (truncMap k n).comp (AdicCompletion.evalₐ (maximalIdeal (Aalg k)) n : _ →+* _)

theorem fromFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal (Ahat k)) hle).comp (fromFamily k n) =
      fromFamily k m := by
  ext y
  simp only [fromFamily, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  rw [← truncMap_factorPow, evalₐ_factorPow]

/-- `Â → A^`. -/
noncomputable def toCompletion : Ahat k →+* Acompl k :=
  AdicCompletion.liftRingHom _ (toFamily k) (toFamily_compat k)

/-- `A^ → Â`, using completeness of `Â`. -/
noncomputable def fromCompletion : Acompl k →+* Ahat k :=
  @IsAdicComplete.liftRingHom (Acompl k) (Ahat k) _ _ (maximalIdeal (Ahat k))
    (instIsAdicCompleteAhat k) (fromFamily k) (fromFamily_compat k)

theorem evalₐ_toCompletion (n : ℕ) (b : Ahat k) :
    AdicCompletion.evalₐ _ n (toCompletion k b) = (truncEquiv k n).symm (Ideal.Quotient.mk _ b) :=
  AdicCompletion.evalₐ_liftRingHom _ (toFamily k) (toFamily_compat k) n b

theorem mk_fromCompletion (n : ℕ) (y : Acompl k) :
    Ideal.Quotient.mk (maximalIdeal (Ahat k) ^ n) (fromCompletion k y) =
      truncMap k n (AdicCompletion.evalₐ _ n y) :=
  @IsAdicComplete.mk_liftRingHom (Acompl k) (Ahat k) _ _ (maximalIdeal (Ahat k))
    (instIsAdicCompleteAhat k) (fromFamily k) (fromFamily_compat k) n y

/-- **The completion of the algebraic local ring is `Â`.** -/
noncomputable def completionEquiv :
    Acompl k ≃+* Ahat k :=
  RingEquiv.ofRingHom (fromCompletion k) (toCompletion k)
    (by
      apply DFunLike.coe_injective
      refine IsHausdorff.funext' (maximalIdeal (Ahat k)) fun n b => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [mk_fromCompletion, evalₐ_toCompletion, ← truncEquiv_apply, RingEquiv.apply_symm_apply])
    (by
      refine RingHom.ext fun y => AdicCompletion.ext_evalₐ (I := maximalIdeal (Aalg k)) fun n => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [evalₐ_toCompletion, mk_fromCompletion, ← truncEquiv_apply, RingEquiv.symm_apply_apply])


/-! ### The paper's `SquareCompletion` -/

/-- `SquareCompletion k` is `Acompl k` up to the choice of the `A`-module instance on `A`
(the two are definitionally equal). -/
theorem squareCompletion_eq : SquareCompletion k = Acompl k := rfl

/-- The ring structure of the completion. -/
noncomputable instance : CommRing (SquareCompletion k) := inferInstanceAs (CommRing (Acompl k))

/-- **`SquareCompletion ≃+* Â`.** -/
noncomputable def sqEquiv : SquareCompletion k ≃+* Ahat k := completionEquiv k

instance : Nontrivial (SquareCompletion k) := (sqEquiv k).symm.injective.nontrivial

instance : IsLocalRing (SquareCompletion k) :=
  IsLocalRing.of_surjective' (sqEquiv k).symm.toRingHom (sqEquiv k).symm.surjective

instance : IsNoetherianRing (SquareCompletion k) :=
  isNoetherianRing_of_ringEquiv _ (sqEquiv k).symm

theorem ringKrullDim_squareCompletion : ringKrullDim (SquareCompletion k) = ringKrullDim (Ahat k) :=
  ringKrullDim_eq_of_ringEquiv (sqEquiv k)

/-- **`dim SquareCompletion ≤ 197` in characteristic three.** -/
theorem ringKrullDim_squareCompletion_le_charThree [CharP k 3] :
    ringKrullDim (SquareCompletion k) ≤ 197 := by
  rw [ringKrullDim_squareCompletion]
  exact ringKrullDim_Ahat_le_charThree k

/-- **`dim SquareCompletion ≤ 197` in characteristic zero.** -/
theorem ringKrullDim_squareCompletion_le_charZero [CharZero k] :
    ringKrullDim (SquareCompletion k) ≤ 197 := by
  rw [ringKrullDim_squareCompletion]
  exact ringKrullDim_Ahat_le_charZero k

/-! #### The branches -/

/-- The branch maps on `SquareCompletion`. -/
noncomputable def sqBranchMap (left : Bool) :
    SquareCompletion k →+* MvPowerSeries (BranchVar k left) k :=
  (branchMap k left).comp (sqEquiv k).toRingHom

theorem sqBranchMap_surjective (left : Bool) : Function.Surjective (sqBranchMap k left) :=
  (branchMap_surjective k left).comp (sqEquiv k).surjective

/-- The branch primes `𝔭_L` (`left = true`) and `𝔭_R` of `SquareCompletion`. -/
noncomputable def sqBranchPrime (left : Bool) : Ideal (SquareCompletion k) :=
  RingHom.ker (sqBranchMap k left)

instance sqBranchPrime_isPrime (left : Bool) : (sqBranchPrime k left).IsPrime :=
  RingHom.ker_isPrime _

theorem sqBranchPrime_eq_comap (left : Bool) :
    sqBranchPrime k left = (branchPrime k left).comap (sqEquiv k).toRingHom := by
  rw [sqBranchPrime, sqBranchMap, ← RingHom.comap_ker]
  rfl

theorem sqBranchPrime_eq_map (left : Bool) :
    sqBranchPrime k left = (branchPrime k left).map (sqEquiv k).symm := by
  rw [sqBranchPrime_eq_comap, Ideal.map_symm]
  rfl

/-- **`SquareCompletion ⧸ 𝔭_L ≃ k⟦c, x⟧` and `SquareCompletion ⧸ 𝔭_R ≃ k⟦c, y⟧`.** -/
noncomputable def sqBranchQuotEquiv (left : Bool) :
    (SquareCompletion k ⧸ sqBranchPrime k left) ≃+* MvPowerSeries (BranchVar k left) k :=
  RingHom.quotientKerEquivOfSurjective (sqBranchMap_surjective k left)

theorem ringKrullDim_sqBranch (left : Bool) :
    ringKrullDim (SquareCompletion k ⧸ sqBranchPrime k left) = 197 := by
  rw [ringKrullDim_eq_of_ringEquiv (sqBranchQuotEquiv k left), ringKrullDim_mvPowerSeries,
    card_branchVar]
  rfl

theorem sqBranchPrime_minimal (left : Bool) (hdim : ringKrullDim (SquareCompletion k) ≤ 197) :
    sqBranchPrime k left ∈ minimalPrimes (SquareCompletion k) := by
  refine ker_mem_minimalPrimes (sqBranchMap k left) (sqBranchMap_surjective k left)
    (varChain (BranchVar k left) k) (varChain_head _ k) ?_
  rw [varChain_length, card_branchVar]
  exact hdim

/-- **`𝔭_L` and `𝔭_R` are minimal primes of `SquareCompletion` (characteristic three).** -/
theorem sqBranchPrime_minimal_charThree [CharP k 3] (left : Bool) :
    sqBranchPrime k left ∈ minimalPrimes (SquareCompletion k) :=
  sqBranchPrime_minimal k left (ringKrullDim_squareCompletion_le_charThree k)

/-- **`𝔭_L` and `𝔭_R` are minimal primes of `SquareCompletion` (characteristic zero).** -/
theorem sqBranchPrime_minimal_charZero [CharZero k] (left : Bool) :
    sqBranchPrime k left ∈ minimalPrimes (SquareCompletion k) :=
  sqBranchPrime_minimal k left (ringKrullDim_squareCompletion_le_charZero k)

/-- **`𝔭_L ≠ 𝔭_R` in `SquareCompletion`.** -/
theorem sqBranchPrime_ne : sqBranchPrime k true ≠ sqBranchPrime k false := by
  intro h
  rw [sqBranchPrime_eq_comap, sqBranchPrime_eq_comap] at h
  exact branchPrime_ne k (Ideal.comap_injective_of_surjective _ (sqEquiv k).surjective h)

/-! #### The intersection of the branches -/

noncomputable def sqOrbitMap : SquareCompletion k →+* MvPowerSeries (OrbitVar k) k :=
  (orbitMap k).comp (sqEquiv k).toRingHom

theorem ker_sqOrbitMap :
    RingHom.ker (sqOrbitMap k) = sqBranchPrime k true ⊔ sqBranchPrime k false := by
  rw [sqOrbitMap, ← RingHom.comap_ker, ker_orbitMap, sqBranchPrime_eq_map, sqBranchPrime_eq_map,
    ← Ideal.map_sup, Ideal.map_symm]
  rfl

/-- **`SquareCompletion ⧸ (𝔭_L + 𝔭_R) ≃ k⟦c⟧`.** -/
noncomputable def sqIntersectionEquiv :
    (SquareCompletion k ⧸ (sqBranchPrime k true ⊔ sqBranchPrime k false)) ≃+*
      MvPowerSeries (OrbitVar k) k :=
  (Ideal.quotEquivOfEq (ker_sqOrbitMap k).symm).trans
    (RingHom.quotientKerEquivOfSurjective ((orbitMap_surjective k).comp (sqEquiv k).surjective))

/-- **The intersection of the branches in `SquareCompletion` has dimension 143.** -/
theorem ringKrullDim_sqIntersection :
    ringKrullDim (SquareCompletion k ⧸ (sqBranchPrime k true ⊔ sqBranchPrime k false)) = 143 := by
  rw [ringKrullDim_eq_of_ringEquiv (sqIntersectionEquiv k), ringKrullDim_mvPowerSeries,
    card_orbitVar]
  rfl

end Brent.Formal
