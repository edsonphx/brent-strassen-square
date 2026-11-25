import Brent.Formal.SliceIndependence
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The swap symmetry of the two orientations (§7)

Let `K` be the permutation of the 4-dimensional matrix index `k² ⊗ k²` that exchanges the two
tensor factors. The global change `P = Q = R = K`, composed with the term permutation
`(i, j) ↦ (j, i)`, is the involution `swapDec` of decompositions. It is a symmetry of the Brent
equations, fixes the recursive point `p`, and exchanges the two families:
`swapDec (leftFamily P Q T) = rightFamily P Q T` for every block parameter, and more generally
`swapDec (g·L) = (KgK)·R` for every group element `g`.

On the formal local ring it induces an automorphism `swapHat` of `Â` that exchanges the branch
primes `𝔭_L` and `𝔭_R` (characteristic three and zero) and fixes `𝔭_L + 𝔭_R`.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries TangentData

set_option linter.unusedSectionVars false

/-! ### The involution on decompositions -/

/-- The factor exchange `K` on `k² ⊗ k²`. -/
def Kv : SquareVertex ≃ SquareVertex := Equiv.prodComm (Fin 2) (Fin 2)

/-- `K` on pairs of matrix indices. -/
def Kp : SquareVertex × SquareVertex ≃ SquareVertex × SquareVertex := Equiv.prodCongr Kv Kv

/-- The term permutation `(i, j) ↦ (j, i)`. -/
def Ks : SquareSummand ≃ SquareSummand := Equiv.prodComm (Fin 7) (Fin 7)

section Dec

variable {R : Type} [CommRing R]

/-- **The swap**: global change of basis by `K` in all three slots, then the term
permutation. -/
def swapDec (d : Decomposition R SquareVertex SquareSummand) :
    Decomposition R SquareVertex SquareSummand where
  u s a := d.u (Ks s) (Kp a)
  v s a := d.v (Ks s) (Kp a)
  w s a := d.w (Ks s) (Kp a)

theorem swapDec_swapDec (d : Decomposition R SquareVertex SquareSummand) :
    swapDec (swapDec d) = d := rfl

theorem swapDec_injective : Function.Injective (swapDec (R := R)) := fun d e h => by
  rw [← swapDec_swapDec d, h, swapDec_swapDec]

theorem entry_swapDec (d : Decomposition R SquareVertex SquareSummand) (a b c : SquareVertex × SquareVertex) :
    (swapDec d).entry a b c = d.entry (Kp a) (Kp b) (Kp c) := by
  unfold Decomposition.entry
  exact Fintype.sum_equiv Ks _ _ fun s => rfl

theorem mme_Kp (a b c : SquareVertex × SquareVertex) :
    matrixMultiplicationEntry R (Kp a) (Kp b) (Kp c) = matrixMultiplicationEntry R a b c := by
  unfold matrixMultiplicationEntry
  simp only [Kp, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, EmbeddingLike.apply_eq_iff_eq]

/-- **The swap is a symmetry of the Brent equations.** -/
theorem swapDec_solves {d : Decomposition R SquareVertex SquareSummand} (hd : d.Solves) :
    (swapDec d).Solves := by
  intro a b c
  rw [entry_swapDec, hd, mme_Kp]

/-- **The swap exchanges the two block families.** -/
theorem swapDec_leftFamily (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    swapDec (leftFamily P Q T) = rightFamily P Q T := by
  unfold swapDec leftFamily rightFamily Decomposition.recursiveLeft Decomposition.recursiveRight
  congr 1 <;> funext s a <;> exact mul_comm _ _

theorem swapDec_rightFamily (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    swapDec (rightFamily P Q T) = leftFamily P Q T := by
  rw [← swapDec_leftFamily, swapDec_swapDec]

/-- **The swap fixes the recursive point.** -/
theorem swapDec_strassenSquare : swapDec (strassenSquare R) = strassenSquare R := by
  conv_lhs => rw [← leftFamily_at_identity]
  rw [swapDec_leftFamily, rightFamily_at_identity]

/-- Conjugation by `K`. -/
noncomputable def conjK : Matrix SquareVertex SquareVertex R ≃ₐ[R] Matrix SquareVertex SquareVertex R :=
  Matrix.reindexAlgEquiv R R Kv

theorem conjK_apply (M : Matrix SquareVertex SquareVertex R) (i j : SquareVertex) :
    conjK M i j = M (Kv i) (Kv j) := by
  rw [conjK, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

/-- Conjugating a unit by `K`. -/
noncomputable def conjU (P : (Matrix SquareVertex SquareVertex R)ˣ) :
    (Matrix SquareVertex SquareVertex R)ˣ :=
  Units.map (conjK (R := R)).toMonoidHom P

theorem conjK_eq (M : Matrix SquareVertex SquareVertex R) :
    conjK M = M.submatrix Kv Kv := by
  ext i j; rw [conjK_apply]; rfl

theorem swapDec_changeBasis (d : Decomposition R SquareVertex SquareSummand)
    (P Q T : (Matrix SquareVertex SquareVertex R)ˣ) :
    swapDec (d.changeBasis P Q T) = (swapDec d).changeBasis (conjU P) (conjU Q) (conjU T) := by
  have key : ∀ (A : Matrix SquareVertex SquareVertex R) (f : SquareVertex × SquareVertex → R)
      (B : Matrix SquareVertex SquareVertex R) (a : SquareVertex × SquareVertex),
      (A * Matrix.of (fun i j => f (i, j)) * B) (Kp a).1 (Kp a).2 =
        ((A.submatrix Kv Kv) * Matrix.of (fun i j => f (Kp (i, j))) * (B.submatrix Kv Kv))
          a.1 a.2 := by
    intro A f B a
    have h1 : Matrix.of (fun i j => f (Kp (i, j))) =
        (Matrix.of fun i j => f (i, j)).submatrix Kv Kv := by
      ext i j; rfl
    rw [h1, Matrix.submatrix_mul_equiv _ _ _ Kv _, Matrix.submatrix_mul_equiv _ _ _ Kv _]
    rfl
  unfold swapDec Decomposition.changeBasis
  congr 1 <;> funext s a
  · refine (key _ (d.u (Ks s)) _ a).trans ?_
    rfl
  · refine (key _ (d.v (Ks s)) _ a).trans ?_
    rfl
  · refine (key _ (d.w (Ks s)) _ a).trans ?_
    rfl

theorem swapDec_rescale (d : Decomposition R SquareVertex SquareSummand) (l m : SquareSummand → Rˣ) :
    swapDec (d.rescale l m) = (swapDec d).rescale (fun s => l (Ks s)) (fun s => m (Ks s)) := rfl

/-- The swapped group element `g ↦ (KgK, blocks, scalings ∘ (i,j)↦(j,i))`. -/
noncomputable def swapParams (p : FamilyParameters R) : FamilyParameters R :=
  ⟨fun g => conjU (p.global g), p.block, fun s c => p.scale (Ks s) c⟩

/-- **The swap exchanges the two orientations**, for every group element. -/
theorem swapDec_value (p : FamilyParameters R) (left : Bool) :
    swapDec (p.value left) = (swapParams p).value (!left) := by
  cases left <;>
    simp only [FamilyParameters.value, swapDec_rescale, swapDec_changeBasis, swapDec_leftFamily,
      swapDec_rightFamily, swapParams, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_true, if_false]

end Dec

/-! ### The induced automorphism of `Â` -/

section Formal

variable (k : Type) [Field k]

/-- The swap on the Brent variables. -/
def piV (x : Var) : Var := (Ks x.1, x.2.1, Kp x.2.2)

theorem piV_piV (x : Var) : piV (piV x) = x := rfl

theorem coordinates_swapDec {R : Type} [CommRing R] (d : Decomposition R SquareVertex SquareSummand)
    (x : Var) : (swapDec d).coordinates x = d.coordinates (piV x) := by
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

theorem pt_piV (x : Var) : pt k (piV x) = pt k x := by
  rw [pt, pt, ← coordinates_swapDec, swapDec_strassenSquare]

/-- The decomposition with coordinates `g`. -/
def univ {τ : Type} (g : Var → MvPowerSeries τ k) :
    Decomposition (MvPowerSeries τ k) SquareVertex SquareSummand :=
  ⟨fun s a => g (s, .u, a), fun s a => g (s, .v, a), fun s a => g (s, .w, a)⟩

theorem eval₂_equation {τ : Type} (g : Var → MvPowerSeries τ k) (abc : EquationIndex SquareVertex) :
    MvPolynomial.eval₂Hom C g (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2) =
      (univ k g).entry abc.1 abc.2.1 abc.2.2 - C (matrixMultiplicationEntry k abc.1 abc.2.1 abc.2.2) := by
  simp [equation, Decomposition.entry, univ]

theorem hasSubst_piV : HasSubst (fun x : Var => (X (piV x) : MvPowerSeries Var k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

/-- The swap on `k⟦z⟧`. -/
noncomputable def swapPS : MvPowerSeries Var k →ₐ[k] MvPowerSeries Var k :=
  substAlgHom (hasSubst_piV k)

theorem swapPS_swapPS (f : MvPowerSeries Var k) : swapPS k (swapPS k f) = f := by
  rw [swapPS, substAlgHom_apply, substAlgHom_apply,
    subst_comp_subst_apply (hasSubst_piV k) (hasSubst_piV k)]
  have : (fun x : Var => subst (fun x => (X (piV x) : MvPowerSeries Var k)) (X (piV x) : MvPowerSeries Var k)) =
      (X : Var → MvPowerSeries Var k) := by
    funext x
    rw [subst_X (hasSubst_piV k), piV_piV]
  rw [this, subst_self]
  rfl

/-- **The swap permutes the centered Brent equations.** -/
theorem swapPS_eqPS (abc : EquationIndex SquareVertex) :
    swapPS k (eqPS k abc) = eqPS k (Kp abc.1, Kp abc.2.1, Kp abc.2.2) := by
  rw [swapPS, substAlgHom_apply, subst_eqPS (hasSubst_piV k), eval₂_equation, eqPS,
    eval₂_equation]
  have h : univ k (fun x => C (pt k x) + X (piV x)) =
      swapDec (univ k (fun y => (C (pt k y) + X y : MvPowerSeries Var k))) := by
    change univ k _ = univ k (fun x => C (pt k (piV x)) + X (piV x))
    simp only [pt_piV]
  rw [h, entry_swapDec]
  simp only [mme_Kp]

theorem map_swapPS_le : Ideal.map (swapPS k) (brentPS k) ≤ brentPS k := by
  rw [brentPS, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨abc, rfl⟩, rfl⟩
  rw [swapPS_eqPS]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- **The swap on `Â`.** -/
noncomputable def swapHat : Ahat k →ₐ[k] Ahat k :=
  Ideal.Quotient.liftₐ (brentPS k) ((Ideal.Quotient.mkₐ k (brentPS k)).comp (swapPS k))
    fun a ha => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact map_swapPS_le k (Ideal.mem_map_of_mem _ ha)

theorem swapHat_mk (f : MvPowerSeries Var k) :
    swapHat k (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (swapPS k f) := rfl

theorem swapHat_swapHat (a : Ahat k) : swapHat k (swapHat k a) = a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [swapHat_mk, swapHat_mk, swapPS_swapPS]

/-- **The swap is an automorphism of `Â`** (an involution). -/
noncomputable def swapHatEquiv : Ahat k ≃ₐ[k] Ahat k :=
  AlgEquiv.ofAlgHom (swapHat k) (swapHat k) (AlgHom.ext (swapHat_swapHat k))
    (AlgHom.ext (swapHat_swapHat k))

/-! ### Exchange of the branches -/

/-- The swap on the full parameters. -/
def piF : FIdx → FIdx
  | .inl (g, a, b) => .inl (g, Kv a, Kv b)
  | .inr (.inl x) => .inr (.inl x)
  | .inr (.inr (s, c)) => .inr (.inr (Ks s, c))

theorem piF_piF (w : FIdx) : piF (piF w) = w := by
  rcases w with ⟨g, a, b⟩ | x | ⟨s, c⟩ <;> rfl

theorem hasSubst_piF : HasSubst (fun w : FIdx => (X (piF w) : MvPowerSeries FIdx k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

/-- The swap of the full parameter ring. -/
noncomputable def swapParamPS : MvPowerSeries FIdx k →ₐ[k] MvPowerSeries FIdx k :=
  substAlgHom (hasSubst_piF k)

theorem swapParamPS_swapParamPS (f : MvPowerSeries FIdx k) :
    swapParamPS k (swapParamPS k f) = f := by
  rw [swapParamPS, substAlgHom_apply, substAlgHom_apply,
    subst_comp_subst_apply (hasSubst_piF k) (hasSubst_piF k)]
  have : (fun w : FIdx => subst (fun w => (X (piF w) : MvPowerSeries FIdx k)) (X (piF w) : MvPowerSeries FIdx k)) =
      (X : FIdx → MvPowerSeries FIdx k) := by
    funext w
    rw [subst_X (hasSubst_piF k), piF_piF]
  rw [this, subst_self]
  rfl

theorem centered_swap : FCentered fun w => (swapParamPS k).toRingHom (tF k w) := by
  intro w
  change constantCoeff (swapParamPS k (X w)) = 0
  rw [swapParamPS, substAlgHom_X]
  exact constantCoeff_X _

theorem swapParams_fullParams :
    swapParams (fullParams (tF k) (centered_tF k)) =
      (fullParams (tF k) (centered_tF k)).map (swapParamPS k).toRingHom := by
  rw [fullParams_map _ _ (centered_swap k)]
  have hX : ∀ w, (swapParamPS k).toRingHom (tF k w) = X (piF w) := fun w => by
    change swapParamPS k (X w) = _
    rw [swapParamPS, substAlgHom_X]
  simp only [swapParams, fullParams, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change conjK (fMat (tF k) g) a b = fMat (fun w => (swapParamPS k).toRingHom (tF k w)) g a b
    rw [conjK_apply]
    simp only [fMat, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
      EmbeddingLike.apply_eq_iff_eq, hX]
    rfl
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change fBlk (tF k) s g a b = fBlk (fun w => (swapParamPS k).toRingHom (tF k w)) s g a b
    simp only [fBlk, Matrix.add_apply, Matrix.of_apply, hX]
    rfl
  · funext s c; apply Units.ext
    change fScal (tF k) (Ks s) c = fScal (fun w => (swapParamPS k).toRingHom (tF k w)) s c
    simp only [fScal, hX]
    rfl

theorem based_swap : Based ((fullParams (tF k) (centered_tF k)).map (swapParamPS k).toRingHom) := by
  rw [fullParams_map _ _ (centered_swap k)]
  exact fullParams_based _

theorem famArg_swap (x : Var) :
    famArg (fullParams (tF k) (centered_tF k)) false (piV x) =
      famArg ((fullParams (tF k) (centered_tF k)).map (swapParamPS k).toRingHom) true x := by
  rw [famArg, famArg, pt_piV, ← coordinates_swapDec, swapDec_value, swapParams_fullParams]
  rfl

/-- **The swap intertwines the two full family maps.** -/
theorem fullHat_swapHat :
    (fullHat k false).comp (swapHat k) = (swapParamPS k).comp (fullHat k true) := by
  apply Ideal.Quotient.algHom_ext
  ext1 f
  change famPull _ (fullParams_based (centered_tF k)) false (swapPS k f) =
    ((swapParamPS k).comp (famPull _ (fullParams_based (centered_tF k)) true)) f
  rw [swapParamPS, ← famPull_map (fullParams_based (centered_tF k)) (hasSubst_piF k)
    (based_swap k) true, famPull_apply, famPull_apply, swapPS, substAlgHom_apply,
    subst_comp_subst_apply (hasSubst_piV k) (hasSubst_famArg (fullParams_based (centered_tF k)) false)]
  congr 1
  funext x
  rw [subst_X (hasSubst_famArg (fullParams_based (centered_tF k)) false), famArg_swap]
  rfl

theorem swapParamPS_injective : Function.Injective (swapParamPS k) := fun f g h => by
  rw [← swapParamPS_swapParamPS k f, h, swapParamPS_swapParamPS]

/-- **The swap exchanges the branches**: `swap⁻¹(𝔭_R) = 𝔭_L` once `dim Â ≤ 197`. -/
theorem comap_swapHat_right (hdim : ringKrullDim (Ahat k) ≤ 197) :
    (branchPrime k false).comap (swapHat k) = branchPrime k true := by
  rw [← ker_fullHat k false hdim, ← ker_fullHat k true hdim]
  ext a
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
  change (fullHat k false).comp (swapHat k) a = 0 ↔ _
  rw [fullHat_swapHat, AlgHom.comp_apply]
  constructor
  · intro h
    exact swapParamPS_injective k (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem comap_swapHat_swapHat (I : Ideal (Ahat k)) :
    (I.comap (swapHat k)).comap (swapHat k) = I := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, swapHat_swapHat]

theorem comap_swapHat_left (hdim : ringKrullDim (Ahat k) ≤ 197) :
    (branchPrime k true).comap (swapHat k) = branchPrime k false := by
  rw [← comap_swapHat_right k hdim, comap_swapHat_swapHat]

/-- The swap fixes the branch intersection `𝔭_L + 𝔭_R`. -/
theorem comap_swapHat_sup (hdim : ringKrullDim (Ahat k) ≤ 197) :
    (branchPrime k true ⊔ branchPrime k false).comap (swapHat k) =
      branchPrime k true ⊔ branchPrime k false := by
  have hle : branchPrime k true ⊔ branchPrime k false ≤
      (branchPrime k true ⊔ branchPrime k false).comap (swapHat k) := by
    refine sup_le ?_ ?_
    · rw [← comap_swapHat_right k hdim]
      exact Ideal.comap_mono le_sup_right
    · rw [← comap_swapHat_left k hdim]
      exact Ideal.comap_mono le_sup_left
  refine le_antisymm ?_ hle
  have h := Ideal.comap_mono (f := swapHat k) hle
  rwa [comap_swapHat_swapHat] at h

theorem comap_swapHat_right_charThree [CharP k 3] :
    (branchPrime k false).comap (swapHat k) = branchPrime k true :=
  comap_swapHat_right k (ringKrullDim_Ahat_le_charThree k)

theorem comap_swapHat_right_charZero [CharZero k] :
    (branchPrime k false).comap (swapHat k) = branchPrime k true :=
  comap_swapHat_right k (ringKrullDim_Ahat_le_charZero k)

end Formal

end Brent.Formal
