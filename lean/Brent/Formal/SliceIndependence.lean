import Brent.Formal.OrbitDimension
import Brent.Formal.Branches

/-!
# Slice independence and the orbit subgerm (§3 and §6)

* **Slice independence.** For either family, take the formal map from the *full* parameter space
  (all global, block and scaling parameters) at the identity. Its comorphism
  `Â → k⟦230⟧` has prime kernel, contained in the kernel `𝔭_L` (resp. `𝔭_R`) of the chosen
  197-parameter slice, because the slice is a substitution of the full parameters. Minimality
  forces equality. So the branch does not depend on the slice used to detect it.
* **Orbit subgerm.** The scheme-theoretic intersection `Â ⧸ (𝔭_L + 𝔭_R) ≃ k⟦c⟧`, computed in the
  coordinate change `H`, is the formal orbit subgerm of the group slice of `OrbitDimension`: the
  kernel of the gauge-fixed group orbit comorphism `Â → k⟦c⟧` is `𝔭_L + 𝔭_R`.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries TangentData

set_option linter.unusedSectionVars false

/-! ### Restriction commutes with substitution -/

open MvPowerSeries.WithPiTopology in
/-- Setting variables to zero commutes with substitution. -/
theorem killCompl_subst {k : Type} [Field k] {σ τ υ : Type} [Finite υ] (e : σ ↪ τ)
    {a : υ → MvPowerSeries τ k} (ha0 : ∀ x, constantCoeff (a x) = 0) (f : MvPowerSeries υ k) :
    killCompl e (subst a f) = subst (fun x => killCompl e (a x)) f := by
  letI : UniformSpace k := ⊥
  haveI : DiscreteUniformity k := ⟨rfl⟩
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hb : HasSubst (fun x => killCompl (R := k) e (a x)) := by
    apply hasSubst_of_constantCoeff_zero
    intro x
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
      coeff_zero_eq_constantCoeff_apply, ha0]
  have hε : Continuous (killCompl (R := k) e) :=
    continuous_pi fun x => continuous_coeff k (Finsupp.embDomain e x)
  rw [← coe_substAlgHom ha, substAlgHom_eq_aeval, ← AlgHom.comp_apply, comp_aeval _ hε,
    ← coe_substAlgHom hb, substAlgHom_eq_aeval]

/-! ### Comorphisms of families of solutions -/

section Gen

variable {k : Type} [Field k] {W : Type}

/-- Parameters through the identity. -/
def Based (P : FamilyParameters (MvPowerSeries W k)) : Prop :=
  P.map constantCoeff = FamilyParameters.one k

/-- The centered family `P·p − p`. -/
noncomputable def famArg (P : FamilyParameters (MvPowerSeries W k)) (left : Bool) (x : Var) :
    MvPowerSeries W k :=
  (P.value left).coordinates x - C (pt k x)

theorem constantCoeff_famArg {P : FamilyParameters (MvPowerSeries W k)} (hP : Based P)
    (left : Bool) (x : Var) : constantCoeff (famArg P left x) = 0 := by
  rw [famArg, map_sub, ← LowerBound.coordinates_map, FamilyParameters.value_map, hP,
    FamilyParameters.value_one, constantCoeff_C]
  exact sub_self _

theorem hasSubst_famArg {P : FamilyParameters (MvPowerSeries W k)} (hP : Based P)
    (left : Bool) : HasSubst (famArg P left) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_famArg hP left)

/-- The comorphism `k⟦z⟧ → k⟦W⟧` of a family. -/
noncomputable def famPull (P : FamilyParameters (MvPowerSeries W k)) (hP : Based P)
    (left : Bool) : MvPowerSeries Var k →ₐ[k] MvPowerSeries W k :=
  substAlgHom (hasSubst_famArg hP left)

theorem famPull_apply {P : FamilyParameters (MvPowerSeries W k)} (hP : Based P) (left : Bool)
    (f : MvPowerSeries Var k) : famPull P hP left f = subst (famArg P left) f := by
  rw [famPull, substAlgHom_apply]

theorem famPull_eqPS {P : FamilyParameters (MvPowerSeries W k)} (hP : Based P) (left : Bool)
    (abc : EquationIndex SquareVertex) : famPull P hP left (eqPS k abc) = 0 := by
  rw [famPull_apply, subst_eqPS (hasSubst_famArg hP left)]
  exact centered_zero _ (FamilyParameters.value_solves _ _) _ (fun x => rfl) abc

/-- The comorphism on `Â`. -/
noncomputable def famHat (P : FamilyParameters (MvPowerSeries W k)) (hP : Based P)
    (left : Bool) : Ahat k →ₐ[k] MvPowerSeries W k :=
  Ideal.Quotient.liftₐ (brentPS k) (famPull P hP left) fun a ha => by
    have : brentPS k ≤ RingHom.ker (famPull P hP left) := by
      rw [brentPS, Ideal.span_le]
      rintro _ ⟨abc, rfl⟩
      exact famPull_eqPS hP left abc
    exact this ha

theorem famHat_mk {P : FamilyParameters (MvPowerSeries W k)} (hP : Based P) (left : Bool)
    (f : MvPowerSeries Var k) : famHat P hP left (Ideal.Quotient.mk _ f) = famPull P hP left f :=
  rfl

theorem famPull_congr {P P' : FamilyParameters (MvPowerSeries W k)} (h : P = P') (hP : Based P)
    (hP' : Based P') (left : Bool) : famPull P hP left = famPull P' hP' left := by
  subst h; rfl

/-- Substituting into the parameters composes the comorphism with the substitution. -/
theorem famPull_map {W' : Type} {P : FamilyParameters (MvPowerSeries W k)} (hP : Based P)
    {σ : W → MvPowerSeries W' k} (hσ : HasSubst σ)
    (hP' : Based (P.map (substAlgHom (R := k) hσ).toRingHom)) (left : Bool) :
    famPull (P.map (substAlgHom (R := k) hσ).toRingHom) hP' left =
      (substAlgHom (R := k) hσ).comp (famPull P hP left) := by
  ext1 f
  rw [AlgHom.comp_apply, famPull_apply, famPull_apply, substAlgHom_apply,
    subst_comp_subst_apply (hasSubst_famArg hP left) hσ]
  congr 1
  funext x
  rw [famArg, famArg, ← substAlgHom_apply hσ, map_sub, algHom_C]
  congr 1
  change _ = (substAlgHom (R := k) hσ).toRingHom _
  rw [← LowerBound.coordinates_map, FamilyParameters.value_map]

end Gen

/-! ### The full parameter space of a family -/

section Full

variable {k : Type} [Field k] {W : Type}

/-- All parameters of a family: 48 global, 84 block and 98 scaling parameters. -/
abbrev FIdx :=
  (Fin 3 × SquareVertex × SquareVertex) ⊕ ((Fin 7 × Fin 3 × Fin 2 × Fin 2) ⊕ (SquareSummand × Fin 2))

theorem card_FIdx : Fintype.card FIdx = 230 := rfl

/-- Parameters with zero constant term. -/
def FCentered (t : FIdx → MvPowerSeries W k) : Prop := ∀ w, constantCoeff (t w) = 0

noncomputable def fMat (t : FIdx → MvPowerSeries W k) (g : Fin 3) :
    Matrix SquareVertex SquareVertex (MvPowerSeries W k) :=
  1 + Matrix.of fun a b => t (.inl (g, a, b))

noncomputable def fBlk (t : FIdx → MvPowerSeries W k) (s : Fin 7) (g : Fin 3) :
    Matrix (Fin 2) (Fin 2) (MvPowerSeries W k) :=
  1 + Matrix.of fun a b => t (.inr (.inl (s, g, a, b)))

noncomputable def fScal (t : FIdx → MvPowerSeries W k) (s : SquareSummand) (c : Fin 2) :
    MvPowerSeries W k :=
  1 + t (.inr (.inr (s, c)))

theorem isUnit_fMat {t : FIdx → MvPowerSeries W k} (ht : FCentered t) (g : Fin 3) :
    IsUnit (fMat t g) := by
  have h : (fMat t g).map constantCoeff = 1 := by
    ext a b
    simp [fMat, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply,
      apply_ite constantCoeff]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
    RingHom.mapMatrix_apply, h, Matrix.det_one]
  exact isUnit_one

theorem isUnit_fBlk {t : FIdx → MvPowerSeries W k} (ht : FCentered t) (s : Fin 7) (g : Fin 3) :
    IsUnit (fBlk t s g) := by
  have h : (fBlk t s g).map constantCoeff = 1 := by
    ext a b
    simp [fBlk, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply,
      apply_ite constantCoeff]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
    RingHom.mapMatrix_apply, h, Matrix.det_one]
  exact isUnit_one

theorem isUnit_fScal {t : FIdx → MvPowerSeries W k} (ht : FCentered t) (s : SquareSummand)
    (c : Fin 2) : IsUnit (fScal t s c) := by
  rw [isUnit_iff_constantCoeff, fScal, map_add, map_one, ht, add_zero]
  exact isUnit_one

/-- The group element with all parameters `t`. -/
noncomputable def fullParams (t : FIdx → MvPowerSeries W k) (ht : FCentered t) :
    FamilyParameters (MvPowerSeries W k) :=
  ⟨fun g => (isUnit_fMat ht g).unit, fun s g => (isUnit_fBlk ht s g).unit,
   fun s c => (isUnit_fScal ht s c).unit⟩

theorem fullParams_based {t : FIdx → MvPowerSeries W k} (ht : FCentered t) :
    Based (fullParams t ht) := by
  simp only [Based, fullParams, FamilyParameters.map, FamilyParameters.one,
    FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; ext a b
    change constantCoeff (fMat t g a b) = _
    simp [fMat, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply,
      apply_ite constantCoeff]
  · funext s g; apply Units.ext; ext a b
    change constantCoeff (fBlk t s g a b) = _
    simp [fBlk, show ∀ w, constantCoeff (t w) = 0 from ht, Matrix.one_apply,
      apply_ite constantCoeff]
  · funext s c; apply Units.ext
    change constantCoeff (fScal t s c) = 1
    rw [fScal, map_add, map_one, ht, add_zero]

theorem fullParams_map {W' : Type} {t : FIdx → MvPowerSeries W k} (ht : FCentered t)
    (φ : MvPowerSeries W k →+* MvPowerSeries W' k) (hφ : FCentered fun w => φ (t w)) :
    (fullParams t ht).map φ = fullParams (fun w => φ (t w)) hφ := by
  simp only [fullParams, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change φ (fMat t g a b) = fMat (fun w => φ (t w)) g a b
    by_cases h : a = b <;> simp [fMat, h]
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change φ (fBlk t s g a b) = fBlk (fun w => φ (t w)) s g a b
    by_cases h : a = b <;> simp [fBlk, h]
  · funext s c; apply Units.ext
    change φ (fScal t s c) = fScal (fun w => φ (t w)) s c
    simp [fScal]

theorem fullParams_congr {t t' : FIdx → MvPowerSeries W k} (h : t = t') (ht : FCentered t)
    (ht' : FCentered t') : fullParams t ht = fullParams t' ht' := by
  subst h; rfl

variable (k)

/-- The universal parameters. -/
noncomputable def tF : FIdx → MvPowerSeries FIdx k := fun w => X w

theorem centered_tF : FCentered (tF k) := fun w => constantCoeff_X w

/-- **The comorphism of the full parameter map of a family**, `Â → k⟦230⟧`. -/
noncomputable def fullHat (left : Bool) : Ahat k →ₐ[k] MvPowerSeries FIdx k :=
  famHat (fullParams (tF k) (centered_tF k)) (fullParams_based _) left

/-- Its kernel is prime: `k⟦230⟧` is a domain. -/
theorem ker_fullHat_isPrime (left : Bool) : (RingHom.ker (fullHat k left)).IsPrime :=
  RingHom.ker_isPrime _

variable {k}

/-- The full parameters of an assignment of the frame directions. -/
noncomputable def specF (t : Assignment k W) : FIdx → MvPowerSeries W k
  | .inl (g, a, b) => ∑ i, t.1 i * C (tGlobal k g i a b)
  | .inr (.inl (s, g, a, b)) => ∑ i, t.1 i * C (tBlock k s g i a b)
  | .inr (.inr (s, c)) => ∑ i, t.1 i * C (tScale k s c i)

theorem centered_specF (t : Assignment k W) : FCentered (specF t) := by
  intro w
  rcases w with ⟨g, a, b⟩ | ⟨s, g, a, b⟩ | ⟨s, c⟩ <;>
    simp [specF, map_sum, t.2]

theorem paramsOf_eq_fullParams (t : Assignment k W) :
    paramsOf k t = fullParams (specF t) (centered_specF t) := by
  simp only [paramsOf, fullParams, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change psMat t (tGlobal k g) a b = fMat (specF t) g a b
    rw [psMat_apply]; rfl
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change psMat t (tBlock k s g) a b = fBlk (specF t) s g a b
    rw [psMat_apply]; rfl
  · funext s c; apply Units.ext
    rfl

theorem hasSubst_specF [Finite W] (t : Assignment k W) : HasSubst (specF t) :=
  hasSubst_of_constantCoeff_zero (centered_specF t)

/-- The family of an assignment is the full family substituted along `specF`. -/
theorem famPull_paramsOf [Finite W] (t : Assignment k W) (hP : Based (paramsOf k t))
    (left : Bool) :
    famPull (paramsOf k t) hP left =
      (substAlgHom (R := k) (hasSubst_specF t)).comp
        (famPull (fullParams (tF k) (centered_tF k)) (fullParams_based _) left) := by
  have hmap : (fullParams (tF k) (centered_tF k)).map (substAlgHom (R := k) (hasSubst_specF t)).toRingHom =
      paramsOf k t := by
    rw [fullParams_map _ _ (by
      intro w
      change constantCoeff (substAlgHom (R := k) (hasSubst_specF t) (X w)) = 0
      rw [substAlgHom_X]
      exact centered_specF t w), paramsOf_eq_fullParams]
    apply fullParams_congr
    funext w
    change substAlgHom (R := k) (hasSubst_specF t) (X w) = _
    rw [substAlgHom_X]
  rw [← famPull_map (fullParams_based (centered_tF k)) (hasSubst_specF t) (hmap ▸ hP) left]
  exact famPull_congr hmap.symm _ _ left

end Full

/-! ### The branch maps factor through the full parameter maps -/

section Branch

variable (k : Type) [Field k]

theorem based_paramsOf {W : Type} (t : Assignment k W) : Based (paramsOf k t) :=
  paramsOf_constantCoeff k t

/-- The branch assignment: the chart's frame directions, the others set to zero. -/
noncomputable def branchAssign (left : Bool) : Assignment k (BranchVar k left) :=
  (selAssign k (NIdx k) fun i => InChart i left).map (killR k left) (kill_zero_const k left)

theorem kill_H (left : Bool) (x : Var) :
    kill k left (H k x) = famArg (paramsOf k (branchAssign k left)) left x := by
  rw [famArg, branchAssign, ← kill_coordinates]
  cases left
  · exact kill_H_right k x
  · exact kill_H_left k x

/-- **The branch map is the comorphism of the chosen slice.** -/
theorem branchMap_mk_eq (left : Bool) (f : MvPowerSeries Var k) :
    branchMap k left (mkA k f) =
      famPull (paramsOf k (branchAssign k left)) (based_paramsOf k _) left f := by
  rw [branchMap_mk, Φ_apply, kill, killCompl_subst _ (constantCoeff_H k), famPull_apply]
  congr 1
  funext x
  exact kill_H k left x

/-- **The chosen slice is a substitution of the full parameters.** -/
theorem branchMap_eq (left : Bool) :
    branchMap k left =
      ((substAlgHom (R := k) (hasSubst_specF (branchAssign k left))).comp (fullHat k left)).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext1 f
  change branchMap k left (mkA k f) = _
  rw [branchMap_mk_eq, famPull_paramsOf]
  rfl

theorem ker_fullHat_le (left : Bool) : RingHom.ker (fullHat k left) ≤ branchPrime k left := by
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [branchPrime, RingHom.mem_ker, branchMap_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.comp_apply, ha, map_zero]

/-- **Slice independence.** If `dim Â ≤ 197`, the kernel of the full parameter map of either
family is the branch prime. -/
theorem ker_fullHat (left : Bool) (hdim : ringKrullDim (Ahat k) ≤ 197) :
    RingHom.ker (fullHat k left) = branchPrime k left :=
  le_antisymm (ker_fullHat_le k left)
    ((branchPrime_minimal k left hdim).2 ⟨ker_fullHat_isPrime k left, bot_le⟩
      (ker_fullHat_le k left))

theorem ker_fullHat_charThree [CharP k 3] (left : Bool) :
    RingHom.ker (fullHat k left) = branchPrime k left :=
  ker_fullHat k left (ringKrullDim_Ahat_le_charThree k)

theorem ker_fullHat_charZero [CharZero k] (left : Bool) :
    RingHom.ker (fullHat k left) = branchPrime k left :=
  ker_fullHat k left (ringKrullDim_Ahat_le_charZero k)

/-- **Any slice detects the same branch.** If restricting the full parameter map along any ring
map `φ` gives a minimal prime kernel, that kernel is the branch prime. -/
theorem slice_independent {S : Type} [CommRing S] (left : Bool)
    (hdim : ringKrullDim (Ahat k) ≤ 197) (φ : MvPowerSeries FIdx k →+* S)
    (hmin : RingHom.ker (φ.comp (fullHat k left).toRingHom) ∈ minimalPrimes (Ahat k)) :
    RingHom.ker (φ.comp (fullHat k left).toRingHom) = branchPrime k left := by
  have hle : branchPrime k left ≤ RingHom.ker (φ.comp (fullHat k left).toRingHom) := by
    rw [← ker_fullHat k left hdim]
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [RingHom.comp_apply]
    change φ (fullHat k left a) = 0
    rw [ha, map_zero]
  exact le_antisymm (hmin.2 ⟨inferInstance, bot_le⟩ hle) hle

end Branch

/-! ### The orbit subgerm -/

section Orbit

variable {k : Type} [Field k] {W : Type}

/-- The orbit parameters of an assignment of the orbit directions. -/
noncomputable def specO (t : Assignment k W) : GIdx → MvPowerSeries W k
  | .inl (g, a, b) => ∑ i, t.1 i * C (tGlobal k g i a b)
  | .inr (s, c) => if c = 0 then ∑ i, t.1 i * C (tScale k s 0 i) + ∑ i, t.1 i * C (tScale k s 1 i)
      else -∑ i, t.1 i * C (tScale k s 1 i)

theorem centered_specO (t : Assignment k W) : Centered (specO t) := by
  intro w
  rcases w with ⟨g, a, b⟩ | ⟨s, c⟩
  · simp [specO, map_sum, t.2]
  · simp only [specO]
    split_ifs <;> simp [map_sum, t.2]

theorem paramsOf_eq_orbParams (t : Assignment k W) (ht : OrbitOnly k t) :
    paramsOf k t = orbParams (specO t) (centered_specO t) := by
  have hb := blockTrivial_of_orbitOnly k t ht
  change FamilyParameters.mk _ _ _ = FamilyParameters.mk _ _ _
  simp only [FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    change psMat t (tGlobal k g) a b = orbMat (specO t) g a b
    rw [psMat_apply]; rfl
  · funext s g
    exact hb s g
  · funext s c; apply Units.ext
    change psScal t (tScale k s c) = orbScal (specO t) s c
    unfold psScal orbScal
    fin_cases c
    · simp [specO]; ring
    · simp [specO]

theorem hasSubst_specO [Finite W] (t : Assignment k W) : HasSubst (specO t) :=
  hasSubst_of_constantCoeff_zero (centered_specO t)

variable (k)

set_option maxRecDepth 100000 in
/-- No orbit frame direction moves the gauge entry `(1,1),(1,1)` of a global factor. -/
theorem gauge_origin : ∀ i : Fin 251, i.val < 143 → ∀ g : Fin 3,
    (((frameOrigin ℤ i).global g).val (1, 1) (1, 1)).snd = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem slot_none : ∀ w : GIdx, slot w = none → ∃ g : Fin 3, w = .inl (g, (1, 1), (1, 1)) := by
  decide +kernel

theorem tGlobal_gauge (g : Fin 3) (i : Fin 251) (hi : i.val < 143) :
    tGlobal k g i (1, 1) (1, 1) = 0 := by
  change ((((frameOrigin ℤ i).global g).val (1, 1) (1, 1)).snd : k) = 0
  rw [gauge_origin i hi g, Int.cast_zero]

/-- The orbit assignment: the orbit directions `c`, the others set to zero. -/
noncomputable def orbitAssign : Assignment k (OrbitVar k) :=
  (selAssign k (NIdx k) fun i => i.val < 143).map (killO k) fun f hf => by
    rw [← coeff_zero_eq_constantCoeff_apply, killO, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_eq_constantCoeff_apply, hf]

theorem killO_X_drop {w : Brent.Formal.W k} (hw : ¬ KeepO k w) : killO k (X w) = 0 := by
  change killCompl (embO k) (X w) = 0
  apply killCompl_X_eq_zero
  simpa [embO] using hw

theorem killO_C (r : k) : killO k (C r) = C r := killCompl_C r

theorem orbitAssign_orbitOnly : OrbitOnly k (orbitAssign k) := by
  intro i hi
  change killO k (selVar k (NIdx k) (fun i : Fin 251 => i.val < 143) i) = 0
  rw [selVar, if_neg (by omega), map_zero]

theorem killO_selAssign (P : Fin 251 → Prop) [DecidablePred P] (hP : ∀ i : Fin 251, i.val < 143 → P i) :
    (selAssign k (NIdx k) P).map (killO k) (orbitAssign._proof_1 k) = orbitAssign k := by
  apply Subtype.ext
  funext i
  change killO k (selVar k (NIdx k) P i) = killO k (selVar k (NIdx k) (fun i : Fin 251 => i.val < 143) i)
  by_cases hi : i.val < 143
  · simp only [selVar, if_pos (hP i hi), if_pos hi]
  · have hX : killO k (X (Sum.inl i)) = 0 := killO_X_drop k (by simpa [KeepO] using hi)
    unfold selVar
    split_ifs <;> simp [hX]

theorem killO_coordinates (P : Fin 251 → Prop) [DecidablePred P] (side : Bool) (x : Var) :
    killO k ((selFamily k (NIdx k) P side).coordinates x) =
      ((paramsOf k ((selAssign k (NIdx k) P).map (killO k) (orbitAssign._proof_1 k))).value side).coordinates x := by
  rw [← LowerBound.coordinates_map, selFamily, FamilyParameters.value_map, paramsOf_map]
  intro r
  exact killO_C k r

theorem killO_H (x : Var) :
    killO k (H k x) = famArg (paramsOf k (orbitAssign k)) false x := by
  have hL : killO k ((famL k).coordinates x) = killO k ((famO k).coordinates x) := by
    rw [famL, famO, killO_coordinates, killO_coordinates,
      killO_selAssign k _ (fun i hi => by simp [InChart]; omega),
      killO_selAssign k _ (fun i hi => hi), value_orbit_left_eq_right k _ (orbitAssign_orbitOnly k)]
  have hR : killO k ((famR k).coordinates x) = killO k ((famO k).coordinates x) := by
    rw [famR, famO, killO_coordinates, killO_coordinates,
      killO_selAssign k _ (fun i hi => by simp [InChart]; omega),
      killO_selAssign k _ (fun i hi => hi)]
  have hN : killO k (∑ n : NIdx k, C (B k (Sum.inr n) x) * X (Sum.inr n)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [map_mul, killO_X_drop k (by simp [KeepO]), mul_zero]
  rw [famArg, famO, killO_coordinates, killO_selAssign k _ (fun i hi => hi)] at *
  simp only [H, map_add, map_sub, hL, hR, hN, killO_C, famO]
  rw [killO_coordinates, killO_selAssign k _ (fun i hi => hi)]
  ring

/-- **The frame orbit map is the comorphism of the frame's orbit slice.** -/
theorem orbitMap_mk_eq (f : MvPowerSeries Var k) :
    orbitMap k (mkA k f) = famPull (paramsOf k (orbitAssign k)) (based_paramsOf k _) false f := by
  change killCompl (embO k) (Φ k f) = _
  rw [Φ_apply, killCompl_subst _ (constantCoeff_H k), famPull_apply]
  congr 1
  funext x
  exact killO_H k x

/-- The frame's orbit slice, expressed in the group parameters. -/
theorem orbitMap_eq :
    orbitMap k = ((substAlgHom (R := k) (hasSubst_specO (orbitAssign k))).comp (orbitHat k)).toRingHom := by
  have hP := paramsOf_eq_orbParams (orbitAssign k) (orbitAssign_orbitOnly k)
  have hmap : (orbParams (tΓ k) (centered_tΓ k)).map
      (substAlgHom (R := k) (hasSubst_specO (orbitAssign k))).toRingHom = paramsOf k (orbitAssign k) := by
    rw [orbParams_map _ _ (by
      intro w
      change constantCoeff (substAlgHom (R := k) (hasSubst_specO (orbitAssign k)) (X w)) = 0
      rw [substAlgHom_X]
      exact centered_specO _ w), hP]
    apply orbParams_congr
    funext w
    change substAlgHom (R := k) (hasSubst_specO (orbitAssign k)) (X w) = _
    rw [substAlgHom_X]
  apply Ideal.Quotient.ringHom_ext
  ext1 f
  change orbitMap k (mkA k f) = _
  rw [orbitMap_mk_eq, famPull_congr hmap.symm _ (hmap ▸ based_paramsOf k _),
    famPull_map (orbParams_constantCoeff (centered_tΓ k))]
  rfl

/-- The frame's orbit slice factors through the group slice. -/
noncomputable def sliceToFrame : MvPowerSeries (Fin 143) k →ₐ[k] MvPowerSeries (OrbitVar k) k :=
  substAlgHom (R := k) (hasSubst_of_constantCoeff_zero fun j : Fin 143 =>
    centered_specO (orbitAssign k) (rowsA j))

theorem specO_gauge (g : Fin 3) : specO (orbitAssign k) (.inl (g, (1, 1), (1, 1))) = 0 := by
  simp only [specO]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < 143
  · rw [tGlobal_gauge k g i hi, map_zero, mul_zero]
  · rw [orbitAssign_orbitOnly k i (by omega), zero_mul]

theorem sliceToFrame_tS (w : GIdx) : sliceToFrame k (tS k w) = specO (orbitAssign k) w := by
  unfold tS
  cases h : slot w with
  | none =>
    obtain ⟨g, rfl⟩ := slot_none w h
    rw [map_zero, specO_gauge]
  | some j =>
    dsimp only
    rw [sliceToFrame, substAlgHom_X, slot_some h]

theorem orbitMap_eq_slice :
    orbitMap k = ((sliceToFrame k).comp (sliceHat k)).toRingHom := by
  rw [orbitMap_eq, sliceHat_eq]
  congr 1
  rw [← AlgHom.comp_assoc]
  congr 1
  apply AlgHom.ext
  intro f
  rw [AlgHom.comp_apply, gaugeRestrict, substAlgHom_apply, substAlgHom_apply, sliceToFrame,
    substAlgHom_apply, subst_comp_subst_apply (hasSubst_tS k)
      (hasSubst_of_constantCoeff_zero fun j : Fin 143 => centered_specO (orbitAssign k) (rowsA j))]
  congr 1
  funext w
  rw [← sliceToFrame_tS k w, sliceToFrame, substAlgHom_apply]

theorem ker_sliceHat_le : RingHom.ker (sliceHat k) ≤ branchPrime k true ⊔ branchPrime k false := by
  rw [← ker_orbitMap, orbitMap_eq_slice]
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  change sliceToFrame k (sliceHat k a) = 0
  rw [ha, map_zero]

/-- A prime inside the kernel of a surjection onto `k⟦σ⟧` with the same dimension is the
kernel. -/
theorem eq_ker_of_le {R : Type} [CommRing R] {σ : Type} [Fintype σ]
    (f : R →+* MvPowerSeries σ k) (hf : Function.Surjective f) (q : Ideal R) [q.IsPrime]
    (hq : q ≤ RingHom.ker f) (hdim : ringKrullDim (R ⧸ q) ≤ Fintype.card σ) :
    q = RingHom.ker f := by
  let f' : R ⧸ q →+* MvPowerSeries σ k := Ideal.Quotient.lift q f hq
  have hf' : Function.Surjective f' := Ideal.Quotient.lift_surjective_of_surjective q hq hf
  have hmin := ker_mem_minimalPrimes f' hf' (varChain σ k) (varChain_head σ k)
    (by rw [varChain_length]; exact hdim)
  have hbot : RingHom.ker f' = ⊥ :=
    le_antisymm (hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le) bot_le
  refine le_antisymm hq fun a ha => ?_
  have : Ideal.Quotient.mk q a ∈ RingHom.ker f' := by
    rw [RingHom.mem_ker]
    exact ha
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

/-- **The intersection is the group orbit subgerm**: the kernel of the gauge-fixed group orbit
comorphism `Â → k⟦c⟧` is `𝔭_L + 𝔭_R`. -/
theorem ker_sliceHat : RingHom.ker (sliceHat k) = branchPrime k true ⊔ branchPrime k false := by
  rw [← ker_orbitMap]
  haveI : (RingHom.ker (sliceHat k)).IsPrime := RingHom.ker_isPrime _
  refine eq_ker_of_le k (orbitMap k) (orbitMap_surjective k) _ ?_ ?_
  · rw [ker_orbitMap]; exact ker_sliceHat_le k
  · have e : (Ahat k ⧸ RingHom.ker (sliceHat k).toRingHom) ≃+* MvPowerSeries (Fin 143) k :=
      RingHom.quotientKerEquivOfSurjective (f := (sliceHat k).toRingHom) (sliceHat_surjective k)
    rw [card_orbitVar]
    change ringKrullDim (Ahat k ⧸ RingHom.ker (sliceHat k).toRingHom) ≤ _
    rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_slice]
    rfl

/-- `Â ⧸ (𝔭_L + 𝔭_R) ≃ k⟦c⟧` through the group slice. -/
noncomputable def orbitSubgermEquiv :
    (Ahat k ⧸ (branchPrime k true ⊔ branchPrime k false)) ≃+* MvPowerSeries (Fin 143) k :=
  (Ideal.quotEquivOfEq (ker_sliceHat k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (sliceHat k).toRingHom) (sliceHat_surjective k))

end Orbit

end Brent.Formal
