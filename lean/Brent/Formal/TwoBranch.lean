import Brent.Formal.Completion
import Brent.KernelCheck.HilbertValues

/-!
# `H(2) = 30978` against the two-branch value `28710`

The degree-two Hilbert value `30978` of the algebraic local ring `A` transfers to `Â` and to
`SquareCompletion`, because `A ⧸ 𝔪ⁿ ≃ Â ⧸ 𝔪̂ⁿ`. In the coordinates `(c, x, y, n)` of F5, the
reduced union of the two branches is `Â ⧸ (𝔭_L ⊓ 𝔭_R)`: there `n = 0` and `x_i y_j = 0`, and its
degree-two Hilbert value is `binom(252, 2) − 54 · 54 = 28710`. Hence `𝔭_L ⊓ 𝔭_R ≠ 0`, so the
completed local ring is nonreduced or has a minimal prime other than `𝔭_L`, `𝔭_R`.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries IsLocalRing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

/-! ### Transport of Hilbert values -/

section Transport

variable {k : Type*} [Field k] {R S : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]
  [CommRing S] [IsLocalRing S] [Algebra k S]

/-- A `k`-algebra map that detects `𝔪ⁿ` for `n = d, d + 1` and is onto modulo `𝔪^(d+1)`
preserves `H(d)`. -/
theorem hilbertValue_eq_of_algHom (f : R →ₐ[k] S) (d : ℕ)
    (hmem : ∀ n a, f a ∈ maximalIdeal S ^ n ↔ a ∈ maximalIdeal R ^ n)
    (hsurj : ∀ b, ∃ a, b - f a ∈ maximalIdeal S ^ (d + 1)) :
    hilbertValue k R d = hilbertValue k S d := by
  have hle : powK k R (d + 1) ≤ (powK k S (d + 1)).comap f.toLinearMap :=
    fun a ha => (hmem (d + 1) a).mpr ha
  let L := (powK k R (d + 1)).mapQ (powK k S (d + 1)) f.toLinearMap hle
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (hmem (d + 1) a).mp hx
  have hmap : gradedPiece k S d = (gradedPiece k R d).map L := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨a, ha⟩ := hsurj b
      have hfa : f a ∈ maximalIdeal S ^ d := by
        have h1 : b - f a ∈ maximalIdeal S ^ d := Ideal.pow_le_pow_right (Nat.le_succ d) ha
        have := Ideal.sub_mem _ (show b ∈ maximalIdeal S ^ d from hb) h1
        rwa [sub_sub_cancel] at this
      refine ⟨proj k R d a, proj_mem d ((hmem d a).mp hfa), ?_⟩
      change Submodule.Quotient.mk (f a) = Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq, ← neg_mem_iff, neg_sub]
      exact ha
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact proj_mem d ((hmem d a).mpr ha)
  rw [hilbertValue, hilbertValue, hmap]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hL _))

omit [Algebra k R] [Algebra k S] in
/-- A surjective map of local rings sends the maximal ideal onto the maximal ideal. -/
theorem map_maximalIdeal_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    (maximalIdeal R).map f = maximalIdeal S := by
  have hmax : (Ideal.comap f (maximalIdeal S)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hf
  rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.map_comap_of_surjective _ hf]

/-- `k`-algebra isomorphisms of local rings preserve the Hilbert function. -/
theorem hilbertValue_eq_of_bijective (f : R →ₐ[k] S) (hf : Function.Bijective f) (d : ℕ) :
    hilbertValue k R d = hilbertValue k S d := by
  refine hilbertValue_eq_of_algHom f d (fun n a => ?_) (fun b => ?_)
  · rw [← map_maximalIdeal_of_surjective f.toRingHom hf.2, ← Ideal.map_pow]
    change f.toRingHom a ∈ _ ↔ _
    rw [Ideal.mem_map_iff_of_surjective f.toRingHom hf.2]
    constructor
    · rintro ⟨x, hx, hxa⟩
      rwa [← hf.1 hxa]
    · exact fun ha => ⟨a, ha, rfl⟩
  · obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨a, by rw [sub_self]; exact Ideal.zero_mem _⟩

/-- `hilbertValue_le_of_le_span` for any finite index type. -/
theorem hilbertValue_le_of_le_span' {d : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → R ⧸ powK k R (d + 1)) (hv : gradedPiece k R d ≤ Submodule.span k (Set.range v)) :
    FiniteDimensional k (gradedPiece k R d) ∧ hilbertValue k R d ≤ Fintype.card ι := by
  haveI : FiniteDimensional k (Submodule.span k (Set.range v)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range v)
  exact ⟨Submodule.finiteDimensional_of_le hv,
    (Submodule.finrank_mono hv).trans (finrank_range_le_card v)⟩

/-- `le_hilbertValue` for any finite index type. -/
theorem le_hilbertValue' {d : ℕ} {ι : Type*} [Fintype ι] [FiniteDimensional k (gradedPiece k R d)]
    (Λ : R →ₗ[k] (ι → k)) (hΛ : ∀ a ∈ maximalIdeal R ^ (d + 1), Λ a = 0)
    {κ : Type*} (y : κ → R) (hy : ∀ i, y i ∈ maximalIdeal R ^ d)
    (hspan : Submodule.span k (Set.range fun i => Λ (y i)) = ⊤) :
    Fintype.card ι ≤ hilbertValue k R d := by
  let L : (R ⧸ powK k R (d + 1)) →ₗ[k] (ι → k) :=
    (powK k R (d + 1)).liftQ Λ fun a ha => hΛ a ha
  have hL : (gradedPiece k R d).map L = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨proj k R d (y i), proj_mem d (hy i), rfl⟩
  have h := Submodule.finrank_map_le L (gradedPiece k R d)
  rw [hL, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h

end Transport

variable (k : Type) [Field k]

/-! ### `H(2)` of `Â` and of `SquareCompletion` -/

theorem ψ_algebraMap (r : k) : ψ k (algebraMap k (Aalg k) r) = algebraMap k (Ahat k) r := by
  rw [← (toA k).commutes r, MvPolynomial.algebraMap_eq, ψ_toPoint]
  simp [ψ0]
  rfl

/-- `ψ` as a `k`-algebra map. -/
noncomputable def ψalg : Aalg k →ₐ[k] Ahat k := { ψ k with commutes' := ψ_algebraMap k }

theorem hilbertValue_Ahat (d : ℕ) : hilbertValue k (Ahat k) d = hilbertValue k (Aalg k) d := by
  refine (hilbertValue_eq_of_algHom (ψalg k) d (fun n a => ⟨mem_pow_of_ψ k, ψ_mem_pow k⟩)
    (fun b => ?_)).symm
  obtain ⟨x, hx⟩ := truncMap_surjective k (d + 1) (Ideal.Quotient.mk _ b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, ?_⟩
  rw [truncMap_mk, Ideal.Quotient.eq] at hx
  rw [← neg_mem_iff, neg_sub]
  exact hx

/-- **`H(2) = 30978` for `Â`** (any field with `2 ≠ 0`). -/
theorem hilbertValue_two_Ahat (h2 : (2 : k) ≠ 0) : hilbertValue k (Ahat k) 2 = 30978 := by
  rw [hilbertValue_Ahat]
  exact HilbertValues.hilbertValue_two k h2


/-- `SquareCompletion` is a `k`-algebra through `k → A → A^`. -/
noncomputable instance : Algebra k (SquareCompletion k) := inferInstanceAs (Algebra k (Acompl k))

theorem fromCompletion_algebraMap (a : Aalg k) :
    fromCompletion k (algebraMap (Aalg k) (Acompl k) a) = ψ k a := by
  have h : (fun a => fromCompletion k (algebraMap (Aalg k) (Acompl k) a)) = ψ k := by
    refine IsHausdorff.funext' (maximalIdeal (Ahat k)) fun n a => ?_
    rw [mk_fromCompletion, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, truncMap_mk]
  exact congrFun h a

theorem sqEquiv_algebraMap (r : k) :
    sqEquiv k (algebraMap k (SquareCompletion k) r) = algebraMap k (Ahat k) r := by
  change fromCompletion k (algebraMap k (Acompl k) r) = _
  rw [IsScalarTower.algebraMap_apply k (Aalg k) (Acompl k), fromCompletion_algebraMap,
    ψ_algebraMap]

/-- `SquareCompletion ≃ₐ[k] Â`. -/
noncomputable def sqAlgEquiv : SquareCompletion k ≃ₐ[k] Ahat k :=
  AlgEquiv.ofRingEquiv (f := sqEquiv k) (sqEquiv_algebraMap k)

theorem hilbertValue_squareCompletion (d : ℕ) :
    hilbertValue k (SquareCompletion k) d = hilbertValue k (Aalg k) d := by
  rw [hilbertValue_eq_of_bijective (sqAlgEquiv k).toAlgHom (sqAlgEquiv k).bijective,
    hilbertValue_Ahat]

/-- **`H(2) = 30978` for `SquareCompletion`** (any field with `2 ≠ 0`). -/
theorem hilbertValue_two_squareCompletion (h2 : (2 : k) ≠ 0) :
    hilbertValue k (SquareCompletion k) 2 = 30978 := by
  rw [hilbertValue_squareCompletion]
  exact HilbertValues.hilbertValue_two k h2

/-! ### The coordinates of F5 on `Â` -/

theorem Φ_C (r : k) : Φ k (C r) = C r := by
  change substAlgHom (hasSubst_H k) (C r) = C r
  rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, ← MvPowerSeries.c_eq_algebraMap]

theorem constantCoeff_Φ (f : MvPowerSeries Var k) : constantCoeff (Φ k f) = constantCoeff f := by
  have h0 : constantCoeff (Φ k (f - C (constantCoeff f))) = 0 := by
    rw [Φ_apply]
    exact constantCoeff_subst_eq_zero (hasSubst_H k) (constantCoeff_H k) (by simp)
  rw [map_sub, Φ_C, map_sub, constantCoeff_C, sub_eq_zero] at h0
  exact h0

theorem mem_mX_iff {σ : Type*} [Fintype σ] (f : MvPowerSeries σ k) :
    f ∈ mX σ k ↔ constantCoeff f = 0 := by
  rw [← pow_one (mX σ k), mem_pow_iff_lowZero]
  constructor
  · intro h
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact h 0 (by simp)
  · exact lowZero_one_of_constantCoeff

theorem map_Φ_mX : (mX Var k).map (Φ k) = mX (W k) k := by
  ext g
  rw [← Ideal.comap_symm, Ideal.mem_comap, mem_mX_iff, mem_mX_iff, ← constantCoeff_Φ,
    RingEquiv.apply_symm_apply]

theorem map_Φsymm_mX : (mX (W k) k).map (Φ k).symm = mX Var k := by
  ext f
  rw [Ideal.map_symm, Ideal.mem_comap, mem_mX_iff, mem_mX_iff, constantCoeff_Φ]

/-- The F5 coordinate `w` as an element of `Â`. -/
noncomputable def u (w : W k) : Ahat k := mkA k ((Φ k).symm (X w))

theorem maximalIdeal_Ahat_eq_span_u : maximalIdeal (Ahat k) = Ideal.span (Set.range (u k)) := by
  rw [maximalIdeal_Ahat_eq_map, ← map_Φsymm_mX, mX, Ideal.map_span, Ideal.map_span,
    Set.image_image, ← Set.range_comp]
  rfl

theorem branchMap_u (left : Bool) (w : W k) : branchMap k left (u k w) = kill k left (X w) := by
  rw [u, branchMap_mk, RingEquiv.apply_symm_apply]

theorem keep_inl (left : Bool) (i : Fin 251) :
    Keep k left (Sum.inl i) ↔ TangentData.InChart i left := Iff.rfl

/-! ### The reduced union of the two branches -/

/-- The ideal `𝔭_L ⊓ 𝔭_R`. -/
noncomputable abbrev unionIdeal : Ideal (Ahat k) := branchPrime k true ⊓ branchPrime k false

/-- The reduced union of the two branches, `Â ⧸ (𝔭_L ⊓ 𝔭_R)`. -/
abbrev TwoBranch := Ahat k ⧸ unionIdeal k

/-- The quotient map. -/
noncomputable abbrev mkT : Ahat k →+* TwoBranch k := Ideal.Quotient.mk (unionIdeal k)

theorem unionIdeal_ne_top : unionIdeal k ≠ ⊤ := fun h =>
  (branchPrime_isPrime k true).ne_top (top_le_iff.mp (h ▸ inf_le_left))

instance : Nontrivial (TwoBranch k) := Ideal.Quotient.nontrivial_iff.mpr (unionIdeal_ne_top k)

instance : IsLocalRing (TwoBranch k) :=
  IsLocalRing.of_surjective' (mkT k) Ideal.Quotient.mk_surjective

theorem mem_unionIdeal {a : Ahat k} :
    a ∈ unionIdeal k ↔ branchMap k true a = 0 ∧ branchMap k false a = 0 := Iff.rfl

/-- The coordinates `c, x, y` on the two-branch ring. -/
noncomputable def z (i : Fin 251) : TwoBranch k := mkT k (u k (Sum.inl i))

theorem mkT_u_inr (j : NIdx k) : mkT k (u k (Sum.inr j)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_unionIdeal, branchMap_u, branchMap_u,
    kill_X_drop k true (w := Sum.inr j) (fun h => h), kill_X_drop k false (w := Sum.inr j) (fun h => h)]
  exact ⟨rfl, rfl⟩

/-- The mixed pairs `(x_i, y_j)` and `(y_i, x_j)`. -/
def Mixed (i j : Fin 251) : Prop :=
  (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) ∨ (143 ≤ j.val ∧ j.val < 197 ∧ 197 ≤ i.val)

instance (i j : Fin 251) : Decidable (Mixed i j) := by unfold Mixed; infer_instance

theorem mixed_comm {i j : Fin 251} : Mixed i j ↔ Mixed j i := by unfold Mixed; tauto

/-- **`x_i y_j = 0` on the reduced union.** -/
theorem z_mul_z_of_mixed {i j : Fin 251} (h : Mixed i j) : z k i * z k j = 0 := by
  rw [z, z, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_unionIdeal, map_mul, map_mul,
    branchMap_u, branchMap_u, branchMap_u, branchMap_u]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [kill_X_drop k true (w := Sum.inl j) (by simp only [keep_inl, TangentData.InChart, ↓reduceIte]; omega),
      kill_X_drop k false (w := Sum.inl i)
        (by simp only [keep_inl, TangentData.InChart, Bool.false_eq_true, ↓reduceIte]; omega)]
    simp
  · rw [kill_X_drop k true (w := Sum.inl i) (by simp only [keep_inl, TangentData.InChart, ↓reduceIte]; omega),
      kill_X_drop k false (w := Sum.inl j)
        (by simp only [keep_inl, TangentData.InChart, Bool.false_eq_true, ↓reduceIte]; omega)]
    simp

theorem maximalIdeal_twoBranch : maximalIdeal (TwoBranch k) = Ideal.span (Set.range (z k)) := by
  have h := map_maximalIdeal_of_surjective (R := Ahat k) (S := TwoBranch k) (mkT k)
    Ideal.Quotient.mk_surjective
  rw [maximalIdeal_Ahat_eq_span_u, Ideal.map_span] at h
  rw [← h]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    cases w with
    | inl i => exact Ideal.subset_span ⟨i, rfl⟩
    | inr j => rw [SetLike.mem_coe, mkT_u_inr]; exact Ideal.zero_mem _
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨u k (Sum.inl i), ⟨_, rfl⟩, rfl⟩

theorem z_mem (i : Fin 251) : z k i ∈ maximalIdeal (TwoBranch k) := by
  rw [maximalIdeal_twoBranch]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The residue map of the two-branch ring. -/
noncomputable def evT : TwoBranch k →ₐ[k] k :=
  { Ideal.Quotient.lift (unionIdeal k) (constantCoeff.comp (branchMap k true))
      (fun a ha => by
        rw [RingHom.comp_apply, (mem_unionIdeal k).mp ha |>.1, map_zero]) with
    commutes' := fun r => by
      change constantCoeff (branchMap k true (mkA k (algebraMap k _ r))) = r
      rw [branchMap_mk, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Φ_C, constantCoeff_kill, constantCoeff_C] }

/-! #### Upper bound -/

/-- Ordered non-mixed pairs: the degree-two monomials surviving on the reduced union. -/
abbrev QIdx := {p : Fin 251 × Fin 251 // p.1 ≤ p.2 ∧ ¬ Mixed p.1 p.2}

/-- `binom(252, 2) − 54 · 54 = 28710`. -/
theorem card_QIdx : Fintype.card QIdx = 28710 := by
  rw [Fintype.card_subtype]
  decide +kernel

theorem gradedPiece_two_twoBranch_le :
    gradedPiece k (TwoBranch k) 2 ≤ Submodule.span k
      (Set.range fun q : QIdx => proj k (TwoBranch k) 2 (z k q.1.1 * z k q.1.2)) := by
  refine (gradedPiece_two_le_span (evT k) (z k) (z_mem k)
    (by rw [maximalIdeal_twoBranch]; exact le_sup_left)).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  by_cases hm : Mixed i j
  · change proj k (TwoBranch k) 2 (z k i * z k j) ∈ _
    rw [z_mul_z_of_mixed k hm, map_zero]
    exact Submodule.zero_mem _
  · rcases le_total i j with h | h
    · exact Submodule.subset_span ⟨⟨(i, j), h, hm⟩, rfl⟩
    · refine Submodule.subset_span ⟨⟨(j, i), h, fun h' => hm (mixed_comm.mp h')⟩, ?_⟩
      change proj k (TwoBranch k) 2 (z k j * z k i) = proj k (TwoBranch k) 2 (z k i * z k j)
      exact congrArg _ (mul_comm (z k j) (z k i))

theorem hilbertValue_two_twoBranch_le :
    FiniteDimensional k (gradedPiece k (TwoBranch k) 2) ∧
      hilbertValue k (TwoBranch k) 2 ≤ 28710 := by
  rw [← card_QIdx]
  exact hilbertValue_le_of_le_span' _ (gradedPiece_two_twoBranch_le k)

/-! #### Lower bound -/

/-- The monomial `w_i w_j` of a pair. -/
noncomputable def mon (q : QIdx) : W k →₀ ℕ :=
  Finsupp.single (Sum.inl q.1.1) 1 + Finsupp.single (Sum.inl q.1.2) 1

theorem degree_mon (q : QIdx) : (mon k q).degree = 2 := by
  rw [mon, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem pair_apply_ne_zero (a b x : Fin 251) :
    (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1 : W k →₀ ℕ) (Sum.inl x) ≠ 0 ↔
      x = a ∨ x = b := by
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h1 : a = x <;> by_cases h2 : b = x <;> simp [h1, h2, eq_comm]

theorem mon_inj : ∀ {q q' : QIdx}, mon k q' = mon k q → q' = q := by
  rintro ⟨⟨a, b⟩, hab, hm⟩ ⟨⟨c, d⟩, hcd, hm'⟩ h
  simp only [mon] at h
  have mem : ∀ x, (x = c ∨ x = d) → x = a ∨ x = b := fun x hx =>
    (pair_apply_ne_zero k a b x).mp (h ▸ (pair_apply_ne_zero k c d x).mpr hx)
  have mem' : ∀ x, (x = a ∨ x = b) → x = c ∨ x = d := fun x hx =>
    (pair_apply_ne_zero k c d x).mp (h.symm ▸ (pair_apply_ne_zero k a b x).mpr hx)
  have hc := mem c (Or.inl rfl)
  have hd := mem d (Or.inr rfl)
  have ha := mem' a (Or.inl rfl)
  have hb := mem' b (Or.inr rfl)
  simp only [Fin.ext_iff] at hc hd ha hb
  dsimp only at hab hcd
  rw [Fin.le_def] at hab hcd
  apply Subtype.ext
  show (c, d) = (a, b)
  exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))

/-- The coefficients of the surviving monomials, in the F5 coordinates. -/
noncomputable def Λ1 : MvPowerSeries Var k →ₗ[k] (QIdx → k) where
  toFun f q := coeff (mon k q) (Φ k f)
  map_add' f g := by
    funext q
    simp only [map_add, Pi.add_apply]
  map_smul' r f := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, Φ_C, coeff_C_mul]

/-- `k⟦z⟧ → Â → Â ⧸ (𝔭_L ⊓ 𝔭_R)`. -/
noncomputable def qT : MvPowerSeries Var k →ₐ[k] TwoBranch k :=
  (Ideal.Quotient.mkₐ k (unionIdeal k)).comp (Ideal.Quotient.mkₐ k (brentPS k))

theorem qT_apply (f : MvPowerSeries Var k) : qT k f = mkT k (mkA k f) := rfl

theorem qT_surjective : Function.Surjective (qT k) := by
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨f, rfl⟩

/-- A non-mixed monomial lies on one of the two branches, so its coefficient vanishes on
`𝔭_L ⊓ 𝔭_R`. -/
theorem coeff_mon_eq_zero {f : MvPowerSeries Var k} (hf : mkA k f ∈ unionIdeal k) (q : QIdx) :
    coeff (mon k q) (Φ k f) = 0 := by
  obtain ⟨⟨i, j⟩, hij, hm⟩ := q
  have key : ∀ left : Bool, TangentData.InChart i left → TangentData.InChart j left →
      coeff (mon k ⟨(i, j), hij, hm⟩) (Φ k f) = 0 := by
    intro left hi hj
    have hemb : Finsupp.embDomain (emb k left)
        (Finsupp.single ⟨Sum.inl i, hi⟩ 1 + Finsupp.single ⟨Sum.inl j, hj⟩ 1) =
        mon k ⟨(i, j), hij, hm⟩ := by
      rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]
      rfl
    have h0 : kill k left (Φ k f) = 0 := by
      rw [← branchMap_mk]
      cases left
      · exact ((mem_unionIdeal k).mp hf).2
      · exact ((mem_unionIdeal k).mp hf).1
    rw [← hemb, ← coeff_killCompl, ← kill, h0, map_zero]
  simp only [Mixed, Fin.le_def] at hm hij
  by_cases hj : j.val < 197
  · exact key true (by simp only [TangentData.InChart, ↓reduceIte]; omega)
      (by simp only [TangentData.InChart, ↓reduceIte]; omega)
  · exact key false (by simp only [TangentData.InChart, Bool.false_eq_true, ↓reduceIte]; omega)
      (by simp only [TangentData.InChart, Bool.false_eq_true, ↓reduceIte]; omega)

theorem ker_qT_le : LinearMap.ker (qT k).toLinearMap ≤ LinearMap.ker (Λ1 k) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  have hf' : mkA k f ∈ unionIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hf
  funext q
  exact coeff_mon_eq_zero k hf' q

/-- The coefficient functional on the two-branch ring. -/
noncomputable def ΛT : TwoBranch k →ₗ[k] (QIdx → k) :=
  ((LinearMap.ker (qT k).toLinearMap).liftQ (Λ1 k) (ker_qT_le k)).comp
    ((qT k).toLinearMap.quotKerEquivOfSurjective (qT_surjective k)).symm.toLinearMap

theorem ΛT_qT (f : MvPowerSeries Var k) : ΛT k (qT k f) = Λ1 k f := by
  have : ((qT k).toLinearMap.quotKerEquivOfSurjective (qT_surjective k)).symm (qT k f) =
      Submodule.Quotient.mk f := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [ΛT, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    Submodule.liftQ_apply]

theorem maximalIdeal_twoBranch_eq_map :
    maximalIdeal (TwoBranch k) = (mX Var k).map (qT k).toRingHom := by
  have h := map_maximalIdeal_of_surjective (R := Ahat k) (S := TwoBranch k) (mkT k)
    Ideal.Quotient.mk_surjective
  rw [← h, maximalIdeal_Ahat_eq_map, Ideal.map_map]
  rfl

theorem ΛT_cube (a : TwoBranch k) (ha : a ∈ maximalIdeal (TwoBranch k) ^ (2 + 1)) :
    ΛT k a = 0 := by
  have hpow : (mX Var k ^ (2 + 1)).map (qT k).toRingHom = maximalIdeal (TwoBranch k) ^ (2 + 1) := by
    rw [maximalIdeal_twoBranch_eq_map]
    exact Ideal.map_pow (qT k).toRingHom (mX Var k) (2 + 1)
  rw [← hpow, Ideal.mem_map_iff_of_surjective (qT k).toRingHom (qT_surjective k)] at ha
  obtain ⟨f, hf, rfl⟩ := ha
  change ΛT k (qT k f) = 0
  rw [ΛT_qT]
  funext q
  have hΦ : Φ k f ∈ mX (W k) k ^ (2 + 1) := by
    rw [← map_Φ_mX, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf
  exact lowZero_of_mem_pow _ hΦ _ (by rw [degree_mon]; norm_num)

theorem X_mul_X_eq (a b : W k) :
    (X a * X b : MvPowerSeries (W k) k) = monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
  rw [X, X, monomial_mul_monomial, mul_one]

theorem ΛT_z_mul_z (q : QIdx) : ΛT k (z k q.1.1 * z k q.1.2) = Pi.single q 1 := by
  have : z k q.1.1 * z k q.1.2 =
      qT k ((Φ k).symm (X (Sum.inl q.1.1)) * (Φ k).symm (X (Sum.inl q.1.2))) := by
    rw [map_mul]
    rfl
  rw [this, ΛT_qT]
  funext q'
  change coeff (mon k q') (Φ k _) = _
  have hq : (Finsupp.single (Sum.inl q.1.1) 1 + Finsupp.single (Sum.inl q.1.2) 1 : W k →₀ ℕ) =
      mon k q := rfl
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, X_mul_X_eq, hq,
    coeff_monomial]
  by_cases h : q' = q
  · subst h
    rw [if_pos rfl, Pi.single_eq_same]
  · rw [if_neg (fun h' => h (mon_inj k h')), Pi.single_eq_of_ne h]

/-- **The reduced union of the two branches has `H(2) = 28710`.** -/
theorem hilbertValue_two_twoBranch : hilbertValue k (TwoBranch k) 2 = 28710 := by
  obtain ⟨hfin, hle⟩ := hilbertValue_two_twoBranch_le k
  haveI := hfin
  refine le_antisymm hle ?_
  rw [← card_QIdx]
  refine le_hilbertValue' (ΛT k) (ΛT_cube k) (fun q : QIdx => z k q.1.1 * z k q.1.2)
    (fun q => by rw [pow_two]; exact Ideal.mul_mem_mul (z_mem k _) (z_mem k _)) ?_
  simp only [ΛT_z_mul_z]
  have e : (fun q : QIdx => (Pi.single q (1 : k) : QIdx → k)) = ⇑(Pi.basisFun k QIdx) :=
    funext fun q => (Pi.basisFun_apply k QIdx q).symm
  rw [e]
  exact (Pi.basisFun k QIdx).span_eq

/-! ### The comparison -/

/-- **`𝔭_L ⊓ 𝔭_R ≠ 0` in `Â`.** Otherwise `Â` would be the reduced union of the branches, but
`H(2)` is `30978` for `Â` and `28710` for the reduced union. -/
theorem unionIdeal_ne_bot (h2 : (2 : k) ≠ 0) : unionIdeal k ≠ ⊥ := by
  intro h
  have hbij : Function.Bijective (Ideal.Quotient.mkₐ k (unionIdeal k)) := by
    refine ⟨fun a b hab => ?_, Ideal.Quotient.mk_surjective⟩
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, h, Ideal.mem_bot, sub_eq_zero] at hab
    exact hab
  have := hilbertValue_eq_of_bijective (R := Ahat k) (S := TwoBranch k)
    (Ideal.Quotient.mkₐ k (unionIdeal k)) hbij 2
  rw [hilbertValue_two_Ahat k h2, hilbertValue_two_twoBranch] at this
  norm_num at this

/-- **`𝔭_L ⊓ 𝔭_R ≠ 0` in `SquareCompletion`** (any field with `2 ≠ 0`). -/
theorem sqBranchPrime_inf_ne_bot (h2 : (2 : k) ≠ 0) :
    sqBranchPrime k true ⊓ sqBranchPrime k false ≠ ⊥ := by
  rw [sqBranchPrime_eq_comap, sqBranchPrime_eq_comap, ← Ideal.comap_inf]
  intro h
  apply unionIdeal_ne_bot k h2
  rw [← Ideal.map_comap_of_surjective (sqEquiv k).toRingHom (sqEquiv k).surjective (unionIdeal k)]
  exact (congrArg (Ideal.map (sqEquiv k).toRingHom) h).trans Ideal.map_bot

/-- **`SquareCompletion` is nonreduced or has a third minimal prime** (any field with `2 ≠ 0`). -/
theorem not_isReduced_or_extra_minimalPrime (h2 : (2 : k) ≠ 0) :
    ¬ IsReduced (SquareCompletion k) ∨
      ∃ q ∈ minimalPrimes (SquareCompletion k),
        q ≠ sqBranchPrime k true ∧ q ≠ sqBranchPrime k false := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hred, hmin⟩ := hcon
  apply sqBranchPrime_inf_ne_bot k h2
  rw [eq_bot_iff]
  intro a ha
  have hnil : a ∈ nilradical (SquareCompletion k) := by
    rw [nilradical, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro q hq
    by_cases hL : q = sqBranchPrime k true
    · exact hL ▸ ha.1
    · exact hmin q hq hL ▸ ha.2
  exact (mem_nilradical.mp hnil).eq_zero

/-- **Characteristic three.** -/
theorem not_isReduced_or_extra_minimalPrime_charThree [CharP k 3] :
    ¬ IsReduced (SquareCompletion k) ∨
      ∃ q ∈ minimalPrimes (SquareCompletion k),
        q ≠ sqBranchPrime k true ∧ q ≠ sqBranchPrime k false :=
  not_isReduced_or_extra_minimalPrime k (HilbertValues.two_ne_zero_of_charP_three k)

/-- **Characteristic zero.** -/
theorem not_isReduced_or_extra_minimalPrime_charZero [CharZero k] :
    ¬ IsReduced (SquareCompletion k) ∨
      ∃ q ∈ minimalPrimes (SquareCompletion k),
        q ≠ sqBranchPrime k true ∧ q ≠ sqBranchPrime k false :=
  not_isReduced_or_extra_minimalPrime k two_ne_zero

end Brent.Formal
