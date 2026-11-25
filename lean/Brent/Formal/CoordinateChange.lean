import Brent.Formal.PowerSeriesFamily
import Brent.Formal.FormalInverse
import Brent.Formal.MonomialIdeal
import Brent.KernelCheck.CharThreeData
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# The formal coordinate change

`Â = k⟦z⟧ ⧸ (Brent equations centered at the recursive point)`. Extend the 251 certified frame
vectors by vectors `N` to a basis `B` of `k^2352`. In the variables `(t, n)`, `t` indexed by the
frame and `n` by `N`,

  `H(t, n) = L(c, x) + R(c, y) − R(c, 0) + Σₙ B(n) n − p`

has zero constant term and linear part `B`. Here `c` are the 143 orbit directions, `x` the 54
left-only and `y` the 54 right-only directions. So substitution along `H` is an automorphism of
`k⟦2352⟧` (formal inverse function theorem), and it sends every centered Brent equation into
`(y, n) ∩ (x, n)`.
-/

open scoped BigOperators

namespace Module.Basis

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {v : ι → V}

theorem sumExtend_apply (hs : LinearIndependent K v) (j : ι ⊕ sumExtendIndex hs) :
    sumExtend hs j = Sum.elim v Subtype.val j := by
  classical
  cases j with
  | inl i =>
    simp [sumExtend, Equiv.Set.sumDiffSubset, Equiv.Set.union]
    rfl
  | inr n =>
    simp [sumExtend, Equiv.Set.sumDiffSubset, Equiv.Set.union]
    rfl

end Module.Basis

namespace Brent.Formal

open MvPowerSeries TangentData Finsupp

set_option linter.unusedSectionVars false

/-- The 2352 Brent variables. -/
abbrev Var := Variable SquareVertex SquareSummand

section Equations

variable (k : Type) [Field k]

/-- The recursive point. -/
noncomputable def pt (x : Var) : k := (strassenSquare k).coordinates x

/-- The Brent equation centered at the recursive point, as a power series. -/
noncomputable def eqPS (abc : EquationIndex SquareVertex) : MvPowerSeries Var k :=
  MvPolynomial.eval₂Hom C (fun x => C (pt k x) + X x)
    (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2)

/-- The centered Brent ideal of `k⟦z⟧`. -/
noncomputable def brentPS : Ideal (MvPowerSeries Var k) := Ideal.span (Set.range (eqPS k))

/-- The formal local ring of the Brent variety at the recursive point. -/
abbrev Ahat := MvPowerSeries Var k ⧸ brentPS k

variable {k}

/-- A solution over `k⟦σ⟧` kills every Brent equation. -/
theorem eval_equation_solves {σ : Type} (d : Decomposition (MvPowerSeries σ k) SquareVertex SquareSummand)
    (hd : d.Solves) (abc : EquationIndex SquareVertex) :
    MvPolynomial.eval₂Hom C d.coordinates (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2)
      = 0 := by
  have hs := hd abc.1 abc.2.1 abc.2.2
  simp only [equation, map_sub, map_sum, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
  rw [sub_eq_zero]
  simp only [Decomposition.entry] at hs
  convert hs using 1
  simp [matrixMultiplicationEntry, apply_ite (C (σ := σ) (R := k))]

/-- Algebra maps fix constants. -/
theorem algHom_C {σ τ : Type} (φ : MvPowerSeries σ k →ₐ[k] MvPowerSeries τ k) (r : k) :
    φ (C r) = C r := by
  have h := φ.commutes r
  rw [algebraMap_apply, algebraMap_apply] at h
  simpa using h

/-- Applying an algebra map to an evaluated polynomial. -/
theorem algHom_eval₂ {σ τ : Type} (φ : MvPowerSeries σ k →ₐ[k] MvPowerSeries τ k)
    (g : Var → MvPowerSeries σ k) (p : MvPolynomial Var k) :
    φ (MvPolynomial.eval₂Hom C g p) = MvPolynomial.eval₂Hom C (fun x => φ (g x)) p := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, algHom_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

/-- Substituting into a centered equation. -/
theorem subst_eqPS {τ : Type} {a : Var → MvPowerSeries τ k} (ha : HasSubst a)
    (abc : EquationIndex SquareVertex) :
    subst a (eqPS k abc) = MvPolynomial.eval₂Hom C (fun x => C (pt k x) + a x)
      (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2) := by
  rw [← substAlgHom_apply ha, eqPS, algHom_eval₂]
  simp only [map_add, algHom_C, substAlgHom_X]

/-- A centered solution kills every equation. -/
theorem centered_zero {σ : Type} (d : Decomposition (MvPowerSeries σ k) SquareVertex SquareSummand)
    (hd : d.Solves) (g : Var → MvPowerSeries σ k) (hg : ∀ x, g x = d.coordinates x - C (pt k x))
    (abc : EquationIndex SquareVertex) :
    MvPolynomial.eval₂Hom C (fun x => C (pt k x) + g x)
      (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2) = 0 := by
  have : (fun x => C (pt k x) + g x) = d.coordinates := by
    funext x; rw [hg]; ring
  rw [this]
  exact eval_equation_solves d hd abc

end Equations

/-! ### The extended frame -/

section Frame

variable (k : Type) [Field k]

/-- The normal directions: a complement of the frame. -/
abbrev NIdx := Module.Basis.sumExtendIndex (CharThree.frame_independent k)

/-- The frame extended to a basis. -/
noncomputable def B : Module.Basis (Fin 251 ⊕ NIdx k) k (Var → k) :=
  Module.Basis.sumExtend (CharThree.frame_independent k)

noncomputable instance : Fintype (Fin 251 ⊕ NIdx k) := FiniteDimensional.fintypeBasisIndex (B k)

noncomputable instance : Fintype (NIdx k) :=
  have : Finite (NIdx k) :=
    Finite.of_injective (Sum.inr : NIdx k → Fin 251 ⊕ NIdx k) Sum.inr_injective
  Fintype.ofFinite _

noncomputable instance : DecidableEq (NIdx k) := Classical.decEq _

theorem B_inl (j : Fin 251) : B k (Sum.inl j) = (frameDirection k j).coordinates := by
  rw [B, Module.Basis.sumExtend_apply]; rfl

/-- The coordinate variables `(t, n)`. -/
abbrev W := Fin 251 ⊕ NIdx k

theorem card_W : Fintype.card (W k) = Fintype.card Var := by
  rw [← Module.finrank_eq_card_basis (B k), Module.finrank_fintype_fun_eq_card]

end Frame

/-! ### The coordinate change -/

section Change

variable (k : Type) [Field k]

/-- The left family `L(c, x)`. -/
noncomputable def famL := selFamily k (NIdx k) (fun i => InChart i true) true

/-- The right family `R(c, y)`. -/
noncomputable def famR := selFamily k (NIdx k) (fun i => InChart i false) false

/-- The orbit family `R(c, 0)`. -/
noncomputable def famO := selFamily k (NIdx k) (fun i => i.val < 143) false

/-- **The coordinate change** `H = L(c,x) + R(c,y) − R(c,0) + Σ B(n) n − p`. -/
noncomputable def H (x : Var) : MvPowerSeries (W k) k :=
  (famL k).coordinates x + (famR k).coordinates x - (famO k).coordinates x +
    (∑ n : NIdx k, C (B k (Sum.inr n) x) * X (Sum.inr n)) - C (pt k x)

theorem constantCoeff_H (x : Var) : constantCoeff (H k x) = 0 := by
  simp only [H, famL, famR, famO, selFamily, map_add, map_sub, map_sum, map_mul,
    constantCoeff_value, constantCoeff_C, constantCoeff_X, mul_zero, Finset.sum_const_zero, pt]
  ring

theorem coeff_sum_normal (w : W k) (x : Var) :
    coeff (single w 1) (∑ n : NIdx k, C (B k (Sum.inr n) x) * X (Sum.inr n) :
      MvPowerSeries (W k) k) = Sum.elim (fun _ => 0) (fun n => B k (Sum.inr n) x) w := by
  rw [map_sum]
  simp only [coeff_C_mul, coeff_X]
  cases w with
  | inl j =>
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [if_neg, mul_zero]
    intro h
    exact Sum.inl_ne_inr (Finsupp.single_left_injective one_ne_zero h)
  | inr n =>
    rw [Finset.sum_eq_single n]
    · simp
    · intro m _ hm
      rw [if_neg, mul_zero]
      intro h
      exact hm (Sum.inr_injective (Finsupp.single_left_injective one_ne_zero h)).symm
    · simp

theorem coeff_C_pt (w : W k) (x : Var) :
    coeff (single w 1) (C (pt k x) : MvPowerSeries (W k) k) = 0 := by
  rw [coeff_C, if_neg]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

/-- **The linear part of `H` is the basis `B`.** -/
theorem coeff_H (w : W k) (x : Var) : coeff (single w 1) (H k x) = B k w x := by
  simp only [H, map_add, map_sub, coeff_sum_normal, coeff_C_pt, sub_zero]
  cases w with
  | inr n =>
    have hw : ∀ (P : Fin 251 → Prop), ∀ j, Sum.inl j = (Sum.inr n : W k) → ¬ P j :=
      fun _ j h => absurd h Sum.inl_ne_inr
    simp only [famL, famR, famO, coeff_sel_other _ _ _ (hw _), Sum.elim_inr]
    ring
  | inl j =>
    simp only [Sum.elim_inl, add_zero, B_inl]
    by_cases h1 : j.val < 143
    · rw [famL, famR, famO,
        coeff_sel_in (fun i => InChart i true) true j (by simp [InChart]; omega) (by simp [InChart]; omega),
        coeff_sel_in (fun i => InChart i false) false j (by simp [InChart]; omega)
          (by simp [InChart]; omega),
        coeff_sel_in (fun i : Fin 251 => i.val < 143) false j h1 (by simp [InChart]; omega)]
      ring
    · by_cases h2 : j.val < 197
      · rw [famL, famR, famO,
          coeff_sel_in (fun i => InChart i true) true j (by simp [InChart]; omega)
            (by simp [InChart]; omega),
          coeff_sel_other (fun i => InChart i false) false _
            (fun i h => by cases h; simp [InChart]; omega),
          coeff_sel_other (fun i : Fin 251 => i.val < 143) false _
            (fun i h => by cases h; simp; omega)]
        ring
      · rw [famL, famR, famO,
          coeff_sel_other (fun i => InChart i true) true _
            (fun i h => by cases h; simp [InChart]; omega),
          coeff_sel_in (fun i => InChart i false) false j (by simp [InChart]; omega)
            (by simp [InChart]; omega),
          coeff_sel_other (fun i : Fin 251 => i.val < 143) false _
            (fun i h => by cases h; simp; omega)]
        ring

/-- An identification of the coordinate variables with the Brent variables. -/
noncomputable def eW : W k ≃ Var := Fintype.equivOfCardEq (card_W k)

theorem hasSubst_H : HasSubst (H k) := hasSubst_of_constantCoeff_zero (constantCoeff_H k)

/-- **The coordinate change is invertible.** -/
theorem H_bijective : Function.Bijective (subst (R := k) (H k)) := by
  classical
  apply subst_bijective_equiv (eW k) (constantCoeff_H k)
  have hM : (Matrix.of fun x v => coeff (single ((eW k).symm v) 1) (H k x)) =
      (Pi.basisFun k Var).toMatrix ((B k).reindex (eW k)) := by
    ext x v
    rw [Matrix.of_apply, coeff_H, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
      Module.Basis.reindex_apply]
  rw [hM]
  letI := Module.Basis.invertibleToMatrix (Pi.basisFun k Var) ((B k).reindex (eW k))
  exact isUnit_of_invertible _

/-- **The formal coordinate change** as an automorphism of `k⟦z⟧`. -/
noncomputable def Φ : MvPowerSeries Var k ≃+* MvPowerSeries (W k) k :=
  RingEquiv.ofBijective (substAlgHom (hasSubst_H k)).toRingHom (by
    change Function.Bijective (substAlgHom (hasSubst_H k))
    rw [coe_substAlgHom]
    exact H_bijective k)

theorem Φ_apply (f : MvPowerSeries Var k) : Φ k f = subst (H k) f := by
  change substAlgHom (hasSubst_H k) f = _
  rw [substAlgHom_apply]

end Change

/-! ### The branches -/

section Branches

variable (k : Type) [Field k]

/-- The variables kept on a branch: the chart's frame directions (`c, x` on the left,
`c, y` on the right). -/
def Keep (left : Bool) : W k → Prop := Sum.elim (fun i => InChart i left) (fun _ => False)

instance (left : Bool) : DecidablePred (Keep k left) := fun w => by
  cases w <;> (simp only [Keep, Sum.elim_inl, Sum.elim_inr]; infer_instance)

/-- The branch coordinates. -/
abbrev BranchVar (left : Bool) := {w : W k // Keep k left w}

/-- The inclusion of branch coordinates. -/
def emb (left : Bool) : BranchVar k left ↪ W k := Function.Embedding.subtype _

theorem range_emb (left : Bool) : Set.range (emb k left) = {w | Keep k left w} := by
  ext w
  simp [emb]

/-- Restriction to a branch: set the other variables to zero. -/
noncomputable def kill (left : Bool) :
    MvPowerSeries (W k) k →ₐ[k] MvPowerSeries (BranchVar k left) k :=
  killCompl (emb k left)

theorem constantCoeff_kill (left : Bool) (f : MvPowerSeries (W k) k) :
    constantCoeff (kill k left f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, kill,
    coeff_killCompl, Finsupp.embDomain_zero]

theorem kill_X_drop (left : Bool) {w : W k} (hw : ¬ Keep k left w) :
    kill k left (X w) = 0 := by
  apply killCompl_X_eq_zero
  rw [range_emb]
  exact hw

theorem kill_C (left : Bool) (r : k) : kill k left (C r) = C r := killCompl_C r

/-- Restriction as a ring map. -/
noncomputable abbrev killR (left : Bool) :
    MvPowerSeries (W k) k →+* MvPowerSeries (BranchVar k left) k :=
  (kill k left).toRingHom

theorem kill_zero_const (left : Bool) (f : MvPowerSeries (W k) k) (hf : constantCoeff f = 0) :
    constantCoeff (killR k left f) = 0 := by
  change constantCoeff (kill k left f) = 0
  rw [constantCoeff_kill, hf]

/-- Restricted selections agree when they differ only on dropped directions. -/
theorem selAssign_kill (left : Bool) (P Q : Fin 251 → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ i, (P i ↔ Q i) ∨ ¬ InChart i left) :
    (selAssign k (NIdx k) P).map (killR k left) (kill_zero_const k left) =
      (selAssign k (NIdx k) Q).map (killR k left) (kill_zero_const k left) := by
  apply Subtype.ext
  funext i
  change (kill k left) (selVar k (NIdx k) P i) = (kill k left) (selVar k (NIdx k) Q i)
  rcases h i with hi | hi
  · simp only [selVar, hi]
  · have hX : kill k left (X (Sum.inl i)) = 0 := kill_X_drop k left (by simpa [Keep] using hi)
    unfold selVar
    split_ifs <;> simp [hX]

/-- Restricting a family is the family of the restricted assignment. -/
theorem kill_coordinates (left side : Bool) (P : Fin 251 → Prop) [DecidablePred P] (x : Var) :
    kill k left ((selFamily k (NIdx k) P side).coordinates x) =
      ((paramsOf k ((selAssign k (NIdx k) P).map (killR k left)
        (kill_zero_const k left))).value side).coordinates x := by
  change killR k left _ = _
  rw [← LowerBound.coordinates_map, selFamily, FamilyParameters.value_map, paramsOf_map]
  intro r
  exact kill_C k left r

/-- **Left branch.** Restricting `H` to `(c, x)` gives `L − p`. -/
theorem kill_H_left (x : Var) :
    kill k true (H k x) = (kill k true) ((famL k).coordinates x) - C (pt k x) := by
  have hRO : kill k true ((famR k).coordinates x) = kill k true ((famO k).coordinates x) := by
    rw [famR, famO, kill_coordinates, kill_coordinates, selAssign_kill k true
      (fun i => InChart i false) (fun i : Fin 251 => i.val < 143)]
    intro i
    by_cases hi : i.val < 197
    · left; simp [InChart]; omega
    · right; simp [InChart]; omega
  have hN : kill k true (∑ n : NIdx k, C (B k (Sum.inr n) x) * X (Sum.inr n)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [map_mul, kill_X_drop k true (by simp [Keep]), mul_zero]
  simp only [H, map_add, map_sub, hRO, hN, kill_C]
  ring

/-- **Right branch.** Restricting `H` to `(c, y)` gives `R − p`, by the overlap. -/
theorem kill_H_right (x : Var) :
    kill k false (H k x) = (kill k false) ((famR k).coordinates x) - C (pt k x) := by
  have hLO : kill k false ((famL k).coordinates x) = kill k false ((famO k).coordinates x) := by
    rw [famL, famO, kill_coordinates, kill_coordinates, selAssign_kill k false (fun i => InChart i true)
      (fun i : Fin 251 => i.val < 143)]
    · rw [value_orbit_left_eq_right]
      intro i hi
      change (kill k false) (selVar k (NIdx k) (fun i : Fin 251 => i.val < 143) i) = 0
      rw [selVar, if_neg (by omega), map_zero]
    · intro i
      by_cases hi : i.val < 143 ∨ 197 ≤ i.val
      · left; simp [InChart]; omega
      · right; simp [InChart]; omega
  have hN : kill k false (∑ n : NIdx k, C (B k (Sum.inr n) x) * X (Sum.inr n)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [map_mul, kill_X_drop k false (by simp [Keep]), mul_zero]
  simp only [H, map_add, map_sub, hLO, hN, kill_C]
  ring

/-- Every centered Brent equation vanishes on both branches after the coordinate change. -/
theorem kill_subst_eqPS (left : Bool) (abc : EquationIndex SquareVertex) :
    kill k left (subst (H k) (eqPS k abc)) = 0 := by
  rw [subst_eqPS (hasSubst_H k), algHom_eval₂]
  simp only [map_add, kill_C]
  cases left with
  | true =>
    refine centered_zero ((famL k).map (killR k true)) ?_ _ ?_ abc
    · rw [famL, selFamily, FamilyParameters.value_map]
      exact FamilyParameters.value_solves _ _
    · intro x
      rw [kill_H_left, LowerBound.coordinates_map]
      rfl
  | false =>
    refine centered_zero ((famR k).map (killR k false)) ?_ _ ?_ abc
    · rw [famR, selFamily, FamilyParameters.value_map]
      exact FamilyParameters.value_solves _ _
    · intro x
      rw [kill_H_right, LowerBound.coordinates_map]
      rfl

/-- The branch ideal: generated by the dropped variables (`(y, n)` or `(x, n)`). -/
noncomputable def branchIdeal (left : Bool) : Ideal (MvPowerSeries (W k) k) :=
  Ideal.span (X '' (Set.range (emb k left))ᶜ)

theorem ker_kill (left : Bool) :
    RingHom.ker (killR k left) = branchIdeal k left :=
  ker_killCompl (emb k left)

/-- **The Brent ideal in the new coordinates lies in `(y, n) ∩ (x, n)`.** -/
theorem map_brentPS_le :
    Ideal.map (Φ k) (brentPS k) ≤ branchIdeal k true ⊓ branchIdeal k false := by
  rw [brentPS, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨abc, rfl⟩, rfl⟩
  refine ⟨?_, ?_⟩ <;>
  · rw [SetLike.mem_coe, ← ker_kill, RingHom.mem_ker, Φ_apply]
    exact kill_subst_eqPS k _ abc

end Branches

end Brent.Formal
