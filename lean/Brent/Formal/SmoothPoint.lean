import Brent.Formal.SwapSymmetry
import Brent.Formal.MonomialIdeal
import Brent.Formal.PowerSeriesNoetherian
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Formal neighbourhoods of arbitrary solutions

For a solution `q` of the Brent equations, `Â_q = k⟦z⟧ ⧸ (f(q + z))`. The linear part of the
centered equation `f_e(q + z)` is the Jacobian row of `e` at `q`. If `n` columns of the
Jacobian at `q` have a nonsingular `n × n` minor, then the formal inverse function theorem makes
`Â_q` a quotient of a power series ring in the remaining `2352 - n` variables. If moreover
`Â_q` maps onto a power series ring in that many variables, then `Â_q` *is* that power series
ring, since a surjective endomorphism of a Noetherian ring is injective.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries

set_option linter.unusedSectionVars false

variable {k : Type} [Field k]

/-! ### Surjective endomorphisms of Noetherian rings -/

section Noetherian

variable {R : Type*} [CommRing R]

/-- The iterates of a ring endomorphism. -/
def iterHom (f : R →+* R) : ℕ → (R →+* R)
  | 0 => RingHom.id R
  | n + 1 => f.comp (iterHom f n)

theorem iterHom_succ_apply (f : R →+* R) (n : ℕ) (x : R) :
    iterHom f (n + 1) x = iterHom f n (f x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change f (iterHom f (n + 1) x) = f (iterHom f n (f x))
    rw [ih]

theorem iterHom_surjective {f : R →+* R} (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (iterHom f n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact hf.comp ih

/-- **A surjective endomorphism of a Noetherian ring is injective.** -/
theorem injective_of_surjective_endo [IsNoetherianRing R] (f : R →+* R)
    (hf : Function.Surjective f) : Function.Injective f := by
  let K : ℕ →o Ideal R := ⟨fun n => RingHom.ker (iterHom f n), by
    intro m n hmn x hx
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    induction d with
    | zero => exact hx
    | succ d ih =>
      have := ih (by omega)
      change iterHom f (m + d + 1) x = 0
      change f (iterHom f (m + d) x) = 0
      rw [show iterHom f (m + d) x = 0 from this, map_zero]⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr inferInstance K
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := iterHom_surjective hf n x
  have hy : y ∈ K (n + 1) := by
    change iterHom f (n + 1) y = 0
    change f (iterHom f n y) = 0
    exact hx
  rw [← hn (n + 1) (by omega)] at hy
  exact hy

end Noetherian

/-! ### Centered equations at a solution -/

/-- The decomposition with coordinates `g`. -/
def ofCoords {R : Type} (g : Var → R) : Decomposition R SquareVertex SquareSummand :=
  ⟨fun s a => g (s, .u, a), fun s a => g (s, .v, a), fun s a => g (s, .w, a)⟩

theorem eval₂_equation_gen {R : Type} [CommRing R] (f : k →+* R) (g : Var → R)
    (abc : EquationIndex SquareVertex) :
    MvPolynomial.eval₂Hom f g (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2) =
      (ofCoords g).entry abc.1 abc.2.1 abc.2.2 - f (matrixMultiplicationEntry k abc.1 abc.2.1 abc.2.2) := by
  simp [equation, Decomposition.entry, ofCoords]

/-- The Brent equation centered at `q`. -/
noncomputable def eqAt (q : Decomposition k SquareVertex SquareSummand)
    (abc : EquationIndex SquareVertex) : MvPowerSeries Var k :=
  MvPolynomial.eval₂Hom C (fun x => C (q.coordinates x) + X x)
    (equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2)

/-- The centered Brent ideal at `q`. -/
noncomputable def idealAt (q : Decomposition k SquareVertex SquareSummand) :
    Ideal (MvPowerSeries Var k) :=
  Ideal.span (Set.range (eqAt q))

/-- The formal local ring of the Brent scheme at `q`. -/
abbrev AhatAt (q : Decomposition k SquareVertex SquareSummand) := MvPowerSeries Var k ⧸ idealAt q

theorem ofCoords_coordinates {R : Type} (d : Decomposition R SquareVertex SquareSummand) :
    ofCoords d.coordinates = d := by
  cases d; rfl

theorem constantCoeff_eqAt {q : Decomposition k SquareVertex SquareSummand} (hq : q.Solves)
    (abc : EquationIndex SquareVertex) : constantCoeff (eqAt q abc) = 0 := by
  rw [eqAt, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, eval₂_equation_gen]
  have h1 : (fun x => (constantCoeff (σ := Var) (R := k)) (C (q.coordinates x) + X x)) =
      q.coordinates := by
    funext x; simp
  simp only [Function.comp_def, h1, ofCoords_coordinates, RingHom.comp_apply, constantCoeff_C]
  rw [hq]
  exact sub_self _

/-- **The linear part of a centered equation is the Jacobian row.** -/
theorem coeff_eqAt {q : Decomposition k SquareVertex SquareSummand} (hq : q.Solves)
    (v : Var) (abc : EquationIndex SquareVertex) :
    coeff (Finsupp.single v 1) (eqAt q abc) = q.jacobianColumn v abc.1 abc.2.1 abc.2.2 := by
  rw [← jetAt_snd v, eqAt, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, eval₂_equation_gen]
  set d := ofCoords (fun x => (jetAt v) (C (q.coordinates x) + X x)) with hd
  have hc : d.constantPart = q := by
    cases q
    simp only [hd, ofCoords, Decomposition.constantPart, map_add, jetAt_C, jetAt_X]
    congr 1 <;> funext s a <;> split_ifs <;> simp [Decomposition.coordinates]
  have key : ∀ x : Var, ((jetAt v) (C (q.coordinates x) + X x)).snd = if v = x then 1 else 0 := by
    intro x
    rw [map_add, jetAt_C, jetAt_X, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add]
    by_cases h : x = v
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; rfl
  have ht : d.tangentPart = Decomposition.coordinateDirection v := by
    apply Decomposition.eq_of_components <;> funext s a
    · exact key (s, .u, a)
    · exact key (s, .v, a)
    · exact key (s, .w, a)
  rw [TrivSqZeroExt.snd_sub, Decomposition.snd_entry, hc, ht]
  simp [jetAt_C, Decomposition.jacobianColumn]

/-! ### The formal inverse function theorem at `q` -/

section Inverse

attribute [local instance] Classical.propDecidable

variable (q : Decomposition k SquareVertex SquareSummand) (hq : q.Solves) {n : ℕ}
  (col : Fin n → Var) (hcol : Function.Injective col) (eqn : Fin n → EquationIndex SquareVertex)

/-- The variables outside the selected columns. -/
abbrev Free (col : Fin n → Var) := ↥(Set.range col)ᶜ

def freeEmb (col : Fin n → Var) : Free col ↪ Var := Function.Embedding.subtype _

/-- The new coordinates: selected equations, and the free variables. -/
noncomputable def newCoord (x : Var) : MvPowerSeries Var k :=
  if h : x ∈ Set.range col then eqAt q (eqn ((Equiv.ofInjective col hcol).symm ⟨x, h⟩)) else X x

theorem newCoord_col (i : Fin n) : newCoord q col hcol eqn (col i) = eqAt q (eqn i) := by
  rw [newCoord, dif_pos ⟨i, rfl⟩]
  congr 2
  rw [Equiv.symm_apply_eq]
  rfl

theorem newCoord_free (x : Free col) : newCoord q col hcol eqn x = X x.1 := by
  rw [newCoord, dif_neg x.2]

include hq in
theorem constantCoeff_newCoord (x : Var) : constantCoeff (newCoord q col hcol eqn x) = 0 := by
  rw [newCoord]
  split_ifs
  · exact constantCoeff_eqAt hq _
  · exact constantCoeff_X x

/-- The ordering `Fin n ⊕ Free ≃ Var`. -/
noncomputable def splitEquiv' : Fin n ⊕ Free col ≃ Var :=
  (Equiv.sumCongr (Equiv.ofInjective col hcol) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range col))

theorem splitEquiv'_inl (i : Fin n) : splitEquiv' col hcol (Sum.inl i) = col i := by
  simp [splitEquiv']

theorem splitEquiv'_inr (x : Free col) : splitEquiv' col hcol (Sum.inr x) = x.1 := by
  simp [splitEquiv']

/-- The Jacobian minor at `q`. -/
noncomputable def minorAt : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => q.jacobianColumn (col j) (eqn i).1 (eqn i).2.1 (eqn i).2.2

include hq in
theorem isUnit_linear (hdet : (minorAt q col eqn).det ≠ 0) :
    IsUnit (Matrix.of fun x v => coeff (Finsupp.single ((Equiv.refl Var).symm v) 1)
      (newCoord q col hcol eqn x)) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_submatrix_equiv_self (splitEquiv' col hcol)]
  have hblock : (Matrix.of fun x v => coeff (Finsupp.single ((Equiv.refl Var).symm v) 1)
      (newCoord q col hcol eqn x)).submatrix (splitEquiv' col hcol) (splitEquiv' col hcol) =
      Matrix.fromBlocks (minorAt q col eqn)
        (Matrix.of fun i (y : Free col) => q.jacobianColumn y.1 (eqn i).1 (eqn i).2.1 (eqn i).2.2)
        0 1 := by
    ext (i | x) (j | y)
    · simp [splitEquiv'_inl, newCoord_col, coeff_eqAt hq, minorAt]
    · simp [splitEquiv'_inl, splitEquiv'_inr, newCoord_col, coeff_eqAt hq]
    · simp only [Matrix.submatrix_apply, splitEquiv'_inl, splitEquiv'_inr, newCoord_free,
        Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply, coeff_X, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply]
      rw [if_neg]
      intro h
      exact x.2 ⟨j, Finsupp.single_left_injective one_ne_zero h⟩
    · simp only [Matrix.submatrix_apply, splitEquiv'_inr, newCoord_free, Matrix.of_apply,
        Equiv.refl_symm, Equiv.refl_apply, coeff_X, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      by_cases h : x = y
      · subst h; simp
      · rw [if_neg, if_neg h]
        intro h'
        exact h (Subtype.ext (Finsupp.single_left_injective one_ne_zero h').symm)
  rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  exact hdet.isUnit

include hq in
theorem newCoord_bijective (hdet : (minorAt q col eqn).det ≠ 0) :
    Function.Bijective (subst (R := k) (newCoord q col hcol eqn)) :=
  subst_bijective_equiv (Equiv.refl Var) (constantCoeff_newCoord q hq col hcol eqn)
    (isUnit_linear q hq col hcol eqn hdet)

include hq in
theorem hasSubst_newCoord : HasSubst (newCoord q col hcol eqn) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_newCoord q hq col hcol eqn)

include hq in
/-- The free variables, pushed through the coordinate change, into `Â_q`. -/
noncomputable def freeMap : MvPowerSeries (Free col) k →ₐ[k] AhatAt q :=
  (Ideal.Quotient.mkₐ k (idealAt q)).comp
    ((substAlgHom (hasSubst_newCoord q hq col hcol eqn)).comp (rename (freeEmb col)))

theorem range_freeEmb_compl : (Set.range (freeEmb col))ᶜ = Set.range col := by
  ext x
  simp [freeEmb]

include hq in
/-- **Formal inverse function theorem at `q`.** `Â_q` is a quotient of `k⟦Free⟧`. -/
theorem freeMap_surjective (hdet : (minorAt q col eqn).det ≠ 0) :
    Function.Surjective (freeMap q hq col hcol eqn) := by
  intro z
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨h, rfl⟩ := (newCoord_bijective q hq col hcol eqn hdet).2 g
  refine ⟨killCompl (freeEmb col) h, ?_⟩
  have hk : h - rename (freeEmb col) (killCompl (freeEmb col) h) ∈
      Ideal.span (X '' (Set.range (freeEmb col))ᶜ : Set (MvPowerSeries Var k)) := by
    rw [← ker_killCompl]
    change killCompl (freeEmb col) (h - rename (freeEmb col) (killCompl (freeEmb col) h)) = 0
    rw [map_sub, killCompl_rename_app, sub_self]
  rw [range_freeEmb_compl] at hk
  have hmap : substAlgHom (hasSubst_newCoord q hq col hcol eqn)
      (h - rename (freeEmb col) (killCompl (freeEmb col) h)) ∈ idealAt q := by
    have := Ideal.mem_map_of_mem (substAlgHom (hasSubst_newCoord q hq col hcol eqn)) hk
    rw [Ideal.map_span] at this
    refine Ideal.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    rw [substAlgHom_X, newCoord_col]
    exact Ideal.subset_span ⟨_, rfl⟩
  rw [map_sub] at hmap
  change Ideal.Quotient.mk _ (substAlgHom (hasSubst_newCoord q hq col hcol eqn) (rename (freeEmb col) (killCompl (freeEmb col) h))) =
    Ideal.Quotient.mk _ (subst _ h)
  rw [Ideal.Quotient.eq, ← substAlgHom_apply (hasSubst_newCoord q hq col hcol eqn)]
  rw [← neg_mem_iff, neg_sub]
  exact hmap

include hq in
/-- **Smoothness criterion.** If moreover `Â_q` maps onto a power series ring in as many
variables, then `Â_q ≃ k⟦Free⟧`. -/
theorem freeMap_bijective (hdet : (minorAt q col eqn).det ≠ 0) {P : Type} [Fintype P]
    (ρ : AhatAt q →+* MvPowerSeries P k) (hρ : Function.Surjective ρ) (e : P ≃ Free col) :
    Function.Bijective (freeMap q hq col hcol eqn) := by
  refine ⟨?_, freeMap_surjective q hq col hcol eqn hdet⟩
  let φ : MvPowerSeries (Free col) k →+* MvPowerSeries (Free col) k :=
    (renameEquiv k e).toRingEquiv.toRingHom.comp (ρ.comp (freeMap q hq col hcol eqn).toRingHom)
  have hφ : Function.Surjective φ :=
    (renameEquiv k e).surjective.comp (hρ.comp (freeMap_surjective q hq col hcol eqn hdet))
  have hinj := injective_of_surjective_endo φ hφ
  intro a b hab
  apply hinj
  change (renameEquiv k e) (ρ (freeMap q hq col hcol eqn a)) =
    (renameEquiv k e) (ρ (freeMap q hq col hcol eqn b))
  rw [hab]

end Inverse

end Brent.Formal
