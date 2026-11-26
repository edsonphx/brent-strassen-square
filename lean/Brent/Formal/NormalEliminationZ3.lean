import Brent.Formal.SmoothPoint
import Brent.Formal.BaseChange
import Brent.Z3Basis
import Brent.Census.Minors
import Brent.KernelCheck.SquareJacobianRank

/-! Normal elimination for the actual centered Brent equations over Z_(3).
The minor is obtained from the certified rank in F_3, not assumed as a
hypothesis. The same selected rows and columns are used before and after
reduction. All substitutions are untruncated formal power series. -/

namespace Brent.Formal.NormalEliminationZ3
open MvPowerSeries Brent.Z3 Brent.CM.LiftInstance
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev E := EquationIndex SquareVertex
abbrev V := Variable SquareVertex SquareSummand

/-- The actual Jacobian has a unit minor of size 2101 over the local integers. -/
theorem exists_unit_minor : ∃ (col : Fin 2101 → V) (eqn : Fin 2101 → E),
    Function.Injective col ∧ Function.Injective eqn ∧
    IsUnit (minorAt (strassenSquare R0) col eqn).det := by
  classical
  let M : Matrix E V (ZMod 3) := fun e x =>
    (strassenSquare (ZMod 3)).jacobianColumn x e.1 e.2.1 e.2.2
  have hrank : 2101 ≤ M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    change 2101 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3)
      (Set.range fun x : V => fun e : E =>
        (strassenSquare (ZMod 3)).jacobianColumn x e.1 e.2.1 e.2.2))
    rw [square_jacobian_rank]
  obtain ⟨eqn, col, hdet⟩ := Census.Minors.exists_minor_ne_zero M hrank
  have hcol : Function.Injective col := by
    intro i j hij
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_column_eq hne
    intro a
    simp [Matrix.submatrix_apply, hij]
  have heqn : Function.Injective eqn := by
    intro i j hij
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    funext a
    simp [Matrix.submatrix_apply, hij]
  let N : Matrix (Fin 2101) (Fin 2101) ℤ := fun i j => JInt (eqn i) (col j)
  have hN3 : N.map (Int.cast : ℤ → ZMod 3) = M.submatrix eqn col := by
    ext i j
    exact (jacobian_cast (ZMod 3) (eqn i) (col j)).symm
  have h3 : ¬ (3 : ℤ) ∣ N.det := by
    intro hd
    apply hdet
    rw [← hN3, ← Int.cast_det]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
  have hNR : N.map (Int.cast : ℤ → R0) = minorAt (strassenSquare R0) col eqn := by
    ext i j
    change (JInt (eqn i) (col j) : R0) =
      (strassenSquare R0).jacobianColumn (col j) (eqn i).1 (eqn i).2.1 (eqn i).2.2
    rw [JInt, strassenSquare, Decomposition.jacobianColumn_map, eq_intCast]
  refine ⟨col, eqn, hcol, heqn, ?_⟩
  rw [← hNR, ← Int.cast_det]
  have hm : N.det ∈ (Ideal.span {(3 : ℤ)}).primeCompl := by
    intro h
    exact h3 (Ideal.mem_span_singleton.mp h)
  have hu := IsLocalization.map_units R0 (⟨N.det, hm⟩ : (Ideal.span {(3 : ℤ)}).primeCompl)
  simpa [algebraMap_int_eq, eq_intCast] using hu

/-- Naturality of the actual centered cubic equations. -/
theorem map_eqAt_square (e : E) :
    MvPowerSeries.map rho3 (eqAt (strassenSquare R0) e) =
      eqAt (strassenSquare (ZMod 3)) e := by
  have hc (x : V) : rho3 ((strassenSquare R0).coordinates x) =
      (strassenSquare (ZMod 3)).coordinates x := by
    obtain ⟨s,m,a⟩ := x
    cases m <;> simp [strassenSquare, Decomposition.map, Decomposition.coordinates, map_intCast]
  have ht : rho3 (matrixMultiplicationEntry R0 e.1 e.2.1 e.2.2) =
      matrixMultiplicationEntry (ZMod 3) e.1 e.2.1 e.2.2 := by
    unfold matrixMultiplicationEntry
    split_ifs <;> simp
  simp only [eqAt, equation, map_sub, map_sum, map_mul, MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_C, map_add, MvPowerSeries.map_C, MvPowerSeries.map_X, hc, ht]

/-- The selected coordinate change itself commutes with reduction. -/
theorem map_newCoord {n : ℕ} (col : Fin n → V) (hcol : Function.Injective col)
    (eqn : Fin n → E) (x : V) :
    MvPowerSeries.map rho3 (newCoord (strassenSquare R0) col hcol eqn x) =
      newCoord (strassenSquare (ZMod 3)) col hcol eqn x := by
  classical
  by_cases hx : x ∈ Set.range col
  · obtain ⟨i, rfl⟩ := hx
    rw [newCoord_col, newCoord_col, map_eqAt_square]
  · let y : Free col := ⟨x,hx⟩
    change MvPowerSeries.map rho3 (newCoord (strassenSquare R0) col hcol eqn y) =
      newCoord (strassenSquare (ZMod 3)) col hcol eqn y
    simp only [newCoord_free, MvPowerSeries.map_X]

section InverseTuple
variable {R : Type} [CommRing R] [Nontrivial R]

/-- A bijective centered substitution has a centered inverse tuple.  Its
constant term is proved to vanish, not assumed. -/
theorem exists_centered_inverse (a : V → MvPowerSeries V R)
    (ha : ∀ x, constantCoeff (a x) = 0)
    (hbij : Function.Bijective (subst a)) :
    ∃ b : V → MvPowerSeries V R,
      (∀ x, constantCoeff (b x) = 0) ∧
      (∀ x, subst a (b x) = X x) ∧ (∀ x, subst b (a x) = X x) := by
  classical
  have hsa := hasSubst_of_constantCoeff_zero ha
  choose b hb using fun x : V => hbij.2 (X x)
  have hb0 (x : V) : constantCoeff (b x) = 0 := by
    have hz : constantCoeff (b x - C (constantCoeff (b x))) = 0 := by simp
    have h := constantCoeff_subst_eq_zero hsa ha hz
    have hC (r : R) : substAlgHom hsa (C r) = C r := by
      have hh := (substAlgHom hsa).commutes r
      rw [algebraMap_apply, algebraMap_apply] at hh
      exact hh
    rw [← substAlgHom_apply hsa, map_sub, substAlgHom_apply hsa, hb x,
      hC, map_sub, constantCoeff_X, constantCoeff_C, zero_sub, neg_eq_zero] at h
    exact h
  refine ⟨b, hb0, hb, fun x => hbij.1 ?_⟩
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb0) hsa]
  change subst (fun i => subst a (b i)) (a x) = subst a (X x)
  rw [show (fun i => subst a (b i)) = X from funext hb, subst_self, id,
    subst_X hsa]

end InverseTuple

/-- Set precisely the selected normal coordinates to zero, keeping the other
variables. The target is written in the ambient index set, so that identical
index sets are used over both coefficient rings. -/
noncomputable def killNormal {R : Type} [CommRing R] {n : ℕ} (col : Fin n → V)
    (x : V) : MvPowerSeries V R := by
  classical
  exact if x ∈ Set.range col then 0 else X x

theorem centered_killNormal {R : Type} [CommRing R] {n : ℕ} (col : Fin n → V) (x : V) :
    constantCoeff (killNormal (R := R) col x) = 0 := by
  classical
  unfold killNormal
  split_ifs <;> simp

theorem map_killNormal {n : ℕ} (col : Fin n → V) (x : V) :
    MvPowerSeries.map rho3 (killNormal (R := R0) col x) =
      killNormal (R := ZMod 3) col x := by
  classical
  unfold killNormal
  split_ifs <;> simp

/-- Actual all-orders normal elimination for a chosen unit minor: the inverse
exists over R0, its reduction is a two-sided inverse for the actual modular
coordinate tuple, selected Brent equations disappear, and every residual
Brent equation commutes with reduction. -/
theorem normal_elimination_for_minor {n : ℕ} (col : Fin n → V)
    (hcol : Function.Injective col) (eqn : Fin n → E)
    (hu : IsUnit (minorAt (strassenSquare R0) col eqn).det) :
    ∃ b : V → MvPowerSeries V R0,
      (∀ x, constantCoeff (b x) = 0) ∧
      (∀ x, subst (newCoord (strassenSquare R0) col hcol eqn) (b x) = X x) ∧
      (∀ x, subst b (newCoord (strassenSquare R0) col hcol eqn x) = X x) ∧
      (∀ x, subst (newCoord (strassenSquare (ZMod 3)) col hcol eqn)
          (MvPowerSeries.map rho3 (b x)) = X x) ∧
      (∀ x, subst (fun i => MvPowerSeries.map rho3 (b i))
          (newCoord (strassenSquare (ZMod 3)) col hcol eqn x) = X x) ∧
      (∀ j, subst (killNormal col) (subst b (eqAt (strassenSquare R0) (eqn j))) = 0) ∧
      (∀ e : E, MvPowerSeries.map rho3
        (subst (killNormal col) (subst b (eqAt (strassenSquare R0) e))) =
        subst (killNormal col) (subst (fun i => MvPowerSeries.map rho3 (b i))
          (eqAt (strassenSquare (ZMod 3)) e))) := by
  let a := newCoord (strassenSquare R0) col hcol eqn
  have ha := constantCoeff_newCoord _ (strassenSquare_solves R0) col hcol eqn
  have hbij := newCoord_bijective_of_unit _ (strassenSquare_solves R0) col hcol eqn hu
  obtain ⟨b, hb, hab, hba⟩ := exists_centered_inverse a ha hbij
  obtain ⟨hmba, hmab⟩ := inverse_tuple_baseChange rho3 a b ha hb hba hab
  have hmap : (fun x => MvPowerSeries.map rho3 (a x)) =
      newCoord (strassenSquare (ZMod 3)) col hcol eqn :=
    funext (map_newCoord col hcol eqn)
  rw [hmap] at hmba hmab
  refine ⟨b, hb, hab, hba, hmab, hmba, ?_, ?_⟩
  · intro j
    rw [← newCoord_col (strassenSquare R0) col hcol eqn j, hba (col j),
      subst_X (hasSubst_of_constantCoeff_zero (centered_killNormal col))]
    classical
    simp [killNormal, Set.mem_range_self]
  · intro e
    rw [map_subst_centered rho3 (centered_killNormal col),
      map_subst_centered rho3 hb, map_eqAt_square]
    rw [show (fun i => MvPowerSeries.map rho3 (killNormal (R := R0) col i)) =
      killNormal (R := ZMod 3) col from funext (map_killNormal col)]

/-- The concrete chart has 251 free coordinates. -/
theorem card_free (col : Fin 2101 → V) (hcol : Function.Injective col) :
    Fintype.card (Free col) = 251 := by
  classical
  have h := Fintype.card_congr (splitEquiv' col hcol)
  rw [Fintype.card_sum, Fintype.card_fin, square_variable_count] at h
  omega

/-- The actual 2101-equation elimination exists with 251 free coordinates,
with no assumed minor or inverse, and every residual equation reduces naturally. -/
theorem normal_elimination_exists :
    ∃ (col : Fin 2101 → V) (eqn : Fin 2101 → E)
      (hcol : Function.Injective col) (b : V → MvPowerSeries V R0),
      Function.Injective eqn ∧ Fintype.card (Free col) = 251 ∧
      (∀ x, constantCoeff (b x) = 0) ∧
      (∀ x, subst (newCoord (strassenSquare R0) col hcol eqn) (b x) = X x) ∧
      (∀ x, subst b (newCoord (strassenSquare R0) col hcol eqn x) = X x) ∧
      (∀ x, subst (newCoord (strassenSquare (ZMod 3)) col hcol eqn)
          (MvPowerSeries.map rho3 (b x)) = X x) ∧
      (∀ x, subst (fun i => MvPowerSeries.map rho3 (b i))
          (newCoord (strassenSquare (ZMod 3)) col hcol eqn x) = X x) ∧
      (∀ j, subst (killNormal col) (subst b (eqAt (strassenSquare R0) (eqn j))) = 0) ∧
      (∀ e : E, MvPowerSeries.map rho3
        (subst (killNormal col) (subst b (eqAt (strassenSquare R0) e))) =
        subst (killNormal col) (subst (fun i => MvPowerSeries.map rho3 (b i))
          (eqAt (strassenSquare (ZMod 3)) e))) := by
  obtain ⟨col, eqn, hc, he, hu⟩ := exists_unit_minor
  obtain ⟨b, hb⟩ := normal_elimination_for_minor col hc eqn hu
  exact ⟨col, eqn, hc, b, he, card_free col hc, hb⟩

end Brent.Formal.NormalEliminationZ3
