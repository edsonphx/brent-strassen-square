import Brent.Formal.SmoothPoint

/-!
# The swap symmetry at an arbitrary solution

The variable permutation `piV` maps each equation centered at `q` to an equation centered at
`swapDec q`, so it induces `Â_q ≃ Â_{swapDec q}`. At a block point with trivial global part,
`swapDec (pq.value true) = pq.value false`, so the two orientations have isomorphic formal
neighbourhoods.
-/

namespace Brent.Formal

open MvPowerSeries

set_option linter.unusedSectionVars false

variable (k : Type) [Field k]

/-- **The swap permutes the equations centered at `q` into those centered at `swapDec q`.** -/
theorem swapPS_eqAt (q : Decomposition k SquareVertex SquareSummand)
    (abc : EquationIndex SquareVertex) :
    swapPS k (eqAt q abc) = eqAt (swapDec q) (Kp abc.1, Kp abc.2.1, Kp abc.2.2) := by
  rw [swapPS, eqAt, algHom_eval₂]
  simp only [map_add, algHom_C, substAlgHom_X]
  rw [eqAt, eval₂_equation, eval₂_equation]
  have h : univ k (fun x => C (q.coordinates x) + X (piV x)) =
      swapDec (univ k (fun y => (C ((swapDec q).coordinates y) + X y : MvPowerSeries Var k))) := by
    change univ k _ = univ k (fun x => C ((swapDec q).coordinates (piV x)) + X (piV x))
    simp only [coordinates_swapDec, piV_piV]
  rw [h, entry_swapDec]
  simp only [mme_Kp]

theorem map_swapPS_idealAt_le (q : Decomposition k SquareVertex SquareSummand) :
    Ideal.map (swapPS k) (idealAt q) ≤ idealAt (swapDec q) := by
  rw [idealAt, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨abc, rfl⟩, rfl⟩
  rw [swapPS_eqAt]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- The swap `Â_q → Â_{swapDec q}`. -/
noncomputable def swapAt (q : Decomposition k SquareVertex SquareSummand) :
    AhatAt q →ₐ[k] AhatAt (swapDec q) :=
  Ideal.Quotient.liftₐ (idealAt q) ((Ideal.Quotient.mkₐ k (idealAt (swapDec q))).comp (swapPS k))
    fun a ha => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact map_swapPS_idealAt_le k q (Ideal.mem_map_of_mem _ ha)

theorem swapAt_mk (q : Decomposition k SquareVertex SquareSummand) (f : MvPowerSeries Var k) :
    swapAt k q (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (swapPS k f) := rfl

theorem swapAt_swapAt (q : Decomposition k SquareVertex SquareSummand) (a : AhatAt q) :
    swapAt k (swapDec q) (swapAt k q a) = a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [swapAt_mk, swapAt_mk, swapPS_swapPS]
  rfl

/-- **`Â_q ≃ Â_{swapDec q}`.** -/
noncomputable def swapAtEquiv (q : Decomposition k SquareVertex SquareSummand) :
    AhatAt q ≃ₐ[k] AhatAt (swapDec q) :=
  AlgEquiv.ofAlgHom (swapAt k q) (swapAt k (swapDec q))
    (AlgHom.ext (swapAt_swapAt k (swapDec q))) (AlgHom.ext (swapAt_swapAt k q))

/-- At a block point with trivial global part the swap exchanges the two orientations. -/
theorem swapDec_value_trivial {R : Type} [CommRing R] (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) :
    swapDec (pq.value true) = pq.value false := by
  rw [swapDec_value]
  congr 1
  obtain ⟨pg, pb, ps⟩ := pq
  simp only at hg hs
  subst hg hs
  simp only [swapParams, FamilyParameters.mk.injEq, true_and, and_true]
  funext g
  exact map_one _

end Brent.Formal
