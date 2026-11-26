import Brent.LWH.Kernel
import Brent.PointTangents

/-!
# The 146 orbit generators at the Li–Wang–Hu point span 143 dimensions

The generators are the 48 matrix units of the three global `GL₄` factors and the 98 term
scalings (compensated in the second input or in the output), indexed as follows:

* `n < 48`: the matrix unit `(g, i, j) = (n / 16, (n % 16) / 4, n % 4)` in vertex `g`;
* `n ≥ 48`: the scaling of summand `(n - 48) / 2`, compensated in the second input if
  `n - 48` is odd and in the output if it is even.

Each generator is the tangent of an exact dual-number family through the point (a change of
basis or a rescaling), so it lies in the kernel of the Jacobian over every field. A `143 × 143`
minor is upper triangular with diagonal `±1` (kernel-checked), so 143 of them are independent
over every field. The three remaining generators, the identity units `(g, 0, 0)`, are integer
combinations of the kept ones (the central scalings), so the span has dimension exactly 143.
-/

open scoped BigOperators Matrix

namespace Brent.LWH

/-- Vertex number `n` (row-major in the `4 × 4` matrix). -/
def vtx (n : Nat) : SquareVertex := finProdFinEquiv.symm (Fin.ofNat 4 n)

/-- Summand number `n`. -/
def summ (n : Nat) : SquareSummand := finProdFinEquiv.symm (Fin.ofNat 49 n)

/-- Coordinates of orbit generator `n` at a decomposition `d`. -/
def orbitCoord {R : Type} [CommRing R] (d : Decomposition R SquareVertex SquareSummand)
    (n : Fin 146) : Variable SquareVertex SquareSummand → R
  | (s, m, (a, b)) =>
    if n.val < 48 then
      d.vertexUnitCoefficient (Fin.ofNat 3 (n.val / 16)) (vtx (n.val % 16 / 4)) (vtx (n.val % 4)) s m a b
    else
      FamilyParameters.termUnitCoefficient d (summ ((n.val - 48) / 2)) ((n.val - 48) % 2 == 1) s m a b

theorem orbitCoord_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (d : Decomposition R SquareVertex SquareSummand) (n : Fin 146)
    (x : Variable SquareVertex SquareSummand) :
    orbitCoord (d.map f) n x = f (orbitCoord d n x) := by
  obtain ⟨s, m, a, b⟩ := x
  simp only [orbitCoord]
  split_ifs
  · exact Decomposition.vertexUnitCoefficient_map f d _ _ _ s m a b
  · exact FamilyParameters.termUnitCoefficient_map f d _ _ s m a b

section Field

variable (K : Type) [Field K]

/-- The orbit generators at the point over `K`. -/
noncomputable def orbitGens (n : Fin 146) : Variable SquareVertex SquareSummand → K :=
  orbitCoord (pointK K) n

theorem orbitGens_cast (n : Fin 146) (x : Variable SquareVertex SquareSummand) :
    orbitGens K n x = (orbitCoord pointDec n x : K) :=
  orbitCoord_map (Int.castRingHom K) pointDec n x

/-! ### Every generator is tangent -/

/-- Matrix–vector form of `tangent_satisfies_differential`. -/
theorem mulVec_tangent {q : Decomposition K SquareVertex SquareSummand}
    (D : Decomposition (DualNumber K) SquareVertex SquareSummand) (hD : D.Solves)
    (hc : D.constantPart = q) (v : Variable SquareVertex SquareSummand → K)
    (hv : ∀ x, D.tangentPart.coordinates x = v x) :
    (Matrix.of fun (e : EquationIndex SquareVertex) (x : Variable SquareVertex SquareSummand) =>
      q.jacobianColumn x e.1 e.2.1 e.2.2) *ᵥ v = 0 := by
  funext e
  have h0 := Decomposition.tangent_satisfies_differential D hD e.1 e.2.1 e.2.2
  rw [hc, Decomposition.jacobianEntry_eq_sum] at h0
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rw [← h0]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hv, mul_comm]

theorem map_constant_forget (d : Decomposition K SquareVertex SquareSummand) :
    (d.map (Jets.constant K)).map (Jets.forget K) = d := by
  cases d
  rfl

/-- The dual-number family of a global matrix-unit generator. -/
noncomputable def vertexJet (g : Fin 3) (i j : SquareVertex) :
    Decomposition (DualNumber K) SquareVertex SquareSummand :=
  ((pointK K).map (Jets.constant K)).changeBasis
    (matrixJet (Decomposition.vertexUnit g 0 i j)) (matrixJet (Decomposition.vertexUnit g 1 i j))
    (matrixJet (Decomposition.vertexUnit g 2 i j))

/-- The dual-number family of a term scaling. -/
noncomputable def termJet (k : SquareSummand) (second : Bool) :
    Decomposition (DualNumber K) SquareVertex SquareSummand :=
  ((pointK K).map (Jets.constant K)).rescale (fun s => Jets.scalarJet (if s = k then 1 else 0))
    (fun s => Jets.scalarJet (if s = k then (if second then -1 else 0) else 0))

variable {K}

theorem vertexJet_solves (hq : pointDec.Solves) (g : Fin 3) (i j : SquareVertex) :
    (vertexJet K g i j).Solves :=
  Decomposition.solves_changeBasis
    (Decomposition.solves_map _ (Decomposition.solves_map _ hq)) _ _ _

theorem termJet_solves (hq : pointDec.Solves) (k : SquareSummand) (second : Bool) :
    (termJet K k second).Solves :=
  Decomposition.solves_rescale (Decomposition.solves_map _ (Decomposition.solves_map _ hq)) _ _

theorem vertexJet_constant (g : Fin 3) (i j : SquareVertex) :
    (vertexJet K g i j).constantPart = pointK K := by
  change (vertexJet K g i j).map (Jets.forget K) = pointK K
  rw [vertexJet, Decomposition.map_changeBasis]
  simp only [Jets.forget_matrixJet, map_constant_forget, Decomposition.changeBasis_identity]

theorem termJet_constant (k : SquareSummand) (second : Bool) :
    (termJet K k second).constantPart = pointK K := by
  change (termJet K k second).map (Jets.forget K) = pointK K
  rw [termJet, Decomposition.map_rescale]
  simp only [Jets.forget_scalarJet, map_constant_forget, FamilyParameters.rescale_identity]

theorem vertexJet_tangent (g : Fin 3) (i j : SquareVertex) (s : SquareSummand) (m : Mode)
    (a b : SquareVertex) :
    (vertexJet K g i j).tangentPart.coordinates (s, m, (a, b)) =
      (pointK K).vertexUnitCoefficient g i j s m a b := by
  rw [vertexJet, Decomposition.tangent_changeBasis, Decomposition.vertexVariation_unit]

theorem termJet_tangent (k : SquareSummand) (second : Bool) (s : SquareSummand) (m : Mode)
    (a b : SquareVertex) :
    (termJet K k second).tangentPart.coordinates (s, m, (a, b)) =
      FamilyParameters.termUnitCoefficient (pointK K) k second s m a b := by
  cases second <;> cases m <;> by_cases hk : s = k <;>
    simp [termJet, FamilyParameters.termUnitCoefficient, Decomposition.coordinates,
      Decomposition.rescale, Decomposition.tangentPart, Jets.scalarJet, Decomposition.map,
      Jets.constant, hk]

variable (K)

/-- **Every orbit generator lies in the kernel of the Jacobian**, over every field. -/
theorem orbitGens_tangent (hq : pointDec.Solves) (n : Fin 146) : jacK K *ᵥ orbitGens K n = 0 := by
  by_cases hn : n.val < 48
  · refine mulVec_tangent K
      (vertexJet K (Fin.ofNat 3 (n.val / 16)) (vtx (n.val % 16 / 4)) (vtx (n.val % 4)))
      (vertexJet_solves hq _ _ _) (vertexJet_constant _ _ _) _ ?_
    rintro ⟨s, m, a, b⟩
    rw [vertexJet_tangent]
    simp only [orbitGens, orbitCoord, if_pos hn]
  · refine mulVec_tangent K
      (termJet K (summ ((n.val - 48) / 2)) ((n.val - 48) % 2 == 1))
      (termJet_solves hq _ _) (termJet_constant _ _) _ ?_
    rintro ⟨s, m, a, b⟩
    rw [termJet_tangent]
    simp only [orbitGens, orbitCoord, if_neg hn]

end Field

/-! ### 143 independent generators -/

/-- The integer orbit minor on the chosen coordinates. -/
def orbitMinor : Matrix (Fin 143) (Fin 143) ℤ :=
  Matrix.of fun i j => orbitCoord pointDec (kept i) (squareVariableNumber.symm (orbitCoordNum j))

set_option maxRecDepth 100000 in
theorem orbitMinor_upper : ∀ i j : Fin 143, j < i → orbitMinor i j = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem orbitMinor_diag : ∀ i : Fin 143, orbitMinor i i = 1 ∨ orbitMinor i i = -1 := by
  decide +kernel

theorem isUnit_det_orbitMinor : IsUnit orbitMinor.det := by
  have hup : orbitMinor.BlockTriangular id := fun i j hij => orbitMinor_upper i j hij
  rw [Matrix.det_of_upperTriangular hup]
  refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ => ?_
  rcases orbitMinor_diag i with h | h <;> rw [h]
  · exact isUnit_one
  · exact isUnit_one.neg

section Field

variable (K : Type) [Field K]

theorem orbitGens_minor (i j : Fin 143) :
    orbitGens K (kept i) (squareVariableNumber.symm (orbitCoordNum j)) =
      (orbitMinor.map (Int.castRingHom K)) i j := by
  rw [orbitGens_cast]
  rfl

theorem kept_independent : LinearIndependent K (fun i => orbitGens K (kept i)) := by
  have hu : IsUnit (orbitMinor.map (Int.castRingHom K)) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_det_orbitMinor.map _
  have h : LinearIndependent K (orbitMinor.map (Int.castRingHom K)).row :=
    Matrix.linearIndependent_rows_of_isUnit hu
  apply LinearIndependent.of_comp
    (LinearMap.funLeft K K fun j => squareVariableNumber.symm (orbitCoordNum j))
  convert h using 1
  funext i j
  exact orbitGens_minor K i j

/-! ### The three central relations -/

set_option maxRecDepth 100000 in
theorem kept_or_excluded : ∀ n : Fin 146, (∃ i, kept i = n) ∨ ∃ g, excl g = n := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem relList_kept : ∀ g : Fin 3, ∀ y ∈ relList g, ∃ i, kept i = y.1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem relation_int : ∀ g : Fin 3, ∀ x : Fin 2352,
    orbitCoord pointDec (excl g) (squareVariableNumber.symm x) =
      ((relList g).map fun y => y.2 * orbitCoord pointDec y.1 (squareVariableNumber.symm x)).sum := by
  decide +kernel

theorem list_sum_apply {ι : Type*} (l : List ι) (F : ι → Variable SquareVertex SquareSummand → K)
    (x : Variable SquareVertex SquareSummand) :
    (l.map F).sum x = (l.map fun y => F y x).sum := by
  induction l with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem orbitGens_excl (g : Fin 3) :
    orbitGens K (excl g) = ((relList g).map fun y => (y.2 : K) • orbitGens K y.1).sum := by
  funext x
  rw [list_sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, orbitGens_cast]
  have h := relation_int g (squareVariableNumber x)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  simp [Int.cast_list_sum, List.map_map, Function.comp_def]

theorem list_sum_mem {ι : Type*} {S : Submodule K (Variable SquareVertex SquareSummand → K)}
    (l : List ι) (F : ι → Variable SquareVertex SquareSummand → K) (h : ∀ y ∈ l, F y ∈ S) :
    (l.map F).sum ∈ S := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    exact S.add_mem (h y (by simp)) (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem orbit_span_eq : Submodule.span K (Set.range (orbitGens K)) =
    Submodule.span K (Set.range fun i => orbitGens K (kept i)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    rcases kept_or_excluded n with ⟨i, rfl⟩ | ⟨g, rfl⟩
    · exact Submodule.subset_span ⟨i, rfl⟩
    · rw [SetLike.mem_coe, orbitGens_excl K g]
      apply list_sum_mem K
      intro y hy
      obtain ⟨i, hi⟩ := relList_kept g y hy
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, congrArg (orbitGens K) hi⟩
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨kept i, rfl⟩

/-- **The orbit generators span a space of dimension 143**, over every field. -/
theorem orbit_finrank : Module.finrank K (Submodule.span K (Set.range (orbitGens K))) = 143 := by
  rw [orbit_span_eq K, finrank_span_eq_card (kept_independent K), Fintype.card_fin]

end Field

end Brent.LWH
