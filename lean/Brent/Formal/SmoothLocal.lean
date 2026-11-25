import Brent.Formal.GermLower
import Brent.Formal.SmoothFamily

/-!
# Local dimension lower bound at a block point

For a block point `pq` (identity global changes and scalings) and `n` chosen group parameters,
the group element `1 + Σᵢ tᵢ Eᵢ` built over the germ `k[t₁,…,tₙ]_(t)` moves `q = pq.value left`
along an exact family. Its `i`-th derivative is the closed-form tangent
`qTangent pq left (params i)`. If these `n` tangents are linearly independent then
`n ≤ dim 𝒪_q` (`GermLower.le_pointLocalDimension`).
-/

open scoped BigOperators

namespace Brent.Formal

open GermLower

set_option linter.unusedSectionVars false

variable (k : Type) [Field k] {n : ℕ} (params : Fin n → GrpIdx)

theorem qUnit_base (w : GrpIdx) : (qUnit (k := k) w).map (Jets.forget k) = FamilyParameters.one k := by
  rcases w with (⟨g, i, j⟩ | ⟨s, c⟩) | ⟨l, g, i, j⟩
  · exact FamilyParameters.globalUnit_base g i j
  · exact FamilyParameters.termUnit_base s _
  · exact FamilyParameters.blockUnit_base l g i j

noncomputable def unitGlobal (g : Fin 3) (i : Fin n) : Matrix SquareVertex SquareVertex k :=
  fun a b => (((qUnit (k := k) (params i)).global g).val a b).snd

noncomputable def unitBlock (l : Fin 7) (g : Fin 3) (i : Fin n) : Matrix (Fin 2) (Fin 2) k :=
  fun a b => (((qUnit (k := k) (params i)).block l g).val a b).snd

noncomputable def unitScale (s : SquareSummand) (c : Fin 2) (i : Fin n) : k :=
  (((qUnit (k := k) (params i)).scale s c).val).snd

/-- The group element `1 + Σᵢ tᵢ Eᵢ` over the parameter germ. -/
noncomputable def multiQ : FamilyParameters (Germ k n) :=
  ⟨fun g => (isUnit_germMatrix k n (unitGlobal k params g)).unit,
   fun l g => (isUnit_germMatrix k n (unitBlock k params l g)).unit,
   fun s c => (isUnit_germScalar k n (unitScale k params s c)).unit⟩

theorem multiQ_residue : (multiQ k params).map (residue k n) = FamilyParameters.one k := by
  simp only [multiQ, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext
    exact map_residue_germMatrix k n _
  · funext s g; apply Units.ext
    exact map_residue_germMatrix k n _
  · funext s c; apply Units.ext
    exact residue_germScalar k n _

theorem multiQ_germJet (j : Fin n) :
    (multiQ k params).map (germJet k n j) = qUnit (params j) := by
  have hb := qUnit_base k (params j)
  simp only [FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq] at hb
  change _ = FamilyParameters.mk (qUnit (k := k) (params j)).global (qUnit (params j)).block
    (qUnit (params j)).scale
  simp only [multiQ, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((qUnit (k := k) (params j)).global g).val a b).fst =
        (1 : Matrix SquareVertex SquareVertex k) a b :=
      congrArg (fun u : (Matrix SquareVertex SquareVertex k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun hb.1 g)
    change germJet k n j (germMatrix k n (unitGlobal k params g) a b) = _
    rw [germJet_germMatrix]
    exact TrivSqZeroExt.ext h1.symm rfl
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((qUnit (k := k) (params j)).block s g).val a b).fst =
        (1 : Matrix (Fin 2) (Fin 2) k) a b :=
      congrArg (fun u : (Matrix (Fin 2) (Fin 2) k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun (congrFun hb.2.1 s) g)
    change germJet k n j (germMatrix k n (unitBlock k params s g) a b) = _
    rw [germJet_germMatrix]
    exact TrivSqZeroExt.ext h1.symm rfl
  · funext s c; apply Units.ext
    have h1 : (((qUnit (k := k) (params j)).scale s c).val).fst = 1 :=
      congrArg (fun u : kˣ => (u : k)) (congrFun (congrFun hb.2.2 s) c)
    change germJet k n j (germScalar k n (unitScale k params s c)) = _
    rw [germJet_germScalar]
    exact TrivSqZeroExt.ext h1.symm rfl

variable (pq : FamilyParameters k) (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1)
  (left : Bool)

include hg hs in
/-- The tangent of the jet `pq · qUnit w` is the closed form `qTangent`. -/
theorem snd_qUnit_value (w₀ : GrpIdx) (x : Var) :
    ((((pq.map (Jets.constant k)).mul (qUnit w₀)).value left).coordinates x).snd =
      qTangent pq left w₀ x := by
  obtain ⟨s, m, a, b⟩ := x
  rcases w₀ with (⟨g, i, j⟩ | ⟨s₀, c⟩) | ⟨l, g, i, j⟩
  · rw [qTangent, ← FamilyParameters.globalUnit_tangentAt pq hg hs left g i j s m a b]
    cases m <;> rfl
  · rw [qTangent, ← FamilyParameters.termUnit_tangentAt pq hg hs left s₀ _ s m a b]
    cases m <;> rfl
  · rw [qTangent, ← FamilyParameters.blockUnit_tangentAt pq hg hs left l g i j s m a b]
    cases m <;> rfl

/-- The exact family through `q` over the parameter germ. -/
noncomputable def germFamily : Decomposition (Germ k n) SquareVertex SquareSummand :=
  ((pq.map (algebraMap k (Germ k n))).mul (multiQ k params)).value left

theorem residue_comp_algebraMap (m : ℕ) :
    (residue k m).comp (algebraMap k (Germ k m)) = RingHom.id k := by
  ext c; exact residue_algebraMap_k k m c

theorem germJet_comp_algebraMap {m : ℕ} (j : Fin m) :
    (germJet k m j).comp (algebraMap k (Germ k m)) = Jets.constant k := by
  ext c
  · rw [RingHom.comp_apply, germJet_algebraMap_k]; rfl
  · rw [RingHom.comp_apply, germJet_algebraMap_k]; rfl

theorem germFamily_residue (x : Var) :
    residue k n ((germFamily k params pq left).coordinates x) = (pq.value left).coordinates x := by
  rw [← LowerBound.coordinates_map, germFamily, FamilyParameters.value_map,
    FamilyParameters.map_mul, FamilyParameters.map_comp, residue_comp_algebraMap,
    FamilyParameters.map_id, multiQ_residue, FamilyParameters.mul_one]

include hg hs in
theorem germFamily_germJet (j : Fin n) (x : Var) :
    (germJet k n j ((germFamily k params pq left).coordinates x)).snd =
      qTangent pq left (params j) x := by
  rw [← LowerBound.coordinates_map, germFamily, FamilyParameters.value_map,
    FamilyParameters.map_mul, FamilyParameters.map_comp, germJet_comp_algebraMap, multiQ_germJet]
  exact snd_qUnit_value k pq hg hs left (params j) x

include hg hs in
/-- **Lower bound at a block point.** `n` independent closed-form tangents give `n ≤ dim 𝒪_q`. -/
theorem le_localDimension_of_tangents
    (hD : LinearIndependent k (Matrix.of fun i x => qTangent pq left (params i) x).row) :
    (n : WithBot ℕ∞) ≤
      ringKrullDim (PointLocalRing (pq.value left) (FamilyParameters.value_solves left pq)) :=
  le_pointLocalDimension k n (pq.value left) (FamilyParameters.value_solves left pq)
    (germFamily k params pq left) (FamilyParameters.value_solves left _)
    (germFamily_residue k params pq left) _ hD (germFamily_germJet k params pq hg hs left)

end Brent.Formal
