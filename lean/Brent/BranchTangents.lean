import Brent.KernelCheck.FamilyQuadratics

/-!
# The branch tangent spaces meet in `T₀` (`paper.tex` line 329)

DRAFT, NOT YET COMPILED.

"The two branch tangent spaces intersect precisely in `T₀`."

The 251 archived vectors are a basis of `ker J` (`archived_frame_rank`); vectors `0 … 142` span
`T₀`, `143 … 196` span `X` and `197 … 250` span `Y`. The vectors in the chart of either family are
first derivatives of that family (`archived_origin`). The branch tangent space of the left family
is `T₀ + X` (indices `< 197`), of the right family `T₀ + Y` (indices `< 143` or `≥ 197`), each of
dimension 197 (lines 321–328). Their intersection is `T₀`, of dimension 143.
-/

open scoped BigOperators

namespace Brent.TangentData

variable (k : Type*) [Field k]

/-- For an independent family, spans of images of index sets meet in the span of the image of the
intersection. -/
theorem span_image_inf_span_image {ι M : Type*} [AddCommGroup M] [Module k M] {v : ι → M}
    (hv : LinearIndependent k v) (s t : Set ι) :
    Submodule.span k (v '' s) ⊓ Submodule.span k (v '' t) = Submodule.span k (v '' (s ∩ t)) := by
  refine le_antisymm ?_ (le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
    (Submodule.span_mono (Set.image_mono Set.inter_subset_right)))
  rintro x ⟨hs, ht⟩
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp hs
  obtain ⟨l', hl', e⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp ht
  have : l' = l := hv e
  subst this
  refine (Finsupp.mem_span_image_iff_linearCombination k).mpr ⟨l', ?_, rfl⟩
  rw [Finsupp.supported_inter]
  exact ⟨hl, hl'⟩

/-- The archived frame over `k`. -/
noncomputable def frameVec (i : Fin 251) : Fin 2352 → k :=
  SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i)

theorem frameVec_independent : LinearIndependent k (frameVec k) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin 251) = Module.finrank k (Submodule.span k
    (Set.range (fun i => SparseRow.decode (K := k) (Fin.val : Fin 2352 → Nat) (frame i))))
  rw [archived_frame_rank, Fintype.card_fin]

/-- `T₀`: the span of the 143 orbit directions. -/
noncomputable def orbitTangent : Submodule k (Fin 2352 → k) :=
  Submodule.span k (frameVec k '' {i | i.val < 143})

/-- The tangent space of either branch: the span of the archived vectors in that family's chart. -/
noncomputable def branchTangent (left : Bool) : Submodule k (Fin 2352 → k) :=
  Submodule.span k (frameVec k '' {i | InChart i left})

/-- Every vector spanning a branch tangent space is a first derivative of that family. -/
theorem branchTangent_generators (left : Bool) (i : Fin 251) (h : InChart i left) :
    ((castOrigin k i).value left).tangentPart = frameDirection k i :=
  archived_origin k i left h

private theorem finrank_image {P : Fin 251 → Prop} [DecidablePred P] :
    Module.finrank k (Submodule.span k (frameVec k '' {i | P i})) =
      (Finset.univ.filter P).card := by
  have h := finrank_span_eq_card ((frameVec_independent k).comp
    (Subtype.val : {i // P i} → Fin 251) Subtype.val_injective)
  rw [Set.range_comp, Subtype.range_coe_subtype, Fintype.card_subtype] at h
  exact h

theorem finrank_orbitTangent : Module.finrank k (orbitTangent k) = 143 := by
  rw [orbitTangent, finrank_image]
  decide

private theorem inChart_true (i : Fin 251) : InChart i true ↔ i.val < 197 := Iff.rfl

private theorem inChart_false (i : Fin 251) : InChart i false ↔ i.val < 143 ∨ 197 ≤ i.val := Iff.rfl

/-- Lines 321–328: both branch tangent spaces have dimension 197. -/
theorem finrank_branchTangent (left : Bool) : Module.finrank k (branchTangent k left) = 197 := by
  cases left
  · rw [branchTangent, show {i : Fin 251 | InChart i false} = {i | i.val < 143 ∨ 197 ≤ i.val} from
      Set.ext inChart_false, finrank_image]
    decide
  · rw [branchTangent, show {i : Fin 251 | InChart i true} = {i | i.val < 197} from
      Set.ext inChart_true, finrank_image]
    decide

/-- Line 329: "The two branch tangent spaces intersect precisely in `T₀`." -/
theorem branchTangent_inf : branchTangent k true ⊓ branchTangent k false = orbitTangent k := by
  rw [branchTangent, branchTangent, span_image_inf_span_image k (frameVec_independent k),
    orbitTangent]
  congr 2
  ext i
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, inChart_true, inChart_false]
  omega

/-- The two branch tangent spaces are different (`T₀ + X ≠ T₀ + Y`). -/
theorem branchTangent_ne : branchTangent k true ≠ branchTangent k false := by
  intro h
  have := congrArg (Module.finrank k) (inf_idem (branchTangent k true))
  rw [show branchTangent k true ⊓ branchTangent k true =
      branchTangent k true ⊓ branchTangent k false by rw [← h], branchTangent_inf,
    finrank_orbitTangent, finrank_branchTangent] at this
  omega

end Brent.TangentData
