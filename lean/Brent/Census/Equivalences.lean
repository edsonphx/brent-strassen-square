import Brent.Census.RankBoundLink

/-!
# §7: the anchor exclusion is invariant under the equivalences (F18e)

DRAFT, NOT YET COMPILED.

Paper, lines 668–688: the rank tests hold "even allowing summand and mode permutations", and for
the anchor test "Left and right changes preserve the inclusions."

**Equivalences.** `Equivalent v' v` says that, after a summand permutation `τ` and a map of modes
`π`, every mode matrix of `v'` is `c • (L M R)` or `c • (L Mᵀ R)` for the corresponding mode
matrix `M` of `v`, with `L`, `R` invertible and depending only on the mode, and `c ≠ 0`. This
covers the `GL₄³`-action (`equivalent_changeBasis`), term rescalings (`equivalent_rescale`),
summand permutations, cyclic mode permutations and the transpose symmetry `(u, v, w) ↦
(wᵀ, vᵀ, uᵀ)` (`τ`, `π` and `tr` in the definition). `eqClosed k` is the set of all points
equivalent to a point of either family.

**Shape.** `Shape v σ left` says that `v` satisfies the rank budgets and the stacking conditions
after relabelling the summands by `σ`. It is Zariski closed for each `σ` (`isClosed_shape`),
holds on the families with `σ = id`, and passes to equivalent points with `σ` composed with `τ⁻¹`
(`shape_of_equivalent`). Since there are finitely many `σ`, the closure of `eqClosed k` lies in
the finite union of the closed sets `Shape · σ left` (`closure_eqClosed_subset`).

**Conclusion.** At a full-profile point with some shape, every rank equals its budget at the
relabelled summand, and the anchor test holds (`anchorTest_of_shape`). So 2445 and 5969 are not
in the closure of the families closed under all equivalences (`anchor_excluded_eqClosed`).
-/

open MvPolynomial
open scoped BigOperators

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure Brent.Catalogue

variable {k : Type} [Field k]

/-! ### Equivalences -/

/-- `v'` is equivalent to `v`: up to summand and mode relabelling and (optionally) transposition,
each mode matrix changes by `M ↦ c • (L M R)` with invertible `L`, `R` depending only on the mode
and nonzero scalars `c`. -/
def Equivalent (v' v : Var → k) : Prop :=
  ∃ (τ : SquareSummand ≃ SquareSummand) (π : Mode → Mode) (tr : Bool)
    (L R : Mode → Matrix SquareVertex SquareVertex k) (c : SquareSummand → Mode → k),
    (∀ m, IsUnit (L m) ∧ IsUnit (R m)) ∧ (∀ s m, c s m ≠ 0) ∧
      ∀ s m, modeMat v' s m = c s m • (L m * (if tr then (modeMat v (τ s) (π m)).transpose
        else modeMat v (τ s) (π m)) * R m)

theorem equivalent_refl (v : Var → k) : Equivalent v v :=
  ⟨Equiv.refl _, id, false, fun _ => 1, fun _ => 1, fun _ _ => 1,
    fun _ => ⟨isUnit_one, isUnit_one⟩, fun _ _ => one_ne_zero, fun s m => by simp⟩

/-- The `GL₄³`-action is an equivalence. -/
theorem equivalent_changeBasis (d : Decomposition k SquareVertex SquareSummand)
    (P Q T : (Matrix SquareVertex SquareVertex k)ˣ) :
    Equivalent (d.changeBasis P Q T).coordinates d.coordinates := by
  choose L R hL hR h using fun m => modeMat_changeBasis_units d P Q T m
  exact ⟨Equiv.refl _, id, false, L, R, fun _ _ => 1, fun m => ⟨hL m, hR m⟩,
    fun _ _ => one_ne_zero, fun s m => by simp [h m s]⟩

/-- Term rescalings are equivalences. -/
theorem equivalent_rescale (d : Decomposition k SquareVertex SquareSummand)
    (l m' : SquareSummand → kˣ) : Equivalent (d.rescale l m').coordinates d.coordinates := by
  choose c h using fun m => modeMat_rescale_smul d l m' m
  exact ⟨Equiv.refl _, id, false, fun _ => 1, fun _ => 1, fun s m => ((c m s : kˣ) : k),
    fun _ => ⟨isUnit_one, isUnit_one⟩, fun s m => (c m s).ne_zero, fun s m => by simp [h m s]⟩

/-! ### Ranks under equivalences -/

theorem rank_smul_mul {β : Type} [Fintype β] [DecidableEq β] (c : k) (hc : c ≠ 0)
    (L X R : Matrix β β k) (hL : IsUnit L) (hR : IsUnit R) :
    (c • (L * X * R)).rank = X.rank := by
  rw [show c • (L * X * R) = (c • L) * X * R by rw [Matrix.smul_mul, Matrix.smul_mul]]
  have hcL : IsUnit (c • L) := (isUnit_iff_ne_zero.mpr hc).smul hL
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hR),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hcL)]

theorem fromRows_smul_mul {β : Type} [Fintype β] [DecidableEq β] (c₁ c₂ : k)
    (L X Y R : Matrix β β k) :
    Matrix.fromRows (c₁ • (L * X * R)) (c₂ • (L * Y * R)) =
      Matrix.fromBlocks (c₁ • L) 0 0 (c₂ • L) * Matrix.fromRows X Y * R := by
  rw [Matrix.mul_assoc, ← Matrix.fromRows_mul]
  ext i j
  cases i <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.smul_mul, Matrix.mul_assoc]

theorem fromCols_smul_mul {β : Type} [Fintype β] [DecidableEq β] (c₁ c₂ : k)
    (L X Y R : Matrix β β k) :
    Matrix.fromCols (c₁ • (L * X * R)) (c₂ • (L * Y * R)) =
      L * Matrix.fromCols X Y * Matrix.fromBlocks (c₁ • R) 0 0 (c₂ • R) := by
  rw [← Matrix.mul_fromCols]
  ext i j
  cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.mul_smul, Matrix.mul_assoc]

theorem isUnit_fromBlocks_diag {β : Type} [Fintype β] [DecidableEq β] (A D : Matrix β β k)
    (hA : IsUnit A) (hD : IsUnit D) : IsUnit (Matrix.fromBlocks A 0 0 D) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).mul ((Matrix.isUnit_iff_isUnit_det _).mp hD)

theorem rank_fromRows_equiv {β : Type} [Fintype β] [DecidableEq β] (c₁ c₂ : k) (h₁ : c₁ ≠ 0)
    (h₂ : c₂ ≠ 0) (L X Y R : Matrix β β k) (hL : IsUnit L) (hR : IsUnit R) :
    (Matrix.fromRows (c₁ • (L * X * R)) (c₂ • (L * Y * R))).rank =
      (Matrix.fromRows X Y).rank := by
  rw [fromRows_smul_mul,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hR),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_fromBlocks_diag _ _ ((isUnit_iff_ne_zero.mpr h₁).smul hL)
        ((isUnit_iff_ne_zero.mpr h₂).smul hL)))]

theorem rank_fromCols_equiv {β : Type} [Fintype β] [DecidableEq β] (c₁ c₂ : k) (h₁ : c₁ ≠ 0)
    (h₂ : c₂ ≠ 0) (L X Y R : Matrix β β k) (hL : IsUnit L) (hR : IsUnit R) :
    (Matrix.fromCols (c₁ • (L * X * R)) (c₂ • (L * Y * R))).rank =
      (Matrix.fromCols X Y).rank := by
  rw [fromCols_smul_mul,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_fromBlocks_diag _ _ ((isUnit_iff_ne_zero.mpr h₁).smul hR)
        ((isUnit_iff_ne_zero.mpr h₂).smul hR))),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hL)]

theorem fromRows_transpose' {β : Type} (X Y : Matrix β β k) :
    Matrix.fromRows X.transpose Y.transpose = (Matrix.fromCols X Y).transpose := by
  ext i j
  cases i <;> rfl

theorem fromCols_transpose' {β : Type} (X Y : Matrix β β k) :
    Matrix.fromCols X.transpose Y.transpose = (Matrix.fromRows X Y).transpose := by
  ext i j
  cases j <;> rfl

/-! ### Shapes -/

/-- `v` has the family's rank budgets and stacking conditions after relabelling by `σ`. -/
def Shape (v : Var → k) (σ : SquareSummand ≃ SquareSummand) (left : Bool) : Prop :=
  (∀ s m, (modeMat v (σ s) m).rank ≤ budget s.1 * budget s.2) ∧
    ∀ t, InGroup left t → StackOK v (σ t) (σ (anchor left t))

theorem isClosed_shape (σ : SquareSummand ≃ SquareSummand) (left : Bool) :
    IsClosed {v : Affine k | Shape v σ left} := by
  have h : {v : Affine k | Shape v σ left} =
      (⋂ s : SquareSummand, ⋂ m : Mode,
        {v : Affine k | ((modeX (σ s) m).map (eval v)).rank ≤ budget s.1 * budget s.2}) ∩
      ⋂ t : SquareSummand, ⋂ (_ : InGroup left t), {v : Affine k | StackOK v (σ t) (σ (anchor left t))} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Shape, modeX_eval]
  rw [h]
  exact (isClosed_iInter fun s => isClosed_iInter fun m => isClosed_rank_le _ _).inter
    (isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_stackOK _ _)

theorem shape_family (pq : FamilyParameters k) (left : Bool) :
    Shape (pq.value left).coordinates (Equiv.refl _) left :=
  ⟨fun s m => rank_value_le pq left s.1 s.2 m, fun t ht => family_stackOK pq left t ht⟩

/-- **Shapes pass to equivalent points.** -/
theorem shape_of_equivalent {v' v : Var → k} (h : Equivalent v' v)
    {σ : SquareSummand ≃ SquareSummand} {left : Bool} (hv : Shape v σ left) :
    ∃ σ' : SquareSummand ≃ SquareSummand, Shape v' σ' left := by
  obtain ⟨τ, π, tr, L, R, c, hLR, hc, hM⟩ := h
  refine ⟨σ.trans τ.symm, ?_, ?_⟩
  · intro s m
    rw [Equiv.trans_apply, hM, rank_smul_mul _ (hc _ _) _ _ _ (hLR m).1 (hLR m).2,
      Equiv.apply_symm_apply]
    cases tr
    · simp only [Bool.false_eq_true, if_false]
      exact hv.1 s (π m)
    · simp only [if_true]
      rw [Matrix.rank_transpose]
      exact hv.1 s (π m)
  · intro t ht m
    obtain ⟨h1, h2⟩ := hv.2 t ht (π m)
    simp only [Equiv.trans_apply, hM, Equiv.apply_symm_apply]
    rw [rank_fromRows_equiv _ _ (hc _ _) (hc _ _) _ _ _ _ (hLR m).1 (hLR m).2,
      rank_fromCols_equiv _ _ (hc _ _) (hc _ _) _ _ _ _ (hLR m).1 (hLR m).2]
    cases tr
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨h1, h2⟩
    · simp only [if_true]
      rw [fromRows_transpose', fromCols_transpose', Matrix.rank_transpose, Matrix.rank_transpose]
      exact ⟨h2, h1⟩

/-! ### The families closed under all equivalences -/

/-- All points equivalent to a point of either family. -/
def eqClosed (k : Type) [Field k] : Set (Affine k) :=
  {v' | ∃ left : Bool, ∃ v ∈ imageA k left, Equivalent v' v}

theorem eqClosed_subset :
    eqClosed k ⊆ ⋃ σ : SquareSummand ≃ SquareSummand, ⋃ left : Bool,
      {v : Affine k | Shape v σ left} := by
  rintro v' ⟨left, _, ⟨pq, rfl⟩, hv⟩
  obtain ⟨σ', h⟩ := shape_of_equivalent hv (shape_family pq left)
  exact Set.mem_iUnion.mpr ⟨σ', Set.mem_iUnion.mpr ⟨left, h⟩⟩

theorem familyClosure_subset_eqClosed (left : Bool) :
    familyClosure k left ⊆ closure (eqClosed k) := by
  unfold familyClosure
  apply closure_mono
  rintro _ ⟨pq, rfl⟩
  exact ⟨left, _, ⟨pq, rfl⟩, equivalent_refl _⟩

/-- **The closure of the equivalence-closed families has, at every point, some shape.** -/
theorem closure_eqClosed_subset :
    closure (eqClosed k) ⊆ ⋃ σ : SquareSummand ≃ SquareSummand, ⋃ left : Bool,
      {v : Affine k | Shape v σ left} :=
  closure_minimal eqClosed_subset
    (isClosed_iUnion_of_finite fun σ => isClosed_iUnion_of_finite fun left => isClosed_shape σ left)

/-! ### The anchor test at full-profile points with a shape -/

theorem anchorTest_of_shape (p : Fin 14236) (σ : SquareSummand ≃ SquareSummand) (left : Bool)
    (h : Shape (catPoint k p) σ left) (hp : profile k p = fullProfile) : AnchorTest k p := by
  classical
  -- exact ranks
  have hle : ∀ s m, rk k p (sE (σ s)) (mE m) ≤ budget s.1 * budget s.2 := fun s m => by
    rw [← rank_modeMat_catPoint]; exact h.1 s m
  have hsum : ∑ s : SquareSummand, ∑ m : Mode, rk k p (sE (σ s)) (mE m) = 192 := by
    rw [Equiv.sum_comp σ (fun s => ∑ m : Mode, rk k p (sE s) (mE m))]
    exact sum_rk_of_profile p hp
  have hr : ∀ s m, rk k p (sE (σ s)) (mE m) = budget s.1 * budget s.2 := by
    intro s m
    have hle' : ∀ s ∈ (Finset.univ : Finset SquareSummand),
        ∑ m : Mode, rk k p (sE (σ s)) (mE m) ≤ ∑ _m : Mode, budget s.1 * budget s.2 :=
      fun s _ => Finset.sum_le_sum fun m _ => hle s m
    have heq := (Finset.sum_eq_sum_iff_of_le hle').mp (hsum.trans sum_budget.symm) s
      (Finset.mem_univ _)
    exact (Finset.sum_eq_sum_iff_of_le fun m _ => hle s m).mp heq m (Finset.mem_univ _)
  have hM : ∀ s m, (modeMat (catPoint k p) (σ s) m).rank = budget s.1 * budget s.2 :=
    fun s m => by rw [rank_modeMat_catPoint, hr]
  have hcan : ∀ t : SquareSummand, t.1 ≠ 0 ∧ t.2 ≠ 0 →
      CanAnchor k p (sE (σ t)) (sE (σ (anchor left t))) := by
    intro t ht
    have hst := h.2 t (inGroup_of_one left t ht)
    have ha : ∀ m, (modeMat (catPoint k p) (σ (anchor left t)) m).rank = 2 := fun m => by
      rw [hM, budget_anchor left t (inGroup_of_one left t ht)]
    apply canAnchor_of_stack
    intro m
    obtain ⟨h1, h2⟩ := hst m
    refine ⟨le_antisymm ((ha m).symm ▸ h1) (rank_le_fromRows _ _), ?_⟩
    refine le_antisymm ((ha m).symm ▸ h2) ?_
    rw [← Matrix.rank_transpose (Matrix.fromCols _ _), ← fromRows_transpose',
      ← Matrix.rank_transpose (modeMat _ _ _)]
    exact rank_le_fromRows _ _
  have hone : ∀ s : SquareSummand, sE (σ s) ∈ rankOne k p ↔ s.1 ≠ 0 ∧ s.2 ≠ 0 := by
    intro s
    simp only [rankOne, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← budget_eq_one_iff]
    constructor
    · intro hs
      have := hs (mE .u)
      rwa [hr] at this
    · intro hs mi
      rw [← mE.apply_symm_apply mi, hr, hs]
  have htwo : ∀ i : Fin 7, i ≠ 0 → sE (σ (anchorOf left i)) ∈ rankTwo k p := by
    intro i hi
    simp only [rankTwo, Finset.mem_filter, Finset.mem_univ, true_and]
    intro mi
    rw [← mE.apply_symm_apply mi, hr, anchorOf_budget left i hi]
  have huseful : ∀ i : Fin 7, i ≠ 0 → Useful k p (sE (σ (anchorOf left i))) := by
    intro i hi
    refine ⟨htwo i hi, ?_⟩
    have hsub : ((Finset.univ.filter fun j : Fin 7 => j ≠ 0).map
        ((childOf_injective left i).embedding.trans (σ.toEmbedding.trans sE.toEmbedding))) ⊆
        children k p (sE (σ (anchorOf left i))) := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨j, hj, rfl⟩ := hn
      rw [Finset.mem_filter] at hj
      simp only [Function.Embedding.trans_apply, Function.Injective.embedding_apply,
        Equiv.toEmbedding_apply]
      rw [children, Finset.mem_filter]
      have hc := childOf_ne left i j hi hj.2
      refine ⟨(hone _).2 hc, ?_⟩
      have := hcan (childOf left i j) hc
      rwa [anchor_childOf] at this
    have := Finset.card_le_card hsub
    rwa [Finset.card_map, card_nonzero] at this
  refine ⟨?_, ?_⟩
  · have hsub : ((Finset.univ.filter fun i : Fin 7 => i ≠ 0).map
        ((anchorOf_injective left).embedding.trans (σ.toEmbedding.trans sE.toEmbedding))) ⊆
        (rankTwo k p).filter (Useful k p) := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨i, hi, rfl⟩ := hn
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨htwo i hi.2, huseful i hi.2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_map, card_nonzero] at this
  · intro n hn
    obtain ⟨t, rfl⟩ := (σ.trans sE).surjective n
    simp only [Equiv.trans_apply] at hn ⊢
    have ht := (hone t).1 hn
    refine ⟨sE (σ (anchor left t)), ?_, hcan t ht⟩
    rw [anchor_of_one left t ht]
    apply huseful
    cases left
    · exact ht.2
    · exact ht.1

/-- **F18e.** Over every field of characteristic three or zero, the catalogue entries 2445 and
5969 lie outside the closure of the families closed under all equivalences. -/
theorem anchor_excluded_eqClosed (hk : CharP k 3 ∨ CharZero k) (p : Fin 14236)
    (hp : p = 2445 ∨ p = 5969) : catPoint k p ∉ closure (eqClosed k) := by
  intro h
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp (closure_eqClosed_subset h)
  obtain ⟨left, hshape⟩ := Set.mem_iUnion.mp hσ
  have hf := facts_allFields k hk
  have hn : p.val ∈ neg2 := (mem_neg2 p).2 hp
  have hb : p.val ∉ bad87 := by
    rcases hp with rfl | rfl
    · exact neg2_not_bad.1
    · exact neg2_not_bad.2
  exact hf.2.2.2 p hn (anchorTest_of_shape p σ left hshape ((hf.1 p).2 hb))

end Brent.Census
