import Brent.Census.Equivalences

/-!
# §7, line 661: the exact rank profile of the families

DRAFT, NOT YET COMPILED.

Paper, lines 661–663: "Throughout either displayed family, the multiset of triples of ordinary
matrix ranks is `36(1,1,1), 12(2,2,2), 1(4,4,4)`."

`rank_value_le` gives `rank ≤ cᵢ cⱼ` for summand `(i, j)`. Here we prove equality, over every
field, at every point of either family (`rank_value_eq`), and deduce the multiset
(`family_profile`).

* Changes of basis and rescalings do not change ranks; the family mode matrix
  `Sᵢ ⊗ (L Sⱼ R)` (resp. `(L Sᵢ R) ⊗ Sⱼ`) equals `(1 ⊗ L)(Sᵢ ⊗ Sⱼ)(1 ⊗ R)` (resp.
  `(L ⊗ 1)(Sᵢ ⊗ Sⱼ)(R ⊗ 1)`), so its rank is `rank (Sᵢ ⊗ Sⱼ)` (`rank_family_mode`).
* `rank (Sᵢ ⊗ Sⱼ) = cᵢ cⱼ` (`rank_kron_eq`): the upper bound is `rank_kron_strassen`; the lower
  bound is an explicit nonzero minor. `pos i m` is an entry of the Strassen factor `Sᵢ` with
  square one (`pos_sq`, checked by `decide`). For `i, j ≠ 0` the `1 × 1` minor at
  `(pos i, pos j)` is `±1`; for `j = 0` (resp. `i = 0`) the `2 × 2` minor through `pos i`
  (resp. `pos j`) is `±1 · I₂`, of determinant one; `S₀ ⊗ S₀ = I₄`.
-/

open scoped BigOperators Kronecker

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure

variable {k : Type} [Field k]

/-! ### Rank invariance -/

theorem rank_LMR {β : Type} [Fintype β] [DecidableEq β] (L X R : Matrix β β k) (hL : IsUnit L)
    (hR : IsUnit R) : (L * X * R).rank = X.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hR),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hL)]

theorem isUnit_one_kron {L : Matrix (Fin 2) (Fin 2) k} (hL : IsUnit L) :
    IsUnit ((1 : Matrix (Fin 2) (Fin 2) k) ⊗ₖ L) := by
  obtain ⟨u, rfl⟩ := hL
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := (1 : Matrix (Fin 2) (Fin 2) k) ⊗ₖ ↑u⁻¹)
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Units.mul_inv, Matrix.one_kronecker_one]

theorem isUnit_kron_one {L : Matrix (Fin 2) (Fin 2) k} (hL : IsUnit L) :
    IsUnit (L ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) k)) := by
  obtain ⟨u, rfl⟩ := hL
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := ↑u⁻¹ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) k))
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Units.mul_inv, Matrix.one_kronecker_one]

theorem rank_family_mode (pq : FamilyParameters k) (left : Bool) (i j : Fin 7) (m : Mode) :
    (modeMat (pq.value left).coordinates (i, j) m).rank = (sMat k i m ⊗ₖ sMat k j m).rank := by
  -- rescaling
  obtain ⟨c, hc⟩ := modeMat_rescale_smul
    ((if left then leftFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2) else rightFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2)).changeBasis (pq.global 0) (pq.global 1) (pq.global 2))
    (fun s => pq.scale s 0) (fun s => pq.scale s 1) m
  -- change of basis
  obtain ⟨L₀, R₀, hL₀, hR₀, hb⟩ := modeMat_changeBasis_units
    (if left then leftFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2) else rightFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2)) (pq.global 0) (pq.global 1) (pq.global 2) m
  have hval : modeMat (pq.value left).coordinates (i, j) m =
      ((c (i, j) : kˣ) : k) • (L₀ * modeMat (if left then leftFamily (fun l => pq.block l 0)
        (fun l => pq.block l 1) (fun l => pq.block l 2) else rightFamily
        (fun l => pq.block l 0) (fun l => pq.block l 1) (fun l => pq.block l 2)).coordinates
        (i, j) m * R₀) := by
    rw [← hb, ← hc]
    cases left <;> rfl
  rw [hval, show ((c (i, j) : kˣ) : k) • (L₀ * modeMat _ (i, j) m * R₀) =
      (((c (i, j) : kˣ) : k) • L₀) * modeMat _ (i, j) m * R₀ by
    rw [Matrix.smul_mul, Matrix.smul_mul],
    rank_LMR _ _ _ ((c (i, j)).isUnit.smul hL₀) hR₀]
  cases left
  · obtain ⟨L, R, hL, hR, h⟩ := modeMat_rightFamily_units (fun l => pq.block l 0)
      (fun l => pq.block l 1) (fun l => pq.block l 2) j m
    simp only [Bool.false_eq_true, if_false]
    rw [h i, show (L * sMat k i m * R) ⊗ₖ sMat k j m =
        (L ⊗ₖ 1) * (sMat k i m ⊗ₖ sMat k j m) * (R ⊗ₖ 1) by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one],
      rank_LMR _ _ _ (isUnit_kron_one hL) (isUnit_kron_one hR)]
  · obtain ⟨L, R, hL, hR, h⟩ := modeMat_leftFamily_units (fun l => pq.block l 0)
      (fun l => pq.block l 1) (fun l => pq.block l 2) i m
    simp only [if_true]
    rw [h j, show sMat k i m ⊗ₖ (L * sMat k j m * R) =
        (1 ⊗ₖ L) * (sMat k i m ⊗ₖ sMat k j m) * (1 ⊗ₖ R) by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one],
      rank_LMR _ _ _ (isUnit_one_kron hL) (isUnit_one_kron hR)]

/-! ### Ranks of the Strassen Kronecker products -/

/-- An entry of the Strassen factor `Sᵢ` in mode `m` that is `±1` (for `i ≠ 0`). -/
def pos (i : Fin 7) (m : Mode) : Fin 2 × Fin 2 :=
  if strassen.coordinates (i, m, (0, 0)) ≠ 0 then (0, 0)
  else if strassen.coordinates (i, m, (0, 1)) ≠ 0 then (0, 1)
  else if strassen.coordinates (i, m, (1, 0)) ≠ 0 then (1, 0) else (1, 1)

theorem pos_sq : ∀ i : Fin 7, ∀ m : Mode, strassen.coordinates (i, m, pos i m) ^ 2 = 1 := by
  decide

theorem sMat_apply (i : Fin 7) (m : Mode) (a b : Fin 2) :
    sMat k i m a b = ((strassen.coordinates (i, m, (a, b)) : ℤ) : k) := rfl

theorem intCast_ne_zero_of_sq (x : ℤ) (h : x ^ 2 = 1) : (x : k) ≠ 0 := by
  intro h0
  have := congrArg (Int.cast : ℤ → k) h
  push_cast at this
  rw [h0] at this
  simp at this

theorem sMat_pos_ne_zero (i : Fin 7) (m : Mode) : sMat k i m (pos i m).1 (pos i m).2 ≠ 0 := by
  rw [sMat_apply]
  exact intCast_ne_zero_of_sq _ (pos_sq i m)

theorem le_rank_of_minor {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq γ] {n : ℕ}
    (M : Matrix β γ k) (f : Fin n → β) (g : Fin n → γ) (h : (M.submatrix f g).det ≠ 0) :
    n ≤ M.rank := by
  by_contra hlt
  exact h (Minors.det_submatrix_eq_zero M f g (by omega))

theorem rank_kron_le_budget (i j : Fin 7) (m : Mode) :
    (sMat k i m ⊗ₖ sMat k j m).rank ≤ budget i * budget j := by
  have := rank_kron_strassen (k := k) i j m 1 1
  rwa [Matrix.one_mul, Matrix.mul_one] at this

theorem budget_le_rank_kron (i j : Fin 7) (m : Mode) :
    budget i * budget j ≤ (sMat k i m ⊗ₖ sMat k j m).rank := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst hi hj
    rw [sMat_zero, Matrix.one_kronecker_one, Matrix.rank_one]
    decide
  · -- `i = 0`: the 2 × 2 minor through `pos j`.
    subst hi
    have hb : budget (0 : Fin 7) * budget j = 2 := by simp [budget, hj]
    rw [hb]
    apply le_rank_of_minor _ ![(0, (pos j m).1), (1, (pos j m).1)] ![(0, (pos j m).2), (1, (pos j m).2)]
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sMat_zero, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_mul, zero_mul, sub_zero]
    exact mul_ne_zero (sMat_pos_ne_zero j m) (sMat_pos_ne_zero j m)
  · -- `j = 0`: the 2 × 2 minor through `pos i`.
    subst hj
    have hb : budget i * budget (0 : Fin 7) = 2 := by simp [budget, hi]
    rw [hb]
    apply le_rank_of_minor _ ![((pos i m).1, 0), ((pos i m).1, 1)] ![((pos i m).2, 0), ((pos i m).2, 1)]
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sMat_zero, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero, sub_zero]
    exact mul_ne_zero (sMat_pos_ne_zero i m) (sMat_pos_ne_zero i m)
  · -- `i, j ≠ 0`: the 1 × 1 minor at `(pos i, pos j)`.
    have hb : budget i * budget j = 1 := by simp [budget, hi, hj]
    rw [hb]
    apply le_rank_of_minor _ ![((pos i m).1, (pos j m).1)] ![((pos i m).2, (pos j m).2)]
    rw [Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.cons_val_zero]
    exact mul_ne_zero (sMat_pos_ne_zero i m) (sMat_pos_ne_zero j m)

theorem rank_kron_eq (i j : Fin 7) (m : Mode) :
    (sMat k i m ⊗ₖ sMat k j m).rank = budget i * budget j :=
  le_antisymm (rank_kron_le_budget i j m) (budget_le_rank_kron i j m)

/-- **Exact ranks on the families**, over every field. -/
theorem rank_value_eq (pq : FamilyParameters k) (left : Bool) (i j : Fin 7) (m : Mode) :
    (modeMat (pq.value left).coordinates (i, j) m).rank = budget i * budget j := by
  rw [rank_family_mode, rank_kron_eq]

/-- The rank-triple multiset of a point. -/
noncomputable def rankProfile (v : Var → k) : Multiset (ℕ × ℕ × ℕ) :=
  (Finset.univ : Finset SquareSummand).val.map fun s =>
    ((modeMat v s .u).rank, (modeMat v s .v).rank, (modeMat v s .w).rank)

theorem budget_profile :
    ((Finset.univ : Finset SquareSummand).val.map fun s =>
      (budget s.1 * budget s.2, budget s.1 * budget s.2, budget s.1 * budget s.2)) =
      Catalogue.fullProfile := by
  decide

/-- **Line 661.** Throughout either family, the multiset of rank triples is
`36(1,1,1) + 12(2,2,2) + 1(4,4,4)`, over every field. -/
theorem family_profile (pq : FamilyParameters k) (left : Bool) :
    rankProfile (pq.value left).coordinates = Catalogue.fullProfile := by
  rw [← budget_profile, rankProfile]
  congr 1
  funext s
  obtain ⟨i, j⟩ := s
  simp only [rank_value_eq]


theorem budget_pos (i : Fin 7) : 0 < budget i := by
  unfold budget
  split <;> norm_num

/-- Lines 719–720: "The open parameterizations preserve every nonzero factor and retain all 49
summands." For every parameter value of either family, over every field, each of the three factor
matrices of each of the 49 summands is nonzero (so every summand is a nonzero rank-one tensor). -/
theorem family_factor_ne_zero (pq : FamilyParameters k) (left : Bool) (s : SquareSummand)
    (m : Mode) : modeMat (pq.value left).coordinates s m ≠ 0 := by
  obtain ⟨i, j⟩ := s
  intro h
  have hr := rank_value_eq pq left i j m
  rw [h, Matrix.rank_zero] at hr
  have := Nat.mul_pos (budget_pos i) (budget_pos j)
  omega

/-- In a rank-one outer group the inner identity is the unique rank-two term. -/
theorem unique_rankTwo_left (pq : FamilyParameters k) (i : Fin 7)
    (hi : i ≠ 0) (m : Mode) :
    ∃! j : Fin 7, (modeMat (pq.value true).coordinates (i, j) m).rank = 2 := by
  refine ⟨0, ?_, ?_⟩
  · rw [rank_value_eq]
    simp [budget, hi]
  · intro j hj
    rw [rank_value_eq] at hj
    by_contra hn
    simp [budget, hi, hn] at hj

/-- The same uniqueness in the other recursive orientation. -/
theorem unique_rankTwo_right (pq : FamilyParameters k) (j : Fin 7)
    (hj : j ≠ 0) (m : Mode) :
    ∃! i : Fin 7, (modeMat (pq.value false).coordinates (i, j) m).rank = 2 := by
  refine ⟨0, ?_, ?_⟩
  · rw [rank_value_eq]
    simp [budget, hj]
  · intro i hi
    rw [rank_value_eq] at hi
    by_contra hn
    simp [budget, hj, hn] at hi

end Brent.Census
