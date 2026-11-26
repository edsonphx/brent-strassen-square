import Mathlib.Data.Matrix.ColumnRowPartitioned
import Brent.Census.RankBound
import Brent.Census.Minors

/-!
# §7: the anchor structure persists on the family closures (F18, part 4)

DRAFT, NOT YET COMPILED.

Paper, lines 676–688: "At each of the six rank-one outer summands, the group of seven terms
contains a unique rank-two term, obtained by taking the inner identity summand. In each mode, its
row and column spaces contain the row and column spaces of all six other terms in that group …
Left and right changes preserve the inclusions. They persist at closure points with the same
profile because the relevant minors of the stacked matrices vanish. Indeed, equality of the total
rank sum in the two profiles forces equality at every label, since each rank is individually
bounded above by its original value. In particular each anchor stays of rank two. The other
recursive orientation gives the same condition with the index roles exchanged."

Formalization.

* `anchor left s` is the anchor of summand `s = (i, j)`: `(i, 0)` for the left orientation
  (groups by the outer index `i`) and `(0, j)` for the right one. `InGroup left s` says
  `s` belongs to a rank-one outer group (`i ≠ 0`, resp. `j ≠ 0`).
* `StackOK v t a`: in every mode, stacking the mode matrix of `t` on that of `a` (by rows and
  by columns) gives rank at most two. It is Zariski closed (`isClosed_stackOK`, via
  `Minors.rank_le_iff_minors`).
* On the family image the child is `Z · anchor` and `anchor · Z'` (`family_rel_row`,
  `family_rel_col`): the Strassen summand `0` is the identity, so the child
  `Sᵢ ⊗ (L Sⱼ R)` equals `(1 ⊗ L Sⱼ L⁻¹)(Sᵢ ⊗ L R)` and `(Sᵢ ⊗ L R)(1 ⊗ R⁻¹ Sⱼ R)`; changes of
  basis and rescalings preserve both relations. With `rank anchor ≤ 2` this gives `StackOK`
  on the image, hence on the closure (`closure_stackOK`). The rank budgets `≤ cᵢ cⱼ` also hold on
  the closure (`closure_rank_le`).
* At a closure point where the anchor has rank exactly two, `StackOK` gives the span
  containments (`rowSpan_le_of_stack`, `colSpan_le_of_stack`).
-/

open MvPolynomial
open scoped BigOperators Kronecker

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure

variable {k : Type} [Field k]

/-! ### Closed rank conditions -/

/-- The mode matrix with polynomial entries (the coordinate functions). -/
noncomputable def modeX (s : SquareSummand) (m : Mode) :
    Matrix SquareVertex SquareVertex (MvPolynomial Var k) :=
  modeMat (X : Var → MvPolynomial Var k) s m

theorem modeX_eval (v : Affine k) (s : SquareSummand) (m : Mode) :
    (modeX s m).map (eval v) = modeMat v s m := by
  ext a b
  simp [modeX, modeMat]

theorem fromRows_map' {β γ δ : Type*} {R S : Type*} (A : Matrix β δ R) (B : Matrix γ δ R)
    (f : R → S) : (Matrix.fromRows A B).map f = Matrix.fromRows (A.map f) (B.map f) := by
  ext i j
  cases i <;> rfl

theorem fromCols_map' {β γ δ : Type*} {R S : Type*} (A : Matrix β γ R) (B : Matrix β δ R)
    (f : R → S) : (Matrix.fromCols A B).map f = Matrix.fromCols (A.map f) (B.map f) := by
  ext i j
  cases j <;> rfl

/-- **"Rank at most `r`" is Zariski closed** for a matrix of polynomials. -/
theorem isClosed_rank_le {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq γ]
    (P : Matrix β γ (MvPolynomial Var k)) (r : ℕ) :
    IsClosed {v : Affine k | (P.map (eval v)).rank ≤ r} := by
  have h : {v : Affine k | (P.map (eval v)).rank ≤ r} =
      zeroLocus k {q | ∃ (f : Fin (r + 1) → β) (g : Fin (r + 1) → γ), q = (P.submatrix f g).det} := by
    ext v
    change _ ↔ ∀ q ∈ {q | ∃ (f : Fin (r + 1) → β) (g : Fin (r + 1) → γ),
      q = (P.submatrix f g).det}, eval v q = 0
    rw [Set.mem_setOf_eq, Minors.rank_le_iff_minors]
    constructor
    · rintro h q ⟨f, g, rfl⟩
      rw [RingHom.map_det]
      exact h f g
    · intro h f g
      have := h _ ⟨f, g, rfl⟩
      rwa [RingHom.map_det] at this
  rw [h]
  exact isClosed_zeroLocus k _

/-- Stacking condition: in every mode, the mode matrices of `t` and `a`, stacked by rows and
by columns, have rank at most two. -/
def StackOK (v : Var → k) (t a : SquareSummand) : Prop :=
  ∀ m, (Matrix.fromRows (modeMat v t m) (modeMat v a m)).rank ≤ 2 ∧
    (Matrix.fromCols (modeMat v t m) (modeMat v a m)).rank ≤ 2

theorem isClosed_stackOK (t a : SquareSummand) : IsClosed {v : Affine k | StackOK v t a} := by
  have h : {v : Affine k | StackOK v t a} = ⋂ m : Mode,
      ({v : Affine k | ((Matrix.fromRows (modeX t m) (modeX a m)).map (eval v)).rank ≤ 2} ∩
        {v : Affine k | ((Matrix.fromCols (modeX t m) (modeX a m)).map (eval v)).rank ≤ 2}) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, StackOK, fromRows_map',
      fromCols_map', modeX_eval]
  rw [h]
  exact isClosed_iInter fun m => (isClosed_rank_le _ 2).inter (isClosed_rank_le _ 2)

/-- The rank budgets of the families. -/
def BudgetOK (v : Var → k) : Prop :=
  ∀ s : SquareSummand, ∀ m, (modeMat v s m).rank ≤ budget s.1 * budget s.2

theorem isClosed_budgetOK : IsClosed {v : Affine k | BudgetOK v} := by
  have h : {v : Affine k | BudgetOK v} = ⋂ s : SquareSummand, ⋂ m : Mode,
      {v : Affine k | ((modeX s m).map (eval v)).rank ≤ budget s.1 * budget s.2} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iInter, BudgetOK, modeX_eval]
  rw [h]
  exact isClosed_iInter fun s => isClosed_iInter fun m => isClosed_rank_le _ _

/-! ### Stacked ranks from factorizations -/

theorem rank_fromRows_le {β : Type} [Fintype β] [DecidableEq β] (A B Z : Matrix β β k)
    (h : A = Z * B) : (Matrix.fromRows A B).rank ≤ B.rank := by
  have e : Matrix.fromRows A B = Matrix.fromRows Z 1 * B := by
    rw [Matrix.fromRows_mul, Matrix.one_mul, h]
  rw [e]
  exact Matrix.rank_mul_le_right _ _

theorem rank_fromCols_le {β : Type} [Fintype β] [DecidableEq β] (A B Z : Matrix β β k)
    (h : A = B * Z) : (Matrix.fromCols A B).rank ≤ B.rank := by
  have e : Matrix.fromCols A B = B * Matrix.fromCols Z 1 := by
    rw [Matrix.mul_fromCols, Matrix.mul_one, h]
  rw [e]
  exact Matrix.rank_mul_le_left _ _

/-! ### The relations on the families -/

/-- Strassen's summand `0` is the identity in every mode. -/
theorem strassen_zero : ∀ m : Mode, ∀ a b : Fin 2,
    strassen.coordinates (0, m, (a, b)) = if a = b then 1 else 0 := by
  decide

theorem sMat_zero (m : Mode) : sMat k 0 m = 1 := by
  ext a b
  simp only [sMat, Matrix.map_apply, modeMat, strassen_zero, Matrix.one_apply]
  split_ifs <;> simp

theorem isUnit_transpose' {β : Type} [Fintype β] [DecidableEq β] {A : Matrix β β k}
    (h : IsUnit A) : IsUnit A.transpose :=
  (Matrix.isUnit_transpose A).mpr h

theorem modeMat_leftFamily_units (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) (i : Fin 7)
    (m : Mode) : ∃ L R : Matrix (Fin 2) (Fin 2) k, IsUnit L ∧ IsUnit R ∧ ∀ j,
      modeMat (leftFamily P Q T).coordinates (i, j) m = sMat k i m ⊗ₖ (L * sMat k j m * R) := by
  cases m
  · exact ⟨(P i).val.transpose, (Q i).inv.transpose, isUnit_transpose' (P i).isUnit,
      isUnit_transpose' (Q i)⁻¹.isUnit, fun j => rfl⟩
  · exact ⟨(Q i).val.transpose, (T i).inv.transpose, isUnit_transpose' (Q i).isUnit,
      isUnit_transpose' (T i)⁻¹.isUnit, fun j => rfl⟩
  · exact ⟨(P i).inv, (T i).val, (P i)⁻¹.isUnit, (T i).isUnit, fun j => rfl⟩

theorem modeMat_rightFamily_units (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) (j : Fin 7)
    (m : Mode) : ∃ L R : Matrix (Fin 2) (Fin 2) k, IsUnit L ∧ IsUnit R ∧ ∀ i,
      modeMat (rightFamily P Q T).coordinates (i, j) m = (L * sMat k i m * R) ⊗ₖ sMat k j m := by
  cases m
  · exact ⟨(P j).val.transpose, (Q j).inv.transpose, isUnit_transpose' (P j).isUnit,
      isUnit_transpose' (Q j)⁻¹.isUnit, fun i => rfl⟩
  · exact ⟨(Q j).val.transpose, (T j).inv.transpose, isUnit_transpose' (Q j).isUnit,
      isUnit_transpose' (T j)⁻¹.isUnit, fun i => rfl⟩
  · exact ⟨(P j).inv, (T j).val, (P j)⁻¹.isUnit, (T j).isUnit, fun i => rfl⟩

/-- The anchor of a summand. -/
def anchor (left : Bool) (s : SquareSummand) : SquareSummand :=
  if left then (s.1, 0) else (0, s.2)

/-- `s` lies in a rank-one outer group. -/
def InGroup (left : Bool) (s : SquareSummand) : Prop :=
  if left then s.1 ≠ 0 else s.2 ≠ 0

/-- Row relation `M t = Z · M a`. -/
def RowRel (v : Var → k) (t a : SquareSummand) (m : Mode) : Prop :=
  ∃ Z, modeMat v t m = Z * modeMat v a m

/-- Column relation `M t = M a · Z`. -/
def ColRel (v : Var → k) (t a : SquareSummand) (m : Mode) : Prop :=
  ∃ Z, modeMat v t m = modeMat v a m * Z

theorem base_rel_left (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) (t : SquareSummand)
    (m : Mode) :
    RowRel (leftFamily P Q T).coordinates t (anchor true t) m ∧
      ColRel (leftFamily P Q T).coordinates t (anchor true t) m := by
  obtain ⟨i, j⟩ := t
  obtain ⟨L, R, ⟨uL, rfl⟩, ⟨uR, rfl⟩, h⟩ := modeMat_leftFamily_units P Q T i m
  simp only [anchor, if_true]
  refine ⟨⟨1 ⊗ₖ (uL.val * sMat k j m * (uL⁻¹).val), ?_⟩, ⟨1 ⊗ₖ ((uR⁻¹).val * sMat k j m * uR.val), ?_⟩⟩
  · rw [h j, h 0, sMat_zero, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul_cancel_left]
  · rw [h j, h 0, sMat_zero, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem base_rel_right (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) (t : SquareSummand)
    (m : Mode) :
    RowRel (rightFamily P Q T).coordinates t (anchor false t) m ∧
      ColRel (rightFamily P Q T).coordinates t (anchor false t) m := by
  obtain ⟨i, j⟩ := t
  obtain ⟨L, R, ⟨uL, rfl⟩, ⟨uR, rfl⟩, h⟩ := modeMat_rightFamily_units P Q T j m
  simp only [anchor, Bool.false_eq_true, if_false]
  refine ⟨⟨(uL.val * sMat k i m * (uL⁻¹).val) ⊗ₖ 1, ?_⟩, ⟨((uR⁻¹).val * sMat k i m * uR.val) ⊗ₖ 1, ?_⟩⟩
  · rw [h i, h 0, sMat_zero, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul_cancel_left]
  · rw [h i, h 0, sMat_zero, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, Units.mul_inv_cancel_left]

/-- Changes of basis act on every summand by the same invertible `L`, `R`. -/
theorem modeMat_changeBasis_units {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition k α ι) (P Q T : (Matrix α α k)ˣ) (m : Mode) :
    ∃ L R : Matrix α α k, IsUnit L ∧ IsUnit R ∧ ∀ s,
      modeMat (d.changeBasis P Q T).coordinates s m = L * modeMat d.coordinates s m * R := by
  cases m
  · exact ⟨P.val.transpose, Q.inv.transpose, (Matrix.isUnit_transpose _).mpr P.isUnit,
      (Matrix.isUnit_transpose _).mpr Q⁻¹.isUnit, fun s => rfl⟩
  · exact ⟨Q.val.transpose, T.inv.transpose, (Matrix.isUnit_transpose _).mpr Q.isUnit,
      (Matrix.isUnit_transpose _).mpr T⁻¹.isUnit, fun s => rfl⟩
  · exact ⟨P.inv, T.val, P⁻¹.isUnit, T.isUnit, fun s => rfl⟩

/-- Rescalings multiply each summand by a nonzero scalar. -/
theorem modeMat_rescale_smul {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition k α ι) (l m' : ι → kˣ) (m : Mode) :
    ∃ c : ι → kˣ, ∀ s,
      modeMat (d.rescale l m').coordinates s m = ((c s : kˣ) : k) • modeMat d.coordinates s m := by
  cases m
  · exact ⟨l, fun s => by ext a b; simp only [Matrix.smul_apply, smul_eq_mul]; rfl⟩
  · exact ⟨m', fun s => by ext a b; simp only [Matrix.smul_apply, smul_eq_mul]; rfl⟩
  · exact ⟨fun s => (l s)⁻¹ * (m' s)⁻¹, fun s => by
      ext a b; simp only [Matrix.smul_apply, smul_eq_mul, Units.val_mul]; rfl⟩

theorem rowRel_changeBasis {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition k α ι) (P Q T : (Matrix α α k)ˣ) {t a : ι} {m : Mode}
    (h : ∃ Z, modeMat d.coordinates t m = Z * modeMat d.coordinates a m) :
    ∃ Z, modeMat (d.changeBasis P Q T).coordinates t m =
      Z * modeMat (d.changeBasis P Q T).coordinates a m := by
  obtain ⟨L, R, ⟨uL, rfl⟩, -, hs⟩ := modeMat_changeBasis_units d P Q T m
  obtain ⟨Z, hZ⟩ := h
  refine ⟨uL.val * Z * (uL⁻¹).val, ?_⟩
  rw [hs t, hs a, hZ]
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

theorem colRel_changeBasis {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition k α ι) (P Q T : (Matrix α α k)ˣ) {t a : ι} {m : Mode}
    (h : ∃ Z, modeMat d.coordinates t m = modeMat d.coordinates a m * Z) :
    ∃ Z, modeMat (d.changeBasis P Q T).coordinates t m =
      modeMat (d.changeBasis P Q T).coordinates a m * Z := by
  obtain ⟨L, R, -, ⟨uR, rfl⟩, hs⟩ := modeMat_changeBasis_units d P Q T m
  obtain ⟨Z, hZ⟩ := h
  refine ⟨(uR⁻¹).val * Z * uR.val, ?_⟩
  rw [hs t, hs a, hZ]
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem rowRel_rescale {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition k α ι) (l m' : ι → kˣ) {t a : ι} {m : Mode}
    (h : ∃ Z, modeMat d.coordinates t m = Z * modeMat d.coordinates a m) :
    ∃ Z, modeMat (d.rescale l m').coordinates t m =
      Z * modeMat (d.rescale l m').coordinates a m := by
  obtain ⟨c, hc⟩ := modeMat_rescale_smul d l m' m
  obtain ⟨Z, hZ⟩ := h
  refine ⟨((c t).val * (c a).inv) • Z, ?_⟩
  have hscalar : (c t).val * (c a).inv * (c a).val = (c t).val := by
    rw [mul_assoc, (c a).inv_val, mul_one]
  have hscalar' : (c a).val * ((c t).val * (c a).inv) = (c t).val := by
    rw [mul_comm (c a).val, hscalar]
  simp only [hc t, hc a, hZ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hscalar']

theorem colRel_rescale {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition k α ι) (l m' : ι → kˣ) {t a : ι} {m : Mode}
    (h : ∃ Z, modeMat d.coordinates t m = modeMat d.coordinates a m * Z) :
    ∃ Z, modeMat (d.rescale l m').coordinates t m =
      modeMat (d.rescale l m').coordinates a m * Z := by
  obtain ⟨c, hc⟩ := modeMat_rescale_smul d l m' m
  obtain ⟨Z, hZ⟩ := h
  refine ⟨((c t).val * (c a).inv) • Z, ?_⟩
  have hscalar : (c t).val * (c a).inv * (c a).val = (c t).val := by
    rw [mul_assoc, (c a).inv_val, mul_one]
  have hscalar' : (c a).val * ((c t).val * (c a).inv) = (c t).val := by
    rw [mul_comm (c a).val, hscalar]
  simp only [hc t, hc a, hZ, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hscalar, hscalar']

/-- **The relations on every family point.** -/
theorem family_rel (pq : FamilyParameters k) (left : Bool) (t : SquareSummand) (m : Mode) :
    RowRel (pq.value left).coordinates t (anchor left t) m ∧
      ColRel (pq.value left).coordinates t (anchor left t) m := by
  cases left
  · have hb := base_rel_right (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2) t m
    exact ⟨rowRel_rescale _ _ _ (rowRel_changeBasis _ _ _ _ hb.1),
      colRel_rescale _ _ _ (colRel_changeBasis _ _ _ _ hb.2)⟩
  · have hb := base_rel_left (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2) t m
    exact ⟨rowRel_rescale _ _ _ (rowRel_changeBasis _ _ _ _ hb.1),
      colRel_rescale _ _ _ (colRel_changeBasis _ _ _ _ hb.2)⟩

theorem budget_anchor (left : Bool) (t : SquareSummand) (ht : InGroup left t) :
    budget (anchor left t).1 * budget (anchor left t).2 = 2 := by
  obtain ⟨i, j⟩ := t
  cases left <;> simp only [anchor, InGroup, if_true, if_false, Bool.false_eq_true] at ht ⊢ <;>
    simp [budget, ht]

theorem family_stackOK (pq : FamilyParameters k) (left : Bool) (t : SquareSummand)
    (ht : InGroup left t) : StackOK (pq.value left).coordinates t (anchor left t) := by
  unfold StackOK
  intro m
  obtain ⟨⟨Z, hZ⟩, ⟨Z', hZ'⟩⟩ := family_rel pq left t m
  have hA : (modeMat (pq.value left).coordinates (anchor left t) m).rank ≤ 2 := by
    have := rank_value_le pq left (anchor left t).1 (anchor left t).2 m
    rwa [budget_anchor left t ht] at this
  exact ⟨(rank_fromRows_le _ _ _ hZ).trans hA, (rank_fromCols_le _ _ _ hZ').trans hA⟩

/-! ### On the closures -/

/-- The anchor stacking conditions hold on the whole family closure. -/
theorem closure_stackOK (left : Bool) (t : SquareSummand) (ht : InGroup left t) :
    familyClosure k left ⊆ {v : Affine k | StackOK v t (anchor left t)} := by
  unfold familyClosure
  refine closure_minimal ?_ (isClosed_stackOK _ _)
  rintro _ ⟨pq, rfl⟩
  exact family_stackOK pq left t ht

/-- The rank budgets hold on the whole family closure. -/
theorem closure_budgetOK (left : Bool) : familyClosure k left ⊆ {v : Affine k | BudgetOK v} := by
  unfold familyClosure
  refine closure_minimal ?_ isClosed_budgetOK
  rintro _ ⟨pq, rfl⟩ s m
  exact rank_value_le pq left s.1 s.2 m

/-! ### Span containment from the stacking condition -/

theorem rank_le_fromRows {β : Type} [Fintype β] [DecidableEq β] (A B : Matrix β β k) :
    B.rank ≤ (Matrix.fromRows A B).rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Sum.inr i, rfl⟩

/-- Rows of `A` lie in the row span of `B` when `B` has rank two and `[A; B]` rank at most two. -/
theorem rowSpan_le_of_stack {β : Type} [Fintype β] [DecidableEq β] (A B : Matrix β β k)
    (hB : B.rank = 2) (h : (Matrix.fromRows A B).rank ≤ 2) :
    Submodule.span k (Set.range A.row) ≤ Submodule.span k (Set.range B.row) := by
  have heq : (Matrix.fromRows A B).rank = B.rank := le_antisymm (by simpa only [hB] using h) (rank_le_fromRows A B)
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row] at heq
  have hsup : Submodule.span k (Set.range (Matrix.fromRows A B).row) =
      Submodule.span k (Set.range A.row) ⊔ Submodule.span k (Set.range B.row) := by
    rw [← Submodule.span_union]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_union, Sum.exists]
    exact Iff.rfl
  rw [hsup] at heq
  have hle : Submodule.span k (Set.range B.row) ≤
      Submodule.span k (Set.range A.row) ⊔ Submodule.span k (Set.range B.row) := le_sup_right
  have h2 := Submodule.eq_of_le_of_finrank_eq hle heq.symm
  rw [h2]
  exact le_sup_left

/-- Columns of `A` lie in the column span of `B` under the same hypotheses for `[A B]`. -/
theorem colSpan_le_of_stack {β : Type} [Fintype β] [DecidableEq β] (A B : Matrix β β k)
    (hB : B.rank = 2) (h : (Matrix.fromCols A B).rank ≤ 2) :
    Submodule.span k (Set.range A.transpose.row) ≤ Submodule.span k (Set.range B.transpose.row) := by
  apply rowSpan_le_of_stack
  · rw [Matrix.rank_transpose, hB]
  · rw [show Matrix.fromRows A.transpose B.transpose = (Matrix.fromCols A B).transpose by
      ext i j; cases i <;> rfl, Matrix.rank_transpose]
    exact h

end Brent.Census
