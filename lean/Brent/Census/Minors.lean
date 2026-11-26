import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card

/-!
# Rank and minors

DRAFT, NOT YET COMPILED.

Over a field, a matrix has rank at most `r` if and only if all its `(r + 1) × (r + 1)` minors
vanish. `RankBound.det_submatrix_eq_zero_of_rank_lt` is the easy direction; this file proves the
other one (`exists_minor_ne_zero`): if the rank is at least `n`, some `n × n` minor is nonzero.
This makes "rank at most `r`" a Zariski-closed condition on points whose coordinates are the
matrix entries, which the anchor persistence argument (`Census.AnchorClosure`) needs.
-/

namespace Brent.Census.Minors

variable {K : Type*} [Field K]

/-- From a family whose span has dimension at least `n`, pick `n` linearly independent members. -/
theorem exists_independent_subfamily {V ι : Type*} [AddCommGroup V] [Module K V]
    (v : ι → V) [Finite ι] {n : ℕ}
    (hn : n ≤ Module.finrank K (Submodule.span K (Set.range v))) :
    ∃ f : Fin n → ι, LinearIndependent K (v ∘ f) := by
  classical
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent K (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbsub
  letI : Fintype b := hbfin.fintype
  have hcard : Module.finrank K (Submodule.span K b) = Fintype.card b :=
    (finrank_span_set_eq_card hbind).trans (Set.toFinset_card b)
  rw [← hbspan, hcard] at hn
  obtain ⟨e⟩ : Nonempty (Fin n ↪ b) := Function.Embedding.nonempty_of_card_le (by simpa using hn)
  have hpre : ∀ x : b, ∃ i, v i = x := fun x => hbsub x.2
  choose g hg using hpre
  refine ⟨fun j => g (e j), ?_⟩
  have h : v ∘ (fun j => g (e j)) = ((↑) : b → V) ∘ e := by
    funext j
    exact hg (e j)
  rw [h]
  exact hbind.comp e e.injective

/-- **A matrix of rank at least `n` has a nonzero `n × n` minor.** -/
theorem exists_minor_ne_zero {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]
    (M : Matrix m p K) {n : ℕ} (hn : n ≤ M.rank) :
    ∃ (f : Fin n → m) (g : Fin n → p), (M.submatrix f g).det ≠ 0 := by
  classical
  -- `n` independent rows.
  rw [Matrix.rank_eq_finrank_span_row] at hn
  obtain ⟨f, hf⟩ := exists_independent_subfamily M.row hn
  -- The `n × p` matrix of these rows has rank `n`, so it has `n` independent columns.
  set N : Matrix (Fin n) p K := M.submatrix f id
  have hNrow : LinearIndependent K N.row := hf
  have hNrank : N.rank = n := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hNrow, Fintype.card_fin]
  have hcols : n ≤ Module.finrank K (Submodule.span K (Set.range N.col)) := by
    rw [← Matrix.rank_eq_finrank_span_cols, hNrank]
  obtain ⟨g, hg⟩ := exists_independent_subfamily N.col hcols
  refine ⟨f, g, ?_⟩
  have hS : LinearIndependent K (N.submatrix id g).col := hg
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hS
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

/-- A minor larger than the rank vanishes (the easy direction). -/
theorem det_submatrix_eq_zero {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]
    (M : Matrix m p K) {n : ℕ} (f : Fin n → m) (g : Fin n → p) (h : M.rank < n) :
    (M.submatrix f g).det = 0 := by
  by_contra hne
  have hu : IsUnit (M.submatrix f g) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hne)
  have h1 : (M.submatrix f g).rank = n := by rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
  have e : M.submatrix f g = (M.submatrix f id) * (1 : Matrix p p K).submatrix id g := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h2 : (M.submatrix f g).rank ≤ M.rank := by
    rw [e]
    refine (Matrix.rank_mul_le_left _ _).trans ?_
    exact Matrix.rank_submatrix_le f (Equiv.refl p) M
  omega

/-- **Rank at most `r` iff all `(r + 1)`-minors vanish.** -/
theorem rank_le_iff_minors {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]
    (M : Matrix m p K) (r : ℕ) :
    M.rank ≤ r ↔ ∀ (f : Fin (r + 1) → m) (g : Fin (r + 1) → p), (M.submatrix f g).det = 0 := by
  constructor
  · intro h f g
    exact det_submatrix_eq_zero M f g (by omega)
  · intro h
    by_contra hlt
    obtain ⟨f, g, hfg⟩ := exists_minor_ne_zero M (n := r + 1) (by omega)
    exact hfg (h f g)

end Brent.Census.Minors
