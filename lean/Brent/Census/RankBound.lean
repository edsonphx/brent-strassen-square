import Brent.Formal.FamilyClosure
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# §7 census: the rank bounds are closed and hold on the saturated families (F18, part 1)

Every point `v ∈ k^2352` has 147 mode matrices `modeMat v s m` (summand `s`, mode `m`), each a
`4 × 4` matrix indexed by `SquareVertex = Fin 2 × Fin 2`. The vertex `(r₁, r₂)` is the
zero-based row or column `2 r₁ + r₂`, as in `squareVariableNumber`.

**The rank bounds** (paper §7). At most 13 summands have a mode of rank `> 1`, and at most one
summand has a mode of rank `> 2`. `RankBound k` is the zero locus of the products

* `∏_{i < 14} μᵢ`, where `μᵢ` is a `2 × 2` minor of some mode of summand `sᵢ`, for 14 distinct
  summands `sᵢ`, and
* `μ · μ'`, where `μ, μ'` are `3 × 3` minors of two distinct summands.

So `RankBound k` is Zariski closed by definition (`isClosed_rankBound`).

**On the families.** For `pq` with orientation `left`, summand `(i, j)` of `pq.value left` has
every mode of rank at most `c i * c j`, where `c 0 = 2` and `c i = 1` otherwise
(`rank_value_le`). This is because the mode matrix is `L ⊗ₖ`-structured: a Kronecker product of
a Strassen factor and a changed Strassen factor, then multiplied on both sides and scaled. So
36 summands have rank `≤ 1` and all summands but `(0, 0)` have rank `≤ 2`
(`profileBound_family`), and `pq.value left ∈ RankBound k`.

**Saturation.** `Dominated v' v` means that after a permutation of summands, every mode matrix of
`v'` has rank at most that of some mode matrix of `v`. Every allowed equivalence (the
`GL₄³`-action, term scalings, summand permutations, cyclic mode permutations and the transpose
symmetry) acts on mode matrices by `M ↦ L M R` or `M ↦ L Mᵀ R`, possibly in another mode and
another summand (`dominated_of_formula`). So the saturation of the family image (everything
dominated by a family point) lies in `RankBound k`, and so does its Zariski closure:
`closure_saturation_subset_rankBound`. This holds over every field.

`Census.Witness` turns a nonvanishing minor certificate into `v ∉ RankBound k`.
-/

open MvPolynomial
open scoped BigOperators Kronecker

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure

/-! ### Mode matrices and minors -/

/-- The mode matrix of summand `s` in mode `m`: rows and columns are vertices. -/
def modeMat {R α ι : Type*} (v : Variable α ι → R) (s : ι) (m : Mode) : Matrix α α R :=
  fun a b => v (s, m, (a, b))

/-- A choice of `n × n` minor: mode, rows, columns. -/
abbrev MinorChoice (n : ℕ) := Mode × (Fin n → SquareVertex) × (Fin n → SquareVertex)

variable {k : Type} [Field k]

/-- The `n × n` minor polynomial of summand `s`. -/
noncomputable def minorPoly {n : ℕ} (s : SquareSummand) (c : MinorChoice n) : MvPolynomial Var k :=
  (Matrix.of fun i j => (X (s, c.1, (c.2.1 i, c.2.2 j)) : MvPolynomial Var k)).det

theorem eval_minorPoly {n : ℕ} (v : Var → k) (s : SquareSummand) (c : MinorChoice n) :
    eval v (minorPoly s c) = ((modeMat v s c.1).submatrix c.2.1 c.2.2).det := by
  rw [minorPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [modeMat]

/-- A minor of size larger than the rank vanishes. -/
theorem det_submatrix_eq_zero_of_rank_lt {n : ℕ} (M : Matrix SquareVertex SquareVertex k)
    (r c : Fin n → SquareVertex) (h : M.rank < n) : (M.submatrix r c).det = 0 := by
  by_contra hne
  have hu : IsUnit (M.submatrix r c) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hne)
  have h1 : (M.submatrix r c).rank = n := by rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
  have e : M.submatrix r c = M.submatrix r (Equiv.refl SquareVertex) *
      (1 : Matrix SquareVertex SquareVertex k).submatrix id c := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h2 : (M.submatrix r c).rank ≤ M.rank := by
    rw [e]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_submatrix_le r (Equiv.refl _) M)
  omega

/-! ### The closed set `RankBound` -/

/-- The obstruction polynomials of the two rank bounds. -/
def boundPolys : Set (MvPolynomial Var k) :=
  {f | (∃ (s : Fin 14 → SquareSummand) (c : Fin 14 → MinorChoice 2), Function.Injective s ∧
        f = ∏ i, minorPoly (s i) (c i)) ∨
       (∃ (s s' : SquareSummand) (c c' : MinorChoice 3), s ≠ s' ∧
        f = minorPoly s c * minorPoly s' c')}

/-- The points satisfying the rank bounds: a Zariski-closed subset of `k^2352`. -/
def RankBound (k : Type) [Field k] : Set (Affine k) := zeroLocus k (boundPolys (k := k))

theorem isClosed_rankBound : IsClosed (RankBound k) := isClosed_zeroLocus k _

/-- Summand `s` has rank at most `r` in every mode. -/
def RankLe (v : Var → k) (s : SquareSummand) (r : ℕ) : Prop := ∀ m, (modeMat v s m).rank ≤ r

/-- The rank profile bound: 36 summands of rank `≤ 1` and all but one of rank `≤ 2`. -/
def ProfileBound (v : Var → k) : Prop :=
  (∃ S : Finset SquareSummand, 36 ≤ S.card ∧ ∀ s ∈ S, RankLe v s 1) ∧
    ∃ s₀ : SquareSummand, ∀ s, s ≠ s₀ → RankLe v s 2

theorem mem_rankBound_of_profileBound {v : Affine k} (h : ProfileBound v) : v ∈ RankBound k := by
  obtain ⟨⟨S, hS, h1⟩, s₀, h2⟩ := h
  show ∀ f ∈ boundPolys, eval v f = 0
  intro f hf
  rw [boundPolys, Set.mem_setOf_eq] at hf
  rcases hf with ⟨s, c, hs, rfl⟩ | ⟨s, s', c, c', hss', rfl⟩
  · -- 14 distinct summands meet the 36 summands of rank `≤ 1`.
    have hT : (Finset.univ.image s).card = 14 := by
      rw [Finset.card_image_of_injective _ hs, Finset.card_univ, Fintype.card_fin]
    have hu : (Finset.univ.image s ∪ S).card ≤ 49 :=
      (Finset.card_le_univ _).trans (by simp)
    have hi := Finset.card_union_add_card_inter (Finset.univ.image s) S
    obtain ⟨t, ht⟩ : (Finset.univ.image s ∩ S).Nonempty := by
      rw [← Finset.card_pos]
      omega
    rw [Finset.mem_inter, Finset.mem_image] at ht
    obtain ⟨⟨i, -, rfl⟩, htS⟩ := ht
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [eval_minorPoly]
    exact det_submatrix_eq_zero_of_rank_lt _ _ _ (by have := h1 _ htS (c i).1; omega)
  · rw [map_mul]
    by_cases hs : s = s₀
    · have hs' : s' ≠ s₀ := fun h => hss' (hs.trans h.symm)
      apply mul_eq_zero_of_right
      rw [eval_minorPoly]
      exact det_submatrix_eq_zero_of_rank_lt _ _ _ (by have := h2 s' hs' c'.1; omega)
    · apply mul_eq_zero_of_left
      rw [eval_minorPoly]
      exact det_submatrix_eq_zero_of_rank_lt _ _ _ (by have := h2 s hs c.1; omega)

/-! ### Saturation by equivalences -/

/-- `v'` is dominated by `v`: up to a summand permutation, each mode matrix of `v'` has rank at
most that of some mode matrix of `v`. -/
def Dominated (v' v : Var → k) : Prop :=
  ∃ σ : SquareSummand ≃ SquareSummand, ∀ s m, ∃ m',
    (modeMat v' s m).rank ≤ (modeMat v (σ s) m').rank

/-- The saturation of a set: all points dominated by one of its points. It contains the orbit of
the set under all equivalences (`dominated_of_formula`). -/
def saturation (A : Set (Affine k)) : Set (Affine k) := {v' | ∃ v ∈ A, Dominated v' v}

theorem dominated_refl (v : Var → k) : Dominated v v :=
  ⟨Equiv.refl _, fun _ m => ⟨m, le_rfl⟩⟩

theorem subset_saturation (A : Set (Affine k)) : A ⊆ saturation A :=
  fun v hv => ⟨v, hv, dominated_refl v⟩

/-- **Invariance under equivalences.** If each mode matrix of `v'` is `L M R` or `L Mᵀ R` for a
mode matrix `M` of `v` (after a summand permutation), then `v'` is dominated by `v`. This covers
the `GL₄³`-action, term scalings, summand permutations, cyclic mode permutations and the
transpose symmetry. -/
theorem dominated_of_formula {v' v : Var → k} (σ : SquareSummand ≃ SquareSummand)
    (h : ∀ s m, ∃ m' (L R : Matrix SquareVertex SquareVertex k),
      modeMat v' s m = L * modeMat v (σ s) m' * R ∨
        modeMat v' s m = L * (modeMat v (σ s) m')ᵀ * R) :
    Dominated v' v := by
  refine ⟨σ, fun s m => ?_⟩
  obtain ⟨m', L, R, h | h⟩ := h s m
  · refine ⟨m', ?_⟩
    rw [h]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · refine ⟨m', ?_⟩
    rw [h]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
      (Matrix.rank_transpose _).le

theorem profileBound_of_dominated {v' v : Var → k} (hd : Dominated v' v) (h : ProfileBound v) :
    ProfileBound v' := by
  obtain ⟨σ, hσ⟩ := hd
  obtain ⟨⟨S, hS, h1⟩, s₀, h2⟩ := h
  refine ⟨⟨S.map σ.symm.toEmbedding, by rwa [Finset.card_map], fun s hs m => ?_⟩,
    σ.symm s₀, fun s hs m => ?_⟩
  · rw [Finset.mem_map_equiv, Equiv.symm_symm] at hs
    obtain ⟨m', hm'⟩ := hσ s m
    exact hm'.trans (h1 _ hs m')
  · obtain ⟨m', hm'⟩ := hσ s m
    have hne : σ s ≠ s₀ := fun h => hs (by rw [← h, Equiv.symm_apply_apply])
    exact hm'.trans (h2 _ hne m')

/-! ### Mode matrices along the constructions -/

section Constructions

variable {R : Type*} [CommRing R]

theorem rank_le_of_formula {M N : Matrix SquareVertex SquareVertex k}
    (h : ∃ L R, M = L * N * R) : M.rank ≤ N.rank := by
  obtain ⟨L, R, rfl⟩ := h
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem modeMat_changeBasis {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition R α ι) (P Q T : (Matrix α α R)ˣ) (s : ι) (m : Mode) :
    ∃ L R', modeMat (d.changeBasis P Q T).coordinates s m = L * modeMat d.coordinates s m * R' := by
  cases m
  · exact ⟨P.val.transpose, Q.inv.transpose, rfl⟩
  · exact ⟨Q.val.transpose, T.inv.transpose, rfl⟩
  · exact ⟨P.inv, T.val, rfl⟩

theorem modeMat_rescale {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : Decomposition R α ι) (l m' : ι → Rˣ) (s : ι) (m : Mode) :
    ∃ L R', modeMat (d.rescale l m').coordinates s m = L * modeMat d.coordinates s m * R' := by
  cases m
  · refine ⟨Matrix.diagonal fun _ => ((l s : Rˣ) : R), 1, ?_⟩
    ext a b
    simp only [Matrix.mul_one, Matrix.diagonal_mul]
    rfl
  · refine ⟨Matrix.diagonal fun _ => ((m' s : Rˣ) : R), 1, ?_⟩
    ext a b
    simp only [Matrix.mul_one, Matrix.diagonal_mul]
    rfl
  · refine ⟨Matrix.diagonal fun _ => (((l s)⁻¹ : Rˣ) : R) * (((m' s)⁻¹ : Rˣ) : R), 1, ?_⟩
    ext a b
    simp only [Matrix.mul_one, Matrix.diagonal_mul]
    rfl

theorem modeMat_recursiveLeft {α β ι κ : Type*} (d : Decomposition R α ι)
    (e : ι → Decomposition R β κ) (i : ι) (j : κ) (m : Mode) :
    modeMat (d.recursiveLeft e).coordinates (i, j) m =
      modeMat d.coordinates i m ⊗ₖ modeMat (e i).coordinates j m := by
  cases m <;> rfl

theorem modeMat_recursiveRight {α β ι κ : Type*} (d : κ → Decomposition R α ι)
    (e : Decomposition R β κ) (i : ι) (j : κ) (m : Mode) :
    modeMat (Decomposition.recursiveRight d e).coordinates (i, j) m =
      modeMat (d j).coordinates i m ⊗ₖ modeMat e.coordinates j m := by
  cases m <;> rfl

end Constructions

/-! ### The Strassen factors -/

/-- The Strassen mode matrices, over `k`. -/
def sMat (k : Type) [Field k] (i : Fin 7) (m : Mode) : Matrix (Fin 2) (Fin 2) k :=
  (modeMat strassen.coordinates i m).map (Int.castRingHom k)

/-- Column factors of the rank-one Strassen summands `1, …, 6`. -/
def fc : Mode → Fin 7 → Fin 2 → ℤ
  | .u => ![![0, 0], ![0, 1], ![1, 0], ![0, 1], ![1, 0], ![1, -1], ![1, -1]]
  | .v => ![![0, 0], ![1, 0], ![1, -1], ![1, -1], ![0, 1], ![1, 0], ![0, 1]]
  | .w => ![![0, 0], ![0, 1], ![1, 1], ![1, 1], ![1, 0], ![0, 1], ![1, 0]]

/-- Row factors of the rank-one Strassen summands `1, …, 6`. -/
def fr : Mode → Fin 7 → Fin 2 → ℤ
  | .u => ![![0, 0], ![1, 1], ![1, 0], ![0, 1], ![1, 1], ![-1, 0], ![0, 1]]
  | .v => ![![0, 0], ![1, 0], ![0, 1], ![-1, 0], ![0, 1], ![1, 1], ![1, 1]]
  | .w => ![![0, 0], ![1, -1], ![0, 1], ![1, 0], ![-1, 1], ![0, 1], ![1, 0]]

set_option maxRecDepth 8192 in
/-- Summands `1, …, 6` of Strassen are rank one in every mode, evaluated by the kernel. -/
theorem strassen_factor : ∀ m : Mode, ∀ i : Fin 7, i ≠ 0 → ∀ a b : Fin 2,
    strassen.coordinates (i, m, (a, b)) = fc m i a * fr m i b := by
  decide

/-- The column `fc m i` as a `2 × 1` matrix over `k`. -/
def colM (k : Type) [Field k] (x : Fin 2 → ℤ) : Matrix (Fin 2) Unit k := fun a _ => (x a : k)

/-- The row `fr m i` as a `1 × 2` matrix over `k`. -/
def rowM (k : Type) [Field k] (x : Fin 2 → ℤ) : Matrix Unit (Fin 2) k := fun _ b => (x b : k)

theorem sMat_eq (m : Mode) (i : Fin 7) (hi : i ≠ 0) :
    sMat k i m = colM k (fc m i) * rowM k (fr m i) := by
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_unique]
  simp only [sMat, Matrix.map_apply, modeMat, colM, rowM]
  rw [strassen_factor m i hi a b, map_mul]
  rfl

/-! ### Kronecker rank bounds -/

theorem rank_kron_le {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂]
    {A B : Matrix (Fin 2) (Fin 2) k} (A₁ : Matrix (Fin 2) κ₁ k) (A₂ : Matrix κ₁ (Fin 2) k)
    (B₁ : Matrix (Fin 2) κ₂ k) (B₂ : Matrix κ₂ (Fin 2) k) (hA : A = A₁ * A₂) (hB : B = B₁ * B₂) :
    (A ⊗ₖ B).rank ≤ Fintype.card κ₁ * Fintype.card κ₂ := by
  subst hA hB
  rw [Matrix.mul_kronecker_mul]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans (le_of_eq (Fintype.card_prod _ _)))

/-- The rank budget of index `i`: `2` for the full-rank Strassen summand `0`, else `1`. -/
def budget (i : Fin 7) : ℕ := if i = 0 then 2 else 1

/-- `A ⊗ₖ (L B R)` for Strassen factors `A = sMat i m`, `B = sMat j m`. -/
theorem rank_kron_strassen (i j : Fin 7) (m : Mode) (L R : Matrix (Fin 2) (Fin 2) k) :
    (sMat k i m ⊗ₖ (L * sMat k j m * R)).rank ≤ budget i * budget j := by
  unfold budget
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [if_pos hi, if_pos hj]
    exact (rank_kron_le (sMat k i m) 1 (L * sMat k j m) R (Matrix.mul_one _).symm rfl).trans
      (by simp)
  · rw [if_pos hi, if_neg hj]
    exact (rank_kron_le (sMat k i m) 1 (L * colM k (fc m j)) (rowM k (fr m j) * R)
      (Matrix.mul_one _).symm (by rw [sMat_eq m j hj]; simp only [Matrix.mul_assoc])).trans
      (by simp)
  · rw [if_neg hi, if_pos hj]
    exact (rank_kron_le (colM k (fc m i)) (rowM k (fr m i)) (L * sMat k j m) R
      (sMat_eq m i hi) rfl).trans (by simp)
  · rw [if_neg hi, if_neg hj]
    exact (rank_kron_le (colM k (fc m i)) (rowM k (fr m i)) (L * colM k (fc m j))
      (rowM k (fr m j) * R) (sMat_eq m i hi)
      (by rw [sMat_eq m j hj]; simp only [Matrix.mul_assoc])).trans (by simp)

/-- `(L A R) ⊗ₖ B` for Strassen factors `A = sMat i m`, `B = sMat j m`. -/
theorem rank_kron_strassen' (i j : Fin 7) (m : Mode) (L R : Matrix (Fin 2) (Fin 2) k) :
    ((L * sMat k i m * R) ⊗ₖ sMat k j m).rank ≤ budget i * budget j := by
  unfold budget
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [if_pos hi, if_pos hj]
    exact (rank_kron_le (L * sMat k i m) R (sMat k j m) 1 rfl (Matrix.mul_one _).symm).trans
      (by simp)
  · rw [if_pos hi, if_neg hj]
    exact (rank_kron_le (L * sMat k i m) R (colM k (fc m j)) (rowM k (fr m j)) rfl
      (sMat_eq m j hj)).trans (by simp)
  · rw [if_neg hi, if_pos hj]
    exact (rank_kron_le (L * colM k (fc m i)) (rowM k (fr m i) * R) (sMat k j m) 1
      (by rw [sMat_eq m i hi]; simp only [Matrix.mul_assoc]) (Matrix.mul_one _).symm).trans
      (by simp)
  · rw [if_neg hi, if_neg hj]
    exact (rank_kron_le (L * colM k (fc m i)) (rowM k (fr m i) * R) (colM k (fc m j))
      (rowM k (fr m j)) (by rw [sMat_eq m i hi]; simp only [Matrix.mul_assoc])
      (sMat_eq m j hj)).trans (by simp)

/-! ### The families -/

theorem modeMat_leftFamily (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) (i j : Fin 7)
    (m : Mode) : ∃ L R, modeMat (leftFamily P Q T).coordinates (i, j) m =
      sMat k i m ⊗ₖ (L * sMat k j m * R) := by
  cases m
  · exact ⟨(P i).val.transpose, (Q i).inv.transpose, rfl⟩
  · exact ⟨(Q i).val.transpose, (T i).inv.transpose, rfl⟩
  · exact ⟨(P i).inv, (T i).val, rfl⟩

theorem modeMat_rightFamily (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) k)ˣ) (i j : Fin 7)
    (m : Mode) : ∃ L R, modeMat (rightFamily P Q T).coordinates (i, j) m =
      (L * sMat k i m * R) ⊗ₖ sMat k j m := by
  cases m
  · exact ⟨(P j).val.transpose, (Q j).inv.transpose, rfl⟩
  · exact ⟨(Q j).val.transpose, (T j).inv.transpose, rfl⟩
  · exact ⟨(P j).inv, (T j).val, rfl⟩

/-- **Ranks on the family.** Summand `(i, j)` of `pq.value left` has every mode of rank at most
`budget i * budget j`. -/
theorem rank_value_le (pq : FamilyParameters k) (left : Bool) (i j : Fin 7) (m : Mode) :
    (modeMat (pq.value left).coordinates (i, j) m).rank ≤ budget i * budget j := by
  have key : ∀ d : Decomposition k SquareVertex SquareSummand,
      (modeMat ((d.changeBasis (pq.global 0) (pq.global 1) (pq.global 2)).rescale
        (fun s => pq.scale s 0) (fun s => pq.scale s 1)).coordinates (i, j) m).rank ≤
        (modeMat d.coordinates (i, j) m).rank := fun d =>
    (rank_le_of_formula (modeMat_rescale _ _ _ _ m)).trans
      (rank_le_of_formula (modeMat_changeBasis _ _ _ _ _ m))
  cases left
  · refine (key (rightFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2))).trans ?_
    obtain ⟨L, R, h⟩ := modeMat_rightFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2) i j m
    rw [h]
    exact rank_kron_strassen' i j m L R
  · refine (key (leftFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2))).trans ?_
    obtain ⟨L, R, h⟩ := modeMat_leftFamily (fun l => pq.block l 0) (fun l => pq.block l 1)
      (fun l => pq.block l 2) i j m
    rw [h]
    exact rank_kron_strassen i j m L R

/-- The 36 summands `(i, j)` with `i ≠ 0` and `j ≠ 0`. -/
def onesSet : Finset SquareSummand := Finset.univ.filter fun s => s.1 ≠ 0 ∧ s.2 ≠ 0

theorem card_onesSet : onesSet.card = 36 := by decide

/-- **The family satisfies the rank bounds.** -/
theorem profileBound_family (pq : FamilyParameters k) (left : Bool) :
    ProfileBound (pq.value left).coordinates := by
  refine ⟨⟨onesSet, card_onesSet.ge, fun s hs m => ?_⟩, (0, 0), fun s hs m => ?_⟩
  · obtain ⟨i, j⟩ := s
    simp only [onesSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have := rank_value_le pq left i j m
    simpa [budget, hs.1, hs.2] using this
  · obtain ⟨i, j⟩ := s
    have := rank_value_le pq left i j m
    by_cases hi : i = 0
    · have hj : j ≠ 0 := fun hj => hs (by rw [hi, hj])
      simpa [budget, hi, hj] using this
    · by_cases hj : j = 0
      · simpa [budget, hi, hj] using this
      · have h1 : budget i * budget j = 1 := by simp [budget, hi, hj]
        omega

theorem image_subset_rankBound (left : Bool) : imageA k left ⊆ RankBound k := by
  rintro _ ⟨pq, rfl⟩
  exact mem_rankBound_of_profileBound (profileBound_family pq left)

theorem saturation_subset_rankBound (left : Bool) : saturation (imageA k left) ⊆ RankBound k := by
  rintro v ⟨w, ⟨pq, rfl⟩, hd⟩
  exact mem_rankBound_of_profileBound (profileBound_of_dominated hd (profileBound_family pq left))

/-- **The rank bounds hold on the Zariski closure of the saturated union of both families**,
over every field. -/
theorem closure_saturation_subset_rankBound :
    closure (saturation (imageA k true) ∪ saturation (imageA k false)) ⊆ RankBound k :=
  closure_minimal (Set.union_subset (saturation_subset_rankBound true)
    (saturation_subset_rankBound false)) isClosed_rankBound

end Brent.Census
