import Brent.KernelCheck.HilbertTwo
import Brent.KernelCheck.KernelVanishing
import Brent.AugmentedTrace
import Brent.KernelCheck.SquareJacobianRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The relation space has dimension 648

Every symmetrized quadratic table of a left-kernel covector vanishes outside the 54 × 54
mixed block (by `KernelVanishing`, using `2 ≠ 0` on the diagonal). On the mixed block it
is the contraction with the mixed quadratic columns `M`. Hence
`dim Rel = dim {μ M : μ J = 0} = rank [J | M] - rank J = 2749 - 2101 = 648`.
-/

open scoped BigOperators

namespace Brent.MixedRank

open TangentData QuadraticData UpperBound HilbertTwo

variable (k : Type) [Field k]

theorem left_direction_any (a : Fin 54) :
    frameDirection k (xFrameIndex a) = (xDirection a).map (Int.castRingHom k) := by
  apply Decomposition.eq_of_components <;> funext s q
  · exact congrArg (fun z : Int => (z : k)) (archived_left_coordinates a (s, Mode.u, q))
  · exact congrArg (fun z : Int => (z : k)) (archived_left_coordinates a (s, Mode.v, q))
  · exact congrArg (fun z : Int => (z : k)) (archived_left_coordinates a (s, Mode.w, q))

theorem right_direction_any (b : Fin 54) :
    frameDirection k (yFrameIndex b) = (yDirection b).map (Int.castRingHom k) := by
  apply Decomposition.eq_of_components <;> funext s q
  · exact congrArg (fun z : Int => (z : k)) (archived_right_coordinates b (s, Mode.u, q))
  · exact congrArg (fun z : Int => (z : k)) (archived_right_coordinates b (s, Mode.v, q))
  · exact congrArg (fun z : Int => (z : k)) (archived_right_coordinates b (s, Mode.w, q))

/-- The mixed polar rows. -/
noncomputable def mixedRow (p : Fin 54 × Fin 54) (e : EquationIndex SquareVertex) : k :=
  (strassenSquare k).polarizedEntry (frameDirection k (xFrameIndex p.1))
    (frameDirection k (yFrameIndex p.2)) e.1 e.2.1 e.2.2

theorem mixedEntry_cast (a b : Fin 54) (e : EquationIndex SquareVertex) :
    (mixedEntry a b e : k) = mixedRow k (a, b) e := by
  rw [mixedRow, left_direction_any, right_direction_any]
  let x := xDirection a
  let y := yDirection b
  let p := strassenSquareInt
  have integer : mixedEntry a b e = p.polarizedEntry x y e.1 e.2.1 e.2.2 := by
    unfold mixedEntry
    simp only [Decomposition.quadraticEntry, Decomposition.polarizedEntry, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    change (x.u s e.1 + y.u s e.1) * (x.v s e.2.1 + y.v s e.2.1) * p.w s e.2.2 +
      (x.u s e.1 + y.u s e.1) * p.v s e.2.1 * (x.w s e.2.2 + y.w s e.2.2) +
      p.u s e.1 * (x.v s e.2.1 + y.v s e.2.1) * (x.w s e.2.2 + y.w s e.2.2) - _ - _ = _
    ring
  rw [integer]
  change (Int.castRingHom k) (p.polarizedEntry x y e.1 e.2.1 e.2.2) = _
  simp only [Decomposition.polarizedEntry, map_sum, map_add, map_mul, strassenSquare,
    Decomposition.map, p, x, y]

/-- The rows of the augmented matrix `[J | M]ᵗ`. -/
noncomputable def rows :
    Variable SquareVertex SquareSummand ⊕ (Fin 54 × Fin 54) → EquationIndex SquareVertex → k :=
  Sum.elim (fun x e => J k x e) (mixedRow k)

theorem jac_decode (x : Variable SquareVertex SquareSummand) (e : EquationIndex SquareVertex) :
    SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat)
      (JacobianTrace.original (squareVariableNumber x)) (squareEquationNumber e) = J k x e := by
  simp only [SparseRow.decode, JacobianTrace.original, Equiv.symm_apply_apply,
    squareJacobianColumn_correct]
  obtain ⟨s, m, x⟩ := x
  obtain ⟨a, b, c⟩ := e
  cases m <;>
    simp only [Decomposition.jacobianColumn_eq, strassenSquare, Decomposition.map] <;>
      split_ifs <;> simp

theorem mixed_decode (p : Fin 54 × Fin 54) (e : EquationIndex SquareVertex) :
    SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (mixedColumn p.1 p.2)
      (squareEquationNumber e) = mixedRow k p e := by
  simp only [SparseRow.decode]
  rw [coefficient_mixedColumn, mixedEntry_cast]

theorem original_left (i : Fin 2352) :
    AugmentedTrace.original (Fin.castAdd 2916 i) = JacobianTrace.original i := by
  simp only [AugmentedTrace.original, Fin.addCases_left]

theorem original_right (i : Fin (54 * 54)) :
    AugmentedTrace.original (Fin.natAdd 2352 i) =
      mixedColumn (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
  simp only [AugmentedTrace.original, Fin.addCases_right]
  rfl

/-- The augmented trace rows, reindexed by equations. -/
noncomputable def traceRow (i : Fin 5268) : EquationIndex SquareVertex → k :=
  fun e => SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (AugmentedTrace.original i)
    (squareEquationNumber e)

theorem traceRow_left (x : Variable SquareVertex SquareSummand) :
    traceRow k (Fin.castAdd 2916 (squareVariableNumber x)) = rows k (Sum.inl x) := by
  funext e
  rw [traceRow, original_left, jac_decode]
  rfl

theorem traceRow_right (p : Fin 54 × Fin 54) :
    traceRow k (Fin.natAdd 2352 (finProdFinEquiv p)) = rows k (Sum.inr p) := by
  funext e
  rw [traceRow, original_right, Equiv.symm_apply_apply, mixed_decode]
  rfl

theorem range_rows : Set.range (rows k) = Set.range (traceRow k) := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    cases r with
    | inl x => exact ⟨_, traceRow_left k x⟩
    | inr p => exact ⟨_, traceRow_right k p⟩
  · rintro ⟨i, rfl⟩
    refine @Fin.addCases 2352 2916 (fun i => ∃ r, rows k r = traceRow k i)
      (fun a => ?_) (fun b => ?_) i
    · refine ⟨Sum.inl (squareVariableNumber.symm a), ?_⟩
      rw [← traceRow_left, Equiv.apply_symm_apply]
    · refine ⟨Sum.inr (finProdFinEquiv.symm (b : Fin (54 * 54))), ?_⟩
      rw [← traceRow_right, Equiv.apply_symm_apply]

theorem rows_rank (haug : Module.finrank k (Submodule.span k (Set.range (fun i =>
      SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (AugmentedTrace.original i)))) = 2749) :
    Module.finrank k (Submodule.span k (Set.range (rows k))) = 2749 := by
  let L : (Fin 4096 → k) ≃ₗ[k] (EquationIndex SquareVertex → k) :=
    LinearEquiv.funCongrLeft k k squareEquationNumber
  have hrange : Set.range (traceRow k) = (L : (Fin 4096 → k) →ₗ[k] _) '' Set.range (fun i =>
      SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (AugmentedTrace.original i)) := by
    rw [← Set.range_comp]
    rfl
  rw [range_rows, hrange, Submodule.span_image, LinearEquiv.finrank_map_eq, haug]

/-! ### Kernel dimensions -/

/-- Rank–nullity for a family of rows. -/
theorem ker_add_span {ι E : Type} [Fintype ι] [Fintype E] [DecidableEq E] (r : ι → E → k) :
    Module.finrank k (LinearMap.ker (Matrix.of r).mulVecLin) +
      Module.finrank k (Submodule.span k (Set.range r)) = Fintype.card E := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.of r).mulVecLin
  have hr : Module.finrank k (LinearMap.range (Matrix.of r).mulVecLin) = (Matrix.of r).rank := rfl
  rw [hr, Matrix.rank_eq_finrank_span_row, Module.finrank_fintype_fun_eq_card] at h
  rw [← h, add_comm]
  rfl

/-- The contraction with the mixed rows. -/
noncomputable def Mt : (EquationIndex SquareVertex → k) →ₗ[k] (Fin 54 × Fin 54 → k) :=
  (Matrix.of (mixedRow k)).mulVecLin

theorem Mt_apply (μ : EquationIndex SquareVertex → k) (p : Fin 54 × Fin 54) :
    Mt k μ p = ∑ e, mixedRow k p e * μ e := by
  simp only [Mt, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem Jt_eq : Jt k = (Matrix.of (fun x e => J k x e)).mulVecLin := by
  refine LinearMap.ext fun μ => funext fun x => ?_
  simp only [Jt, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply]

theorem ker_rows : LinearMap.ker (Matrix.of (rows k)).mulVecLin =
    LinearMap.ker (Jt k) ⊓ LinearMap.ker (Mt k) := by
  ext μ
  simp only [Submodule.mem_inf, LinearMap.mem_ker, funext_iff, Pi.zero_apply, Sum.forall]
  rfl

theorem finrank_ker_Jt : Module.finrank k (LinearMap.ker (Jt k)) = 1995 := by
  have h := ker_add_span k (fun x e => J k x e)
  have hr : Module.finrank k (Submodule.span k (Set.range (fun x e => J k x e))) = 2101 :=
    square_jacobian_rank k
  rw [hr, square_equation_count, ← Jt_eq] at h
  omega

theorem finrank_ker_rows (haug : Module.finrank k (Submodule.span k (Set.range (rows k))) = 2749) :
    Module.finrank k ((LinearMap.ker (Jt k) ⊓ LinearMap.ker (Mt k) :
      Submodule k (EquationIndex SquareVertex → k))) = 1347 := by
  have h := ker_add_span k (rows k)
  rw [haug, square_equation_count, ker_rows] at h
  omega

theorem finrank_map_Mt (haug : Module.finrank k (Submodule.span k (Set.range (rows k))) = 2749) :
    Module.finrank k ((LinearMap.ker (Jt k)).map (Mt k)) = 648 := by
  let P := LinearMap.ker (Jt k)
  let f := (Mt k).domRestrict P
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range f = P.map (Mt k) := by
    ext v
    simp only [LinearMap.mem_range, Submodule.mem_map, f, LinearMap.domRestrict_apply]
    constructor
    · rintro ⟨μ, rfl⟩; exact ⟨μ, μ.2, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩; exact ⟨⟨μ, hμ⟩, rfl⟩
  have hker : LinearMap.ker f = (P ⊓ LinearMap.ker (Mt k)).comap P.subtype := by
    ext μ
    simp only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.mem_inf, Submodule.subtype_apply]
    exact ⟨fun h => ⟨μ.2, h⟩, fun h => h.2⟩
  have hk : Module.finrank k (LinearMap.ker f) = 1347 := by
    rw [hker, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq]
    exact finrank_ker_rows k haug
  have hP : Module.finrank k P = 1995 := finrank_ker_Jt k
  rw [hrange, hk, hP] at h
  show Module.finrank k (P.map (Mt k)) = 648
  omega

/-! ### The table is supported on the mixed block -/

/-- The unordered mixed pair. -/
def pairOf (p : Fin 54 × Fin 54) : Sym2 (Fin 251) := s(xFrameIndex p.1, yFrameIndex p.2)

theorem mk_eq_pairOf (i j : Fin 251) (p : Fin 54 × Fin 54) (h : s(i, j) = pairOf p) :
    (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) ∨ (143 ≤ j.val ∧ j.val < 197 ∧ 197 ≤ i.val) := by
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; simp only [xFrameIndex, yFrameIndex]; omega
  · right; simp only [xFrameIndex, yFrameIndex]; omega

theorem pairOf_injective : Function.Injective pairOf := by
  intro p q h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [xFrameIndex, yFrameIndex, Fin.ext_iff] at h1 h2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · simp only [xFrameIndex, yFrameIndex, Fin.ext_iff] at h1 h2
    have := p.1.isLt
    omega

/-- Spread a mixed table over unordered pairs. -/
noncomputable def ι : (Fin 54 × Fin 54 → k) →ₗ[k] (Sym2 (Fin 251) → k) :=
  Fintype.linearCombination k (fun p => Pi.single (pairOf p) (1 : k))

theorem ι_apply (g : Fin 54 × Fin 54 → k) (s : Sym2 (Fin 251)) :
    ι k g s = ∑ p, g p * if s = pairOf p then 1 else 0 := by
  simp only [ι, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]

theorem ι_pairOf (g : Fin 54 × Fin 54 → k) (p : Fin 54 × Fin 54) : ι k g (pairOf p) = g p := by
  rw [ι_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    rw [if_neg (fun h => hq (pairOf_injective h).symm), mul_zero]
  · simp

theorem ι_injective : Function.Injective (ι k) := by
  intro g g' h
  funext p
  rw [← ι_pairOf k g, ← ι_pairOf k g', h]

theorem β_add (μ : EquationIndex SquareVertex → k) (i j : Fin 251) :
    β k μ i j + β k μ j i = ∑ e, (strassenSquare k).polarizedEntry
      (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2 * μ e := by
  simp only [β, ← Finset.sum_add_distrib, Decomposition.polarizedEntry_eq_bilinear, add_mul]

theorem kernel_column {μ : EquationIndex SquareVertex → k} (hμ : μ ∈ LinearMap.ker (Jt k))
    (x : Variable SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex,
      (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2 * μ e = 0 :=
  congrFun (LinearMap.mem_ker.mp hμ) x

theorem table_pairOf {μ : EquationIndex SquareVertex → k} (p : Fin 54 × Fin 54) :
    table k μ (pairOf p) = Mt k μ p := by
  have hne : xFrameIndex p.1 ≠ yFrameIndex p.2 := by
    intro h; simp only [xFrameIndex, yFrameIndex, Fin.ext_iff] at h; have := p.1.isLt; omega
  change symm (β k μ) s(xFrameIndex p.1, yFrameIndex p.2) = _
  rw [symm_mk, if_neg hne, β_add, Mt_apply]
  rfl

theorem table_eq (h2 : (2 : k) ≠ 0) {μ : EquationIndex SquareVertex → k}
    (hμ : μ ∈ LinearMap.ker (Jt k)) : table k μ = ι k (Mt k μ) := by
  funext s
  induction s using Sym2.ind with
  | h i j =>
    by_cases hm : (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) ∨
        (143 ≤ j.val ∧ j.val < 197 ∧ 197 ≤ i.val)
    · have key : ∀ a b : Fin 251, 143 ≤ a.val → a.val < 197 → 197 ≤ b.val →
          table k μ s(a, b) = ι k (Mt k μ) s(a, b) := by
        intro a b ha ha' hb
        have hb' := b.isLt
        let p : Fin 54 × Fin 54 := (⟨a.val - 143, by omega⟩, ⟨b.val - 197, by omega⟩)
        have hp : s(a, b) = pairOf p :=
          Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext (by simp only [p, xFrameIndex]; omega),
            Fin.ext (by simp only [p, yFrameIndex]; omega)⟩)
        rw [hp, table_pairOf, ι_pairOf]
      rcases hm with ⟨ha, ha', hb⟩ | ⟨ha, ha', hb⟩
      · exact key i j ha ha' hb
      · rw [Sym2.eq_swap]; exact key j i ha ha' hb
    · rw [ι_apply, Finset.sum_eq_zero fun q _ => by
        rw [if_neg (fun h => hm (mk_eq_pairOf i j q h)), mul_zero]]
      change symm (β k μ) s(i, j) = 0
      rw [symm_mk]
      split_ifs with hij
      · subst hij
        exact KernelVanishing.square_zero μ (kernel_column k hμ)
          (fun r hr => (mul_eq_zero.mp hr).resolve_left h2) i
      · rw [β_add]
        exact KernelVanishing.nonmixed_zero μ (kernel_column k hμ) i j hm

/-! ### The count -/

theorem finrank_Rel (h2 : (2 : k) ≠ 0)
    (haug : Module.finrank k (Submodule.span k (Set.range (rows k))) = 2749) :
    Module.finrank k (HilbertTwo.Rel k) = 648 := by
  have hRel : HilbertTwo.Rel k = ((LinearMap.ker (Jt k)).map (Mt k)).map (ι k) := by
    rw [HilbertTwo.Rel, ← Submodule.map_comp]
    ext v
    simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, hμ, (table_eq k h2 hμ).symm⟩
    · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, hμ, table_eq k h2 hμ⟩
  rw [hRel, ← (Submodule.equivMapOfInjective _ (ι_injective k) _).finrank_eq]
  exact finrank_map_Mt k haug

/-- The second Hilbert value, given the augmented trace rank. -/
theorem hilbertValue_two_of_rank (h2 : (2 : k) ≠ 0)
    (haug : Module.finrank k (Submodule.span k (Set.range (fun i =>
      SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (AugmentedTrace.original i)))) = 2749) :
    hilbertValue k (A k) 2 = 30978 := by
  have h := hilbertValue_two_add k
  rw [finrank_Rel k h2 (rows_rank k haug)] at h
  omega

end Brent.MixedRank
