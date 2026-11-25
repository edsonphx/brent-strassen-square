import Brent.KernelCheck.SecondOrder
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The degree-two Hilbert value

Over any field, `𝔪²/𝔪³` is spanned by the classes of `zᵢ zⱼ`, indexed by unordered pairs.
The relations among them are exactly the symmetrized quadratic tables `β_μ` of the
covectors `μ` in the left kernel of the Jacobian. Relations hold by the Taylor expansion,
and there are no others by the second-order points of `SecondOrder.lean`. Hence
`H(2) = 31626 - dim Rel`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.HilbertTwo

open TangentData QuadraticData CharThree UpperBound SecondJet SecondOrder

variable (k : Type) [Field k]

/-! ### Sums over unordered pairs -/

/-- The symmetrization of a table on ordered pairs. -/
def symm {M : Type*} [AddCommMonoid M] {n : ℕ} (G : Fin n → Fin n → M) : Sym2 (Fin n) → M :=
  Sym2.lift ⟨fun i j => if i = j then G i i else G i j + G j i, fun i j => by
    by_cases h : i = j
    · subst h; rfl
    · dsimp only; rw [if_neg h, if_neg (Ne.symm h), add_comm]⟩

@[simp] theorem symm_mk {M : Type*} [AddCommMonoid M] {n : ℕ} (G : Fin n → Fin n → M) (i j : Fin n) :
    symm G s(i, j) = if i = j then G i i else G i j + G j i := rfl

theorem sum_sym2 {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Sym2 (Fin n) → M) :
    ∑ s, f s = ∑ i, ∑ j, if i ≤ j then f s(i, j) else 0 := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
  rw [← (Sym2.sortEquiv (α := Fin n)).symm.sum_comp]
  rw [Finset.sum_subtype _ (p := fun p : Fin n × Fin n => p.1 ≤ p.2) (by simp)]
  rfl

theorem sum_sum_eq_sum_symm {R : Type*} [CommRing R] {n : ℕ} (G : Fin n → Fin n → R) :
    ∑ i, ∑ j, G i j = ∑ s, symm G s := by
  rw [sum_sym2, Brent.sum_sum_eq_ordered]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symm_mk]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h, if_pos h.le, if_neg (ne_of_lt h)]
  · subst h; simp
  · rw [if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h), if_neg (not_le.mpr h)]

/-! ### The relation space -/

/-- The transposed Jacobian. -/
noncomputable def Jt : (EquationIndex SquareVertex → k) →ₗ[k] (Variable SquareVertex SquareSummand → k) where
  toFun μ x := ∑ e, J k x e * μ e
  map_add' μ ν := by funext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r μ := by funext x; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring

/-- The symmetrized quadratic table of a covector. -/
noncomputable def table : (EquationIndex SquareVertex → k) →ₗ[k] (Sym2 (Fin 251) → k) where
  toFun μ := symm (β k μ)
  map_add' μ ν := by
    funext s
    induction s using Sym2.ind with
    | h i j =>
      simp only [symm_mk, Pi.add_apply, β, mul_add, Finset.sum_add_distrib]
      split_ifs <;> ring
  map_smul' r μ := by
    funext s
    induction s using Sym2.ind with
    | h i j =>
      simp only [symm_mk, Pi.smul_apply, smul_eq_mul, β, RingHom.id_apply]
      split_ifs
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
      · rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun e _ => by ring

/-- The relation space. -/
noncomputable def Rel : Submodule k (Sym2 (Fin 251) → k) :=
  (LinearMap.ker (Jt k)).map (table k)

/-! ### The monomials of degree two -/

/-- The products `zᵢ zⱼ`. -/
noncomputable def zz (s : Sym2 (Fin 251)) : A k :=
  Sym2.lift ⟨fun i j => z k i * z k j, fun _ _ => mul_comm _ _⟩ s

theorem zz_mk (i j : Fin 251) : zz k s(i, j) = z k i * z k j := rfl

theorem zz_mem (s : Sym2 (Fin 251)) : zz k s ∈ maximalIdeal (A k) ^ 2 := by
  induction s using Sym2.ind with
  | h i j => rw [zz_mk, pow_two]; exact Ideal.mul_mem_mul (z_mem k i) (z_mem k j)

/-- The coefficient map onto `𝔪²/𝔪³`. -/
noncomputable def Ψ₂ :=
  Fintype.linearCombination k (fun s : Sym2 (Fin 251) => proj k (A k) 2 (zz k s))

theorem Ψ₂_apply (c : Sym2 (Fin 251) → k) :
    Ψ₂ k c = proj k (A k) 2 (∑ s, c s • zz k s) := by
  rw [Ψ₂, Fintype.linearCombination_apply, map_sum]
  simp only [map_smul]

theorem range_Ψ₂ : LinearMap.range (Ψ₂ k) = gradedPiece k (A k) 2 := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [Ψ₂_apply]
    have hmem : ∑ s, c s • zz k s ∈ maximalIdeal (A k) ^ 2 := by
      refine Submodule.sum_mem _ fun s _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (zz_mem k s)
    exact proj_mem 2 hmem
  · refine (gradedPiece_two_le_span (HilbertInitial.residue k) (z k) (z_mem k)
      (CharZeroBound.gen_z k)).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine ⟨Pi.single s(i, j) 1, ?_⟩
    rw [Ψ₂, Fintype.linearCombination_apply_single, one_smul, zz_mk]

/-! ### Relations -/

theorem quad_rel (μ : EquationIndex SquareVertex → k) (hμ : μ ∈ LinearMap.ker (Jt k)) :
    ∑ i, ∑ j, z k i * z k j * algebraMap k (A k) (β k μ i j) ∈ maximalIdeal (A k) ^ 3 := by
  have h := quad_rel_Z k μ fun x => congrFun (LinearMap.mem_ker.mp hμ) x
  rwa [expand] at h

theorem Rel_le_ker : Rel k ≤ LinearMap.ker (Ψ₂ k) := by
  rintro _ ⟨μ, hμ, rfl⟩
  rw [LinearMap.mem_ker, Ψ₂_apply]
  have e : ∑ s, table k μ s • zz k s =
      ∑ i, ∑ j, z k i * z k j * algebraMap k (A k) (β k μ i j) := by
    rw [sum_sum_eq_sum_symm (fun i j => z k i * z k j * algebraMap k (A k) (β k μ i j))]
    refine Finset.sum_congr rfl fun s _ => ?_
    induction s using Sym2.ind with
    | h i j =>
      change symm (β k μ) s(i, j) • zz k s(i, j) = _
      rw [symm_mk, symm_mk, zz_mk]
      split_ifs with hij
      · subst hij; rw [Algebra.smul_def]; ring
      · rw [Algebra.smul_def, map_add]; ring
  rw [e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact quad_rel k μ hμ

/-! ### Admissible second-order points exist -/

theorem pairing_table (T : Sym2 (Fin 251) → k) (μ : EquationIndex SquareVertex → k) :
    ∑ e, (∑ i, ∑ j, T s(i, j) *
      (strassenSquare k).bilinearEntry (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2) *
        μ e = ∑ s, T s * table k μ s := by
  have h1 : ∑ e, (∑ i, ∑ j, T s(i, j) *
      (strassenSquare k).bilinearEntry (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2) *
        μ e = ∑ i, ∑ j, T s(i, j) * β k μ i j := by
    simp only [β, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => by ring
  rw [h1, sum_sum_eq_sum_symm]
  refine Finset.sum_congr rfl fun s _ => ?_
  induction s using Sym2.ind with
  | h i j =>
    change _ = T s(i, j) * symm (β k μ) s(i, j)
    rw [symm_mk, symm_mk]
    split_ifs with hij
    · subst hij; rfl
    · rw [Sym2.eq_swap (a := j)]; ring

theorem exists_admissible (T : Sym2 (Fin 251) → k)
    (hT : ∀ μ ∈ LinearMap.ker (Jt k), ∑ s, T s * table k μ s = 0) :
    ∃ W, Admissible T W := by
  let b : EquationIndex SquareVertex → k := fun e => ∑ i, ∑ j, T s(i, j) *
    (strassenSquare k).bilinearEntry (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2
  let B : Module.Dual k (EquationIndex SquareVertex → k) :=
    { toFun := fun μ => -∑ e, b e * μ e
      map_add' := fun μ ν => by simp [mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun r μ => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.sum_neg_distrib]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring }
  have hB : B ∈ LinearMap.range (Jt k).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro μ hμ
    change -∑ e, b e * μ e = 0
    rw [pairing_table k T μ, hT μ hμ, neg_zero]
  obtain ⟨g, hg⟩ := hB
  refine ⟨fun x => g (Pi.single x 1), fun e => ?_⟩
  have h := congrArg (fun f : Module.Dual k _ => f (Pi.single e 1)) hg
  simp only [LinearMap.dualMap_apply, B, LinearMap.coe_mk, AddHom.coe_mk] at h
  have hJ : Jt k (Pi.single e 1) =
      ∑ x, J k x e • (Pi.single x (1 : k) : Variable SquareVertex SquareSummand → k) := by
    funext x
    simp [Jt, Pi.single_apply, Finset.sum_apply]
  rw [hJ, map_sum] at h
  simp only [map_smul, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]
  ring

/-! ### No further relations -/

theorem ker_le_Rel : LinearMap.ker (Ψ₂ k) ≤ Rel k := by
  intro c hc
  rw [LinearMap.mem_ker, Ψ₂_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  have hc' : ∑ s, c s • zz k s ∈ maximalIdeal (A k) ^ 3 := hc
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := Rel k),
    Submodule.mem_dualCoannihilator]
  intro f hf
  let T : Sym2 (Fin 251) → k := fun s => f (fun j => if s = j then (1 : k) else 0)
  have hfT : ∀ g : Sym2 (Fin 251) → k, f g = ∑ s, T s * g s := by
    intro g
    conv_lhs => rw [pi_eq_sum_univ g]
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hT : ∀ μ ∈ LinearMap.ker (Jt k), ∑ s, T s * table k μ s = 0 := by
    intro μ hμ
    rw [← hfT]
    exact (Submodule.mem_dualAnnihilator _).mp hf _ ⟨μ, hμ, rfl⟩
  obtain ⟨W, hW⟩ := exists_admissible k T hT
  have h0 := congrArg (functional hW) (show (∑ s, c s • zz k s) = ∑ s, c s • zz k s from rfl)
  have hzero : functional hW (∑ s, c s • zz k s) = 0 := by
    rw [functional_apply, localPoint_cube hW hc']; rfl
  rw [map_sum] at hzero
  rw [hfT]
  rw [← hzero]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 1
  induction s using Sym2.ind with
  | h i j => rw [functional_apply, zz_mk, localPoint_zz]

theorem ker_Ψ₂ : LinearMap.ker (Ψ₂ k) = Rel k :=
  le_antisymm (ker_le_Rel k) (Rel_le_ker k)

theorem card_sym2 : Fintype.card (Sym2 (Fin 251)) = 31626 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right]

/-- **Degree-two Hilbert value** in terms of the relation space, over every field. -/
theorem hilbertValue_two_add : hilbertValue k (A k) 2 + Module.finrank k (Rel k) = 31626 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Ψ₂ k)
  rw [range_Ψ₂, ker_Ψ₂, Module.finrank_fintype_fun_eq_card, card_sym2] at h
  exact h

end Brent.HilbertTwo
