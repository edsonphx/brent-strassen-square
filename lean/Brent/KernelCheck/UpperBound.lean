import Brent.TriangularBound
import Brent.DualFrame
import Brent.KernelCheck.CharThreeData

/-!
# The upper bound `dim ≤ 197` in characteristic three

Over a field of characteristic three, the 54 certified covectors give 54 quadratic relations
among 251 tangent coordinates `z = (c, x, y)` in the Brent local ring, modulo `𝔪³`. Their
mixed coefficient tables are lexicographically triangular with coefficient-one leaders
`x_ℓ y_{π(ℓ)}`. With the 197 parameters `c` and `u_ℓ(y) - x_ℓ`, where `u_ℓ` is the
leading row of the `ℓ`-th table, every square `x_ℓ²` reduces to larger indices. The
triangular monomial reduction then gives `𝔪⁵⁵ ⊆ (parameters) + 𝔪⁵⁶`, and Krull's height
theorem gives `dim ≤ 197`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.UpperBound

open TangentData QuadraticData CharThree

variable (k : Type) [Field k]

abbrev A := PointLocalRing (strassenSquare k) (strassenSquare_solves k)

noncomputable abbrev φ := toPointLocalRing (strassenSquare k) (strassenSquare_solves k)

noncomputable abbrev M0 : Ideal (MvPolynomial (Variable SquareVertex SquareSummand) k) :=
  RingHom.ker (eval (strassenSquare k).coordinates)

noncomputable abbrev J (x : Variable SquareVertex SquareSummand) (e : EquationIndex SquareVertex) : k :=
  (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2

/-! ### Polynomial facts -/

theorem translated_mem (x : Variable SquareVertex SquareSummand) :
    (strassenSquare k).translated.coordinates x ∈ M0 k := by
  rw [Decomposition.translated_coordinates, M0, ker_eval_eq_span]
  exact Ideal.subset_span ⟨x, rfl⟩

theorem mul_mem_sq {f g : MvPolynomial (Variable SquareVertex SquareSummand) k}
    (hf : f ∈ M0 k) (hg : g ∈ M0 k) : f * g ∈ M0 k ^ 2 := by
  rw [pow_two]; exact Ideal.mul_mem_mul hf hg

theorem quad_mem (e : EquationIndex SquareVertex) :
    (strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 ∈
      M0 k ^ 2 := by
  have hu : ∀ s a, (strassenSquare k).translated.u s a ∈ M0 k := fun s a => translated_mem k (s, .u, a)
  have hv : ∀ s a, (strassenSquare k).translated.v s a ∈ M0 k := fun s a => translated_mem k (s, .v, a)
  have hw : ∀ s a, (strassenSquare k).translated.w s a ∈ M0 k := fun s a => translated_mem k (s, .w, a)
  simp only [Decomposition.quadraticEntry]
  refine Submodule.sum_mem _ fun s _ => ?_
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mul_mem_right _ _ (mul_mem_sq k (hu s _) (hv s _))
  · rw [mul_right_comm]; exact Ideal.mul_mem_right _ _ (mul_mem_sq k (hu s _) (hw s _))
  · rw [mul_assoc]; exact Ideal.mul_mem_left _ _ (mul_mem_sq k (hv s _) (hw s _))

theorem cubic_mem (e : EquationIndex SquareVertex) :
    (strassenSquare k).translated.entry e.1 e.2.1 e.2.2 ∈ M0 k ^ 3 := by
  simp only [Decomposition.entry]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [pow_succ]
  exact Ideal.mul_mem_mul (mul_mem_sq k (translated_mem k (s, .u, _)) (translated_mem k (s, .v, _)))
    (translated_mem k (s, .w, _))

theorem jac_poly (e : EquationIndex SquareVertex) :
    (strassenSquare k |>.map C).jacobianEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 =
      ∑ x, (X x - C ((strassenSquare k).coordinates x)) * C (J k x e) := by
  rw [Decomposition.jacobianEntry_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Decomposition.translated_coordinates, Decomposition.jacobianColumn_map]

theorem equation_mem (e : EquationIndex SquareVertex) :
    equation k SquareVertex SquareSummand e.1 e.2.1 e.2.2 ∈ brentIdeal k SquareVertex SquareSummand :=
  Ideal.subset_span ⟨e, rfl⟩

/-! ### The local ring -/

theorem φ_brent {g : MvPolynomial (Variable SquareVertex SquareSummand) k}
    (hg : g ∈ brentIdeal k SquareVertex SquareSummand) : φ k g = 0 := by
  rw [toPointLocalRing_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]

theorem φ_pow {n : ℕ} {g : MvPolynomial (Variable SquareVertex SquareSummand) k}
    (hg : g ∈ M0 k ^ n) : φ k g ∈ maximalIdeal (A k) ^ n := by
  rw [maximalIdeal_pointLocalRing, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hg

theorem φ_sup {n : ℕ} {g : MvPolynomial (Variable SquareVertex SquareSummand) k}
    (hg : g ∈ brentIdeal k SquareVertex SquareSummand ⊔ M0 k ^ n) :
    φ k g ∈ maximalIdeal (A k) ^ n := by
  have hle : brentIdeal k SquareVertex SquareSummand ⊔ M0 k ^ n ≤
      (maximalIdeal (A k) ^ n).comap (φ k) := by
    refine sup_le (fun g hg => ?_) (fun g hg => φ_pow k hg)
    rw [Ideal.mem_comap, φ_brent k hg]
    exact Ideal.zero_mem _
  exact hle hg

/-- The translated coordinates in the local ring. -/
noncomputable def y (x : Variable SquareVertex SquareSummand) : A k :=
  φ k (X x - C ((strassenSquare k).coordinates x))

theorem maximalIdeal_eq : maximalIdeal (A k) = Ideal.span (Set.range (y k)) := by
  rw [maximalIdeal_pointLocalRing, ker_eval_eq_span, Ideal.map_span, ← Set.range_comp]
  rfl

theorem y_mem (x : Variable SquareVertex SquareSummand) : y k x ∈ maximalIdeal (A k) := by
  rw [maximalIdeal_eq]; exact Ideal.subset_span ⟨x, rfl⟩

noncomputable def Ψ : (Variable SquareVertex SquareSummand → k) →ₗ[k] A k :=
  Fintype.linearCombination k (y k)

theorem Ψ_mem (c : Variable SquareVertex SquareSummand → k) : Ψ k c ∈ maximalIdeal (A k) := by
  rw [Ψ, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_of_tower_mem _ _ (y_mem k x)

theorem Ψ_poly (c : Variable SquareVertex SquareSummand → k) :
    Ψ k c = φ k (∑ x, (X x - C ((strassenSquare k).coordinates x)) * C (c x)) := by
  rw [Ψ, Fintype.linearCombination_apply, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, Algebra.smul_def, mul_comm, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rfl

theorem row_mem (e : EquationIndex SquareVertex) :
    Ψ k (fun x => J k x e) ∈ maximalIdeal (A k) ^ 2 := by
  rw [Ψ_poly, ← jac_poly]
  have h := Decomposition.equation_eq_expansion (strassenSquare_solves k) e.1 e.2.1 e.2.2
  have h' : (strassenSquare k |>.map C).jacobianEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 =
      equation k SquareVertex SquareSummand e.1 e.2.1 e.2.2 -
      ((strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 +
        (strassenSquare k).translated.entry e.1 e.2.1 e.2.2) := by
    rw [h]; ring
  rw [h']
  refine φ_sup k (Ideal.sub_mem _ (Ideal.mem_sup_left (equation_mem k e))
    (Ideal.mem_sup_right (Ideal.add_mem _ (quad_mem k e) ?_)))
  exact Ideal.pow_le_pow_right (by norm_num) (cubic_mem k e)

theorem Ψ_rowSpace {r : Variable SquareVertex SquareSummand → k} (hr : r ∈ rowSpace k) :
    Ψ k r ∈ maximalIdeal (A k) ^ 2 := by
  induction hr using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, rfl⟩ := hz
    exact row_mem k e
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_of_tower_mem _ _ ha

/-! ### Tangent coordinates -/

theorem exists_coordinates : ∃ w : Fin 251 → Variable SquareVertex SquareSummand → k,
    ∀ x, Pi.single x 1 - ∑ i, frameVec k i x • w i ∈ rowSpace k := by
  apply exists_dual_frame (rowSpace k) (frameVec k) (frame_independent k)
  · intro r hr i
    induction hr using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      exact frame_orthogonal k i e
    | zero => simp
    | add a b _ _ ha hb => simp [mul_add, Finset.sum_add_distrib, ha, hb]
    | smul c a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show ∑ x, frameVec k i x * (c * a x) = c * ∑ x, frameVec k i x * a x by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring, ha, mul_zero]
  · rw [rowSpace_finrank, square_variable_count]

/-! ### Quadratic relations in characteristic three -/

section Covector

theorem lam_jac_zero (ν : EquationIndex SquareVertex → k)
    (hν : ∀ x, ∑ e : EquationIndex SquareVertex, J k x e * ν e = 0) :
    ∑ e : EquationIndex SquareVertex, C (ν e) *
      (strassenSquare k |>.map C).jacobianEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 = 0 := by
  simp only [jac_poly, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  have h : ∑ e : EquationIndex SquareVertex, C (ν e) *
      ((X x - C ((strassenSquare k).coordinates x)) * C (J k x e)) =
      (X x - C ((strassenSquare k).coordinates x)) *
        C (∑ e : EquationIndex SquareVertex, J k x e * ν e) := by
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_mul]; ring
  rw [h, hν, map_zero, mul_zero]

theorem quad_rel_poly (ν : EquationIndex SquareVertex → k)
    (hν : ∀ x, ∑ e : EquationIndex SquareVertex, J k x e * ν e = 0) :
    ∑ e : EquationIndex SquareVertex, C (ν e) *
      (strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 ∈
      brentIdeal k SquareVertex SquareSummand ⊔ M0 k ^ 3 := by
  have hsplit : ∑ e : EquationIndex SquareVertex, C (ν e) *
      (strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 =
      ∑ e : EquationIndex SquareVertex, C (ν e) *
        equation k SquareVertex SquareSummand e.1 e.2.1 e.2.2 -
      ∑ e : EquationIndex SquareVertex, C (ν e) *
        (strassenSquare k |>.map C).jacobianEntry (strassenSquare k).translated e.1 e.2.1 e.2.2 -
      ∑ e : EquationIndex SquareVertex, C (ν e) *
        (strassenSquare k).translated.entry e.1 e.2.1 e.2.2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [Decomposition.equation_eq_expansion (strassenSquare_solves k)]
    ring
  rw [hsplit, lam_jac_zero k ν hν, sub_zero]
  refine Ideal.sub_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · exact Submodule.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ (equation_mem k e)
  · exact Submodule.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ (cubic_mem k e)

theorem φ_C (c : k) : φ k (C c) = algebraMap k (A k) c := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

/-- The base point in the local ring. -/
noncomputable abbrev P : Decomposition (A k) SquareVertex SquareSummand :=
  (strassenSquare k).map (algebraMap k (A k))

/-- The generic translated point in the local ring. -/
noncomputable abbrev Y : Decomposition (A k) SquareVertex SquareSummand :=
  (strassenSquare k).translated.map (φ k).toRingHom

theorem φ_quadratic (e : EquationIndex SquareVertex) :
    φ k ((strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated e.1 e.2.1 e.2.2) =
      (P k).quadraticEntry (Y k) e.1 e.2.1 e.2.2 := by
  have hP : (strassenSquare k |>.map C).map (φ k).toRingHom = P k := by
    rw [Decomposition.map_map']
    congr 1
  rw [Decomposition.quadraticEntry_eq_bilinear, Decomposition.quadraticEntry_eq_bilinear, ← hP,
    Decomposition.bilinearEntry_map]
  rfl

theorem quad_rel_local (ν : EquationIndex SquareVertex → k)
    (hν : ∀ x, ∑ e : EquationIndex SquareVertex, J k x e * ν e = 0) :
    ∑ e : EquationIndex SquareVertex, algebraMap k (A k) (ν e) *
      (P k).quadraticEntry (Y k) e.1 e.2.1 e.2.2 ∈ maximalIdeal (A k) ^ 3 := by
  have h := φ_sup k (quad_rel_poly k ν hν)
  rw [map_sum] at h
  convert h using 2 with e _
  rw [map_mul, φ_C, φ_quadratic]

/-! ### The tangent coordinates `z` -/

/-- Dual vectors to the certified tangent frame. -/
noncomputable def wv : Fin 251 → Variable SquareVertex SquareSummand → k :=
  Classical.choose (exists_coordinates k)

/-- The 251 tangent coordinates in the local ring. -/
noncomputable def z (i : Fin 251) : A k := Ψ k (wv k i)

theorem z_mem (i : Fin 251) : z k i ∈ maximalIdeal (A k) := Ψ_mem k _

theorem Ψ_single (x : Variable SquareVertex SquareSummand) : Ψ k (Pi.single x 1) = y k x := by
  rw [Ψ, Fintype.linearCombination_apply_single, one_smul]

theorem y_sub_mem (x : Variable SquareVertex SquareSummand) :
    y k x - ∑ i, z k i * algebraMap k (A k) (frameVec k i x) ∈ maximalIdeal (A k) ^ 2 := by
  have h := Ψ_rowSpace k (Classical.choose_spec (exists_coordinates k) x)
  rw [map_sub, map_sum, Ψ_single] at h
  convert h using 3 with i _
  rw [map_smul, Algebra.smul_def, mul_comm]
  rfl

/-- The certified frame as directions in the local ring. -/
noncomputable abbrev V (i : Fin 251) : Decomposition (A k) SquareVertex SquareSummand :=
  (frameDirection k i).map (algebraMap k (A k))

/-- The tangent approximation of the generic point. -/
noncomputable abbrev Z : Decomposition (A k) SquareVertex SquareSummand :=
  Decomposition.lc (z k) (V k)

theorem lc_coordinates {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R)
    (D : Fin n → Decomposition R SquareVertex SquareSummand) (x : Variable SquareVertex SquareSummand) :
    (Decomposition.lc c D).coordinates x = ∑ i, c i * (D i).coordinates x := by
  obtain ⟨s, m, a⟩ := x; cases m <;> rfl

theorem map_coordinates {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (D : Decomposition R SquareVertex SquareSummand) (x : Variable SquareVertex SquareSummand) :
    (D.map f).coordinates x = f (D.coordinates x) := by
  obtain ⟨s, m, a⟩ := x; cases m <;> rfl

theorem Y_coordinates (x : Variable SquareVertex SquareSummand) :
    (Y k).coordinates x = y k x := by
  rw [map_coordinates, Decomposition.translated_coordinates]
  rfl

theorem Z_coordinates (x : Variable SquareVertex SquareSummand) :
    (Z k).coordinates x = ∑ i, z k i * algebraMap k (A k) (frameVec k i x) := by
  rw [lc_coordinates]
  simp only [map_coordinates, frameVec]

theorem components {R : Type*} [CommRing R] {I : Ideal R}
    {D : Decomposition R SquareVertex SquareSummand}
    (h : ∀ x, D.coordinates x ∈ I) : ∀ s a, D.u s a ∈ I ∧ D.v s a ∈ I ∧ D.w s a ∈ I :=
  fun s a => ⟨h (s, .u, a), h (s, .v, a), h (s, .w, a)⟩

theorem components_sub {R : Type*} [CommRing R] {I : Ideal R}
    {D E : Decomposition R SquareVertex SquareSummand}
    (h : ∀ x, D.coordinates x - E.coordinates x ∈ I) :
    ∀ s a, D.u s a - E.u s a ∈ I ∧ D.v s a - E.v s a ∈ I ∧ D.w s a - E.w s a ∈ I :=
  fun s a => ⟨h (s, .u, a), h (s, .v, a), h (s, .w, a)⟩

theorem Z_mem (x : Variable SquareVertex SquareSummand) :
    (Z k).coordinates x ∈ maximalIdeal (A k) := by
  rw [Z_coordinates]
  exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (z_mem k i)

theorem sum_mul_mem_of_sub {R ι : Type*} [CommRing R] [Fintype ι] (m : Ideal R) (c f g : ι → R)
    (hf : ∑ i, c i * f i ∈ m) (hfg : ∀ i, f i - g i ∈ m) : ∑ i, c i * g i ∈ m := by
  have e : ∑ i, c i * g i = ∑ i, c i * f i - ∑ i, c i * (f i - g i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact Ideal.sub_mem _ hf (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hfg i))

theorem quad_rel_Z (ν : EquationIndex SquareVertex → k)
    (hν : ∀ x, ∑ e : EquationIndex SquareVertex, J k x e * ν e = 0) :
    ∑ e : EquationIndex SquareVertex, algebraMap k (A k) (ν e) *
      (P k).quadraticEntry (Z k) e.1 e.2.1 e.2.2 ∈ maximalIdeal (A k) ^ 3 := by
  have hY : ∀ s a, (Y k).u s a ∈ maximalIdeal (A k) ∧ (Y k).v s a ∈ maximalIdeal (A k) ∧
      (Y k).w s a ∈ maximalIdeal (A k) :=
    components (D := Y k) fun x => by rw [Y_coordinates]; exact y_mem k x
  have hZ : ∀ s a, (Z k).u s a ∈ maximalIdeal (A k) ∧ (Z k).v s a ∈ maximalIdeal (A k) ∧
      (Z k).w s a ∈ maximalIdeal (A k) :=
    components (D := Z k) (Z_mem k)
  have hYZ := components_sub (D := Y k) (E := Z k) (I := maximalIdeal (A k) ^ 2)
    fun x => by rw [Y_coordinates, Z_coordinates]; exact y_sub_mem k x
  have hq := Decomposition.quadraticEntry_sub_mem (maximalIdeal (A k)) (P k) (Y k) (Z k) hY hZ
  exact sum_mul_mem_of_sub (maximalIdeal (A k) ^ 3) (fun e => algebraMap k (A k) (ν e))
    (fun e => (P k).quadraticEntry (Y k) e.1 e.2.1 e.2.2)
    (fun e => (P k).quadraticEntry (Z k) e.1 e.2.1 e.2.2) (quad_rel_local k ν hν)
    (fun e => hq hYZ e.1 e.2.1 e.2.2)

/-- The bilinear values of the covectors on the frame. -/
noncomputable def β (ν : EquationIndex SquareVertex → k) (i j : Fin 251) : k :=
  ∑ e : EquationIndex SquareVertex,
    (strassenSquare k).bilinearEntry (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2 *
      ν e

theorem expand (ν : EquationIndex SquareVertex → k) :
    ∑ e : EquationIndex SquareVertex, algebraMap k (A k) (ν e) *
      (P k).quadraticEntry (Z k) e.1 e.2.1 e.2.2 =
      ∑ i, ∑ j, z k i * z k j * algebraMap k (A k) (β k ν i j) := by
  simp only [Decomposition.quadraticEntry_lc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [β, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Decomposition.bilinearEntry_map, map_mul]
  ring

/-! ### The mixed block and its leading terms -/

theorem xFrameIndex_injective : Function.Injective xFrameIndex := by
  intro a b h
  have := congrArg Fin.val h
  simp only [xFrameIndex] at this
  exact Fin.ext (by omega)

theorem yFrameIndex_injective : Function.Injective yFrameIndex := by
  intro a b h
  have := congrArg Fin.val h
  simp only [yFrameIndex] at this
  exact Fin.ext (by omega)

/-- The `x` coordinates. -/
noncomputable def xs (a : Fin 54) : A k := z k (xFrameIndex a)

/-- The `y` coordinates. -/
noncomputable def ys (b : Fin 54) : A k := z k (yFrameIndex b)

/-- The 143 coordinates outside the mixed block. -/
noncomputable def cs (i : Fin 143) : A k := z k (Fin.castLE (by norm_num) i)

theorem z_mem_gen (i : Fin 251) : z k i ∈ Ideal.span (Set.range (cs k)) ⊔
    Ideal.span (Set.range (xs k)) ⊔ Ideal.span (Set.range (ys k)) := by
  by_cases h1 : i.val < 143
  · have : z k i = cs k ⟨i.val, h1⟩ := rfl
    rw [this]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨_, rfl⟩))
  by_cases h2 : i.val < 197
  · have hi : i = xFrameIndex ⟨i.val - 143, by omega⟩ :=
      Fin.ext (by simp only [xFrameIndex]; omega)
    have : z k i = xs k ⟨i.val - 143, by omega⟩ := by rw [xs, ← hi]
    rw [this]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨_, rfl⟩))
  · have hi : i = yFrameIndex ⟨i.val - 197, by have := i.isLt; omega⟩ :=
      Fin.ext (by simp only [yFrameIndex]; omega)
    have : z k i = ys k ⟨i.val - 197, by have := i.isLt; omega⟩ := by rw [ys, ← hi]
    rw [this]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨_, rfl⟩)

theorem gen : maximalIdeal (A k) ≤ Ideal.span (Set.range (cs k)) ⊔
    Ideal.span (Set.range (xs k)) ⊔ Ideal.span (Set.range (ys k)) ⊔ maximalIdeal (A k) ^ 2 := by
  have h : Ideal.span (Set.range (y k)) ≤ Ideal.span (Set.range (cs k)) ⊔
      Ideal.span (Set.range (xs k)) ⊔ Ideal.span (Set.range (ys k)) ⊔
        maximalIdeal (A k) ^ 2 := by
    rw [Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    have hr := Classical.choose_spec (exists_coordinates k) x
    have e : (Pi.single x 1 : Variable SquareVertex SquareSummand → k) =
        (Pi.single x 1 - ∑ i, frameVec k i x • wv k i) + ∑ i, frameVec k i x • wv k i :=
      (sub_add_cancel _ _).symm
    rw [← Ψ_single, e, map_add, map_sum]
    refine Ideal.add_mem _ (Ideal.mem_sup_right (Ψ_rowSpace k hr))
      (Ideal.mem_sup_left (Submodule.sum_mem _ fun i _ => ?_))
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (z_mem_gen k i)
  rwa [← maximalIdeal_eq] at h

end Covector

/-! ### Characteristic three -/

section CharThree

variable [CharP k 3]

theorem β_diag (ell : Fin 54) (i : Fin 251) : β k (lam k ell) i i = 0 := by
  rw [β, ← square_value k ell i]
  simp only [Decomposition.quadraticEntry_eq_bilinear]

theorem β_polar (ell : Fin 54) (i j : Fin 251) :
    β k (lam k ell) i j + β k (lam k ell) j i = castK k (projectedPolar ell i j) := by
  rw [β, β, ← polar_value, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [Decomposition.polarizedEntry_eq_bilinear]
  ring

theorem ordered_rel (ell : Fin 54) :
    ∑ i, ∑ j, (if i < j then z k i * z k j *
      algebraMap k (A k) (castK k (projectedPolar ell i j)) else 0) ∈ maximalIdeal (A k) ^ 3 := by
  have h := quad_rel_Z k (lam k ell) (annihilate k ell)
  rw [expand, sum_sum_eq_ordered (R := A k)] at h
  convert h using 4 with i _ j _
  · rw [← β_polar, map_add]; ring
  · split_ifs with h2
    · subst h2; rw [β_diag, map_zero, mul_zero]
    · rfl

/-- The mixed coefficient tables in the local ring. -/
noncomputable def Mc (ell a b : Fin 54) : A k :=
  algebraMap k (A k) (castK k (projectedPolar ell (xFrameIndex a) (yFrameIndex b)))

theorem mixed_rel (ell : Fin 54) :
    ∑ a, ∑ b, xs k a * ys k b * Mc k ell a b ∈ maximalIdeal (A k) ^ 3 := by
  have h := ordered_rel k ell
  have hx : ∀ i : Fin 251, (∀ a, xFrameIndex a ≠ i) → ¬ (143 ≤ i.val ∧ i.val < 197) := by
    intro i hi ⟨h1, h2⟩
    exact hi ⟨i.val - 143, by omega⟩ (Fin.ext (by simp only [xFrameIndex]; omega))
  have hy : ∀ j : Fin 251, (∀ b, yFrameIndex b ≠ j) → ¬ (197 ≤ j.val) := by
    intro j hj h1
    exact hj ⟨j.val - 197, by have := j.isLt; omega⟩ (Fin.ext (by simp only [yFrameIndex]; omega))
  have hG : ∀ i j : Fin 251, ¬ (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) →
      (if i < j then z k i * z k j *
        algebraMap k (A k) (castK k (projectedPolar ell i j)) else 0) = 0 := by
    intro i j hij
    split_ifs with hlt
    · rw [archived_nonmixed_zero ell i j ?_, map_zero, map_zero, mul_zero]
      rintro (h' | h')
      · exact hij h'
      · have : i.val < j.val := hlt
        omega
    · rfl
  rw [sum_comp_of_zero _ xFrameIndex xFrameIndex_injective
    (fun i hi => Finset.sum_eq_zero fun j _ => hG _ _ fun hh => hx i hi ⟨hh.1, hh.2.1⟩)] at h
  have e : ∀ a, ∑ b, xs k a * ys k b * Mc k ell a b = ∑ j, (if xFrameIndex a < j then
      z k (xFrameIndex a) * z k j *
        algebraMap k (A k) (castK k (projectedPolar ell (xFrameIndex a) j)) else 0) := by
    intro a
    rw [sum_comp_of_zero _ yFrameIndex yFrameIndex_injective
      (fun j hj => hG _ _ fun hh => hy j hj hh.2.2)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hlt : xFrameIndex a < yFrameIndex b := by
      show (xFrameIndex a).val < (yFrameIndex b).val
      simp only [xFrameIndex, yFrameIndex]
      omega
    rw [if_pos hlt]
    rfl
  rw [Finset.sum_congr rfl fun a _ => e a]
  exact h

theorem Mc_lead (ell : Fin 54) : Mc k ell ell (quadraticMatching ell) = 1 := by
  rw [Mc, (archived_polar_leading ell).1, map_one, map_one]

theorem Mc_zero (ell a b : Fin 54)
    (h : 54 * a.val + b.val < 54 * ell.val + (quadraticMatching ell).val) : Mc k ell a b = 0 := by
  rw [Mc, (archived_polar_leading ell).2 a b h, map_zero, map_zero]

theorem ringKrullDim_le : ringKrullDim (A k) ≤ ((143 + 54 : ℕ) : WithBot ℕ∞) :=
  triangular_dim_le (cs k) (xs k) (ys k) (Mc k) quadraticMatching
    quadraticMatching_bijective.2 (fun _ => z_mem k _) (fun _ => z_mem k _) (fun _ => z_mem k _)
    (gen k) (mixed_rel k) (Mc_lead k) (Mc_zero k)

/-- **Upper bound.** Over a field of characteristic three, `dim_p V(4,4,4 | 49) ≤ 197`. -/
theorem squareLocalDimension_le_197 : squareLocalDimension k ≤ 197 := by
  have h := ringKrullDim_le k
  exact h

end CharThree

end Brent.UpperBound
