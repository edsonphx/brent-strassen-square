import Brent.SecondJet
import Brent.KernelCheck.HilbertInitial

/-!
# Second-order points of the Brent local ring

For a symmetric table `T` on the 251 frame directions and a vector `W` with
`J W + Σ T(i,j) B(vᵢ, vⱼ) = 0`, the point `p + Σ tᵢ vᵢ + η W` solves the Brent equations
over the second-order jet ring of `T`. It induces a local homomorphism from the Brent local
ring that sends the tangent coordinate `zᵢ` to `tᵢ + ωᵢ η`, so `zᵢ zⱼ ↦ T(i,j) η`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.SecondOrder

open TangentData QuadraticData CharThree UpperBound SecondJet

variable (k : Type) [Field k]

/-! ### Duality of the tangent coordinates and the frame -/

theorem frame_orthogonal_row {r : Variable SquareVertex SquareSummand → k} (hr : r ∈ rowSpace k)
    (i : Fin 251) : ∑ x, frameVec k i x * r x = 0 := by
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

theorem dual_pairing (i j : Fin 251) :
    ∑ x, wv k i x * frameVec k j x = if i = j then 1 else 0 := by
  have hspec := Classical.choose_spec (exists_coordinates k)
  -- `vⱼ(x) = Σᵢ vᵢ(x) ⟨wᵢ, vⱼ⟩` for every `x`.
  have hx : ∀ x, frameVec k j x - ∑ i, frameVec k i x * ∑ y, wv k i y * frameVec k j y = 0 := by
    intro x
    have h := frame_orthogonal_row k (hspec x) j
    rw [← h]
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [wv]; ring
  have hlin := Fintype.linearIndependent_iff.mp (frame_independent k)
    (fun i => (if i = j then 1 else 0) - ∑ y, wv k i y * frameVec k j y) (by
      funext x
      have := hx x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply]
      rw [← this]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
  have := hlin i
  rw [sub_eq_zero] at this
  exact this.symm

/-! ### The second-order point -/

variable {k} (T : Sym2 (Fin 251) → k) (W : Variable SquareVertex SquareSummand → k)

/-- The value of the point at a coordinate. -/
noncomputable def pointValue (x : Variable SquareVertex SquareSummand) : SecondJet T :=
  ⟨(strassenSquare k).coordinates x, fun i => frameVec k i x, W x⟩

/-- Evaluation at the second-order point. -/
noncomputable def polyPoint : MvPolynomial (Variable SquareVertex SquareSummand) k →+* SecondJet T :=
  eval₂Hom (const T) (pointValue T W)

/-- The `a`-component as a ring homomorphism. -/
def aHom : SecondJet T →+* k where
  toFun x := x.a
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `c`-component as an additive map. -/
def cHom : SecondJet T →+ k where
  toFun x := x.c
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `u`-component as an additive map. -/
def uHom : SecondJet T →+ (Fin 251 → k) where
  toFun x := x.u
  map_zero' := rfl
  map_add' _ _ := rfl

theorem aHom_polyPoint (g : MvPolynomial (Variable SquareVertex SquareSummand) k) :
    aHom T (polyPoint T W g) = eval (strassenSquare k).coordinates g := by
  have h : (aHom T).comp (polyPoint T W) = eval (strassenSquare k).coordinates := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [polyPoint, aHom]
    · intro x; simp [polyPoint, aHom, pointValue]
  exact congrArg (fun f => f g) h

theorem sub_a (x y : SecondJet T) : (x - y).a = x.a - y.a := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; rfl
theorem sub_u (x y : SecondJet T) : (x - y).u = x.u - y.u := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; rfl
theorem sub_c (x y : SecondJet T) : (x - y).c = x.c - y.c := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; rfl

/-- The image of a translated coordinate. -/
theorem polyPoint_lin (x : Variable SquareVertex SquareSummand) :
    polyPoint T W (X x - C ((strassenSquare k).coordinates x)) =
      ⟨0, fun i => frameVec k i x, W x⟩ := by
  rw [map_sub, polyPoint, eval₂Hom_X', eval₂Hom_C]
  ext
  · simp [sub_a, pointValue]
  · simp [sub_u, pointValue]
  · simp [sub_c, pointValue]

theorem mk_mul_const (t r : k) : (⟨0, 0, t⟩ : SecondJet T) * const T r = ⟨0, 0, t * r⟩ := by
  ext <;> simp [bil_zero_left]; ring

theorem mk_mul_mk (u u' : Fin 251 → k) (c c' : k) :
    (⟨0, u, c⟩ : SecondJet T) * ⟨0, u', c'⟩ = ⟨0, 0, bil T u u'⟩ := by
  ext <;> simp

theorem const_mul_mk (r : k) (u : Fin 251 → k) (c : k) :
    const T r * ⟨0, u, c⟩ = ⟨0, r • u, r * c⟩ := by
  ext <;> simp [bil_zero_left]

theorem mk_mul_const' (r : k) (u : Fin 251 → k) (c : k) :
    (⟨0, u, c⟩ : SecondJet T) * const T r = ⟨0, r • u, r * c⟩ := by
  rw [mul_comm, const_mul_mk]

theorem sum_a {ι : Type*} (s : Finset ι) (f : ι → SecondJet T) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (aHom T) f s
theorem sum_u {ι : Type*} (s : Finset ι) (f : ι → SecondJet T) : (∑ i ∈ s, f i).u = ∑ i ∈ s, (f i).u :=
  map_sum (uHom T) f s
theorem sum_c {ι : Type*} (s : Finset ι) (f : ι → SecondJet T) : (∑ i ∈ s, f i).c = ∑ i ∈ s, (f i).c :=
  map_sum (cHom T) f s

/-- Second-order terms with vanishing constant parts. -/
def mkc : k →+ SecondJet T where
  toFun t := ⟨0, 0, t⟩
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

@[simp] theorem mkc_a (t : k) : (mkc T t).a = 0 := rfl
@[simp] theorem mkc_u (t : k) : (mkc T t).u = 0 := rfl
@[simp] theorem mkc_c (t : k) : (mkc T t).c = t := rfl

theorem dirValue (x : Variable SquareVertex SquareSummand) :
    polyPoint T W ((strassenSquare k).translated.coordinates x) =
      ⟨0, fun i => frameVec k i x, W x⟩ := by
  rw [Decomposition.translated_coordinates, polyPoint_lin]

theorem bil_frame (r : k) (x y : Variable SquareVertex SquareSummand) :
    bil T (r • fun i => frameVec k i x) (fun i => frameVec k i y) =
      ∑ i, ∑ j, T s(i, j) * (r * frameVec k i x * frameVec k j y) := by
  simp only [bil, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem summand_value (s : SquareSummand) (a b c : SquareVertex × SquareVertex) :
    polyPoint T W ((strassenSquare k).translated.u s a * (strassenSquare k).translated.v s b *
        C ((strassenSquare k).w s c) +
      (strassenSquare k).translated.u s a * C ((strassenSquare k).v s b) *
        (strassenSquare k).translated.w s c +
      C ((strassenSquare k).u s a) * (strassenSquare k).translated.v s b *
        (strassenSquare k).translated.w s c) =
    mkc T (∑ i, ∑ j, T s(i, j) *
      ((frameDirection k i).u s a * (frameDirection k j).v s b * (strassenSquare k).w s c +
        (frameDirection k i).u s a * (strassenSquare k).v s b * (frameDirection k j).w s c +
        (strassenSquare k).u s a * (frameDirection k i).v s b * (frameDirection k j).w s c)) := by
  have hu : ∀ q, polyPoint T W ((strassenSquare k).translated.u s q) =
      ⟨0, fun i => (frameDirection k i).u s q, W (s, .u, q)⟩ := fun q => dirValue T W (s, .u, q)
  have hv : ∀ q, polyPoint T W ((strassenSquare k).translated.v s q) =
      ⟨0, fun i => (frameDirection k i).v s q, W (s, .v, q)⟩ := fun q => dirValue T W (s, .v, q)
  have hw : ∀ q, polyPoint T W ((strassenSquare k).translated.w s q) =
      ⟨0, fun i => (frameDirection k i).w s q, W (s, .w, q)⟩ := fun q => dirValue T W (s, .w, q)
  have hC : ∀ r, polyPoint T W (C r) = const T r := fun r => eval₂Hom_C _ _ _
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hu, hv, hw, hC, hC,
    hC]
  ext
  · rw [mkc_a]; simp
  · rw [mkc_u]; simp
  · rw [mkc_c]
    simp only [add_c, mul_c, mul_a, mul_u, const_a,
      const_u, const_c, bil, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      zero_mul, add_zero, zero_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem polyPoint_quadratic (a b c : SquareVertex × SquareVertex) :
    polyPoint T W ((strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated a b c) =
      mkc T (∑ i, ∑ j, T s(i, j) *
        (strassenSquare k).bilinearEntry (frameDirection k i) (frameDirection k j) a b c) := by
  have e : (strassenSquare k |>.map C).quadraticEntry (strassenSquare k).translated a b c =
      ∑ s, ((strassenSquare k).translated.u s a * (strassenSquare k).translated.v s b *
        C ((strassenSquare k).w s c) +
      (strassenSquare k).translated.u s a * C ((strassenSquare k).v s b) *
        (strassenSquare k).translated.w s c +
      C ((strassenSquare k).u s a) * (strassenSquare k).translated.v s b *
        (strassenSquare k).translated.w s c) := rfl
  rw [e, map_sum]
  simp only [summand_value, ← map_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Decomposition.bilinearEntry, Finset.mul_sum]

theorem polyPoint_cubic (a b c : SquareVertex × SquareVertex) :
    polyPoint T W ((strassenSquare k).translated.entry a b c) = 0 := by
  simp only [Decomposition.entry, map_sum, map_mul]
  refine Finset.sum_eq_zero fun s _ => ?_
  exact mul_mul_eq_zero T (by rw [show (strassenSquare k).translated.u s a =
      (strassenSquare k).translated.coordinates (s, .u, a) from rfl, dirValue])
    (by rw [show (strassenSquare k).translated.v s b =
      (strassenSquare k).translated.coordinates (s, .v, b) from rfl, dirValue])
    (by rw [show (strassenSquare k).translated.w s c =
      (strassenSquare k).translated.coordinates (s, .w, c) from rfl, dirValue])

theorem polyPoint_jacobian (e : EquationIndex SquareVertex) :
    polyPoint T W ((strassenSquare k |>.map C).jacobianEntry (strassenSquare k).translated
      e.1 e.2.1 e.2.2) = mkc T (∑ x, J k x e * W x) := by
  rw [jac_poly k e, map_sum]
  have h : ∀ x, polyPoint T W ((X x - C ((strassenSquare k).coordinates x)) * C (J k x e)) =
      ⟨0, J k x e • fun i => frameVec k i x, J k x e * W x⟩ := by
    intro x
    rw [map_mul, polyPoint_lin, polyPoint, eval₂Hom_C, mk_mul_const']
  simp only [h]
  ext
  · rw [mkc_a, sum_a]; simp
  · rw [mkc_u, sum_u]
    rename_i i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact HilbertInitial.frame_tangent k i e
  · rw [mkc_c, sum_c]

/-- The admissibility condition for `W`. -/
def Admissible : Prop :=
  ∀ e : EquationIndex SquareVertex, ∑ x, J k x e * W x +
    ∑ i, ∑ j, T s(i, j) *
      (strassenSquare k).bilinearEntry (frameDirection k i) (frameDirection k j) e.1 e.2.1 e.2.2 = 0

variable {T W}

theorem polyPoint_brent (hW : Admissible T W) :
    brentIdeal k SquareVertex SquareSummand ≤ RingHom.ker (polyPoint T W) := by
  rw [brentIdeal, Ideal.span_le]
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  have h := Decomposition.equation_eq_expansion (strassenSquare_solves k) a b c
  change polyPoint T W (equation k SquareVertex SquareSummand a b c) = 0
  rw [h, map_add, map_add, polyPoint_jacobian T W (a, b, c), polyPoint_quadratic, polyPoint_cubic,
    add_zero, ← map_add, hW (a, b, c), map_zero]

/-- The second-order point on the coordinate ring. -/
noncomputable def quotPoint (hW : Admissible T W) :
    CoordinateRing k SquareVertex SquareSummand →+* SecondJet T :=
  Ideal.Quotient.lift (brentIdeal k SquareVertex SquareSummand) (polyPoint T W)
    fun g hg => polyPoint_brent hW hg

theorem quotPoint_unit (hW : Admissible T W)
    (s : (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl) :
    IsUnit (quotPoint hW s) := by
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (s : CoordinateRing k SquareVertex SquareSummand)
  have hs := s.2
  rw [← hg] at hs ⊢
  apply isUnit_of_a
  intro h0
  apply hs
  change pointEvaluation (strassenSquare k) (strassenSquare_solves k) (Ideal.Quotient.mk _ g) = 0
  rw [quotPoint, Ideal.Quotient.lift_mk] at h0
  rw [pointEvaluation, Ideal.Quotient.lift_mk, ← aHom_polyPoint T W g]
  exact h0

/-- The second-order point on the local ring. -/
noncomputable def localPoint (hW : Admissible T W) : A k →+* SecondJet T :=
  IsLocalization.lift (M := (pointIdeal (strassenSquare k) (strassenSquare_solves k)).primeCompl)
    (quotPoint_unit hW)

theorem localPoint_φ (hW : Admissible T W) (g : MvPolynomial (Variable SquareVertex SquareSummand) k) :
    localPoint hW (φ k g) = polyPoint T W g := by
  rw [localPoint, φ, toPointLocalRing_apply, IsLocalization.lift_eq]
  rfl

theorem localPoint_algebraMap (hW : Admissible T W) (r : k) :
    localPoint hW (algebraMap k (A k) r) = const T r := by
  rw [← φ_C, localPoint_φ, polyPoint, eval₂Hom_C]

theorem localPoint_y (hW : Admissible T W) (x : Variable SquareVertex SquareSummand) :
    localPoint hW (y k x) = ⟨0, fun i => frameVec k i x, W x⟩ := by
  rw [y, localPoint_φ, polyPoint_lin]

theorem localPoint_a_of_mem (hW : Admissible T W) {a : A k} (ha : a ∈ maximalIdeal (A k)) :
    (localPoint hW a).a = 0 := by
  have hle : maximalIdeal (A k) ≤ RingHom.ker ((aHom T).comp (localPoint hW)) := by
    rw [maximalIdeal_eq, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    simp [localPoint_y, aHom]
  exact hle ha

theorem localPoint_sq (hW : Admissible T W) {a : A k} (ha : a ∈ maximalIdeal (A k) ^ 2) :
    (localPoint hW a).a = 0 ∧ (localPoint hW a).u = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [map_mul, mul_eq_of_a_zero T (localPoint_a_of_mem hW hx) (localPoint_a_of_mem hW hy)]
    exact ⟨rfl, rfl⟩
  · rw [map_add, add_a, add_u, hx.1, hx.2, hy.1, hy.2]
    exact ⟨add_zero _, add_zero _⟩

theorem localPoint_cube (hW : Admissible T W) {a : A k} (ha : a ∈ maximalIdeal (A k) ^ 3) :
    localPoint hW a = 0 := by
  rw [pow_succ] at ha
  have key : (localPoint hW a).a = 0 ∧ (localPoint hW a) = 0 := by
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨h1, h2⟩ := localPoint_sq hW hx
      have hy' := localPoint_a_of_mem hW hy
      rw [map_mul]
      refine ⟨by simp [h1], ?_⟩
      ext <;> simp [h1, h2, hy', bil_zero_left]
    · rw [map_add, hx.2, hy.2, add_zero]
      exact ⟨rfl, rfl⟩
  exact key.2

theorem localPoint_z (hW : Admissible T W) (i : Fin 251) :
    localPoint hW (z k i) = ⟨0, Pi.single i 1, ∑ x, wv k i x * W x⟩ := by
  rw [z, Ψ_poly, localPoint_φ, map_sum]
  have h : ∀ x, polyPoint T W ((X x - C ((strassenSquare k).coordinates x)) * C (wv k i x)) =
      ⟨0, wv k i x • fun l => frameVec k l x, wv k i x * W x⟩ := by
    intro x
    rw [map_mul, polyPoint_lin, polyPoint, eval₂Hom_C, mk_mul_const']
  simp only [h]
  ext
  · rw [sum_a]; simp
  · rw [sum_u]
    rename_i l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [dual_pairing, Pi.single_apply]
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl, Ne.symm hl]
  · rw [sum_c]

theorem localPoint_zz (hW : Admissible T W) (i j : Fin 251) :
    (localPoint hW (z k i * z k j)).c = T s(i, j) := by
  rw [map_mul, localPoint_z, localPoint_z, mk_mul_mk]
  simp only [bil, Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

/-- The second-order functional of an admissible table. -/
noncomputable def functional (hW : Admissible T W) : A k →ₗ[k] k where
  toFun a := (localPoint hW a).c
  map_add' a b := by rw [map_add]; rfl
  map_smul' r a := by
    rw [Algebra.smul_def, map_mul, localPoint_algebraMap, mul_c, const_a, const_c, const_u,
      bil_zero_left, smul_eq_mul, RingHom.id_apply]
    ring

theorem functional_apply (hW : Admissible T W) (a : A k) :
    functional hW a = (localPoint hW a).c := rfl

end Brent.SecondOrder
