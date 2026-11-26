import Brent.CM.GradedQuotient

/-! Source draft: the associated graded ring of a finite-variable formal
power series ring is the polynomial ring, with its actual multiplication.
Combine this with the homogeneous initial-ideal quotient, rather than treating
a family of vector-space equivalences as a ring isomorphism. -/
namespace Brent.CM.GradedPolynomial

open IsLocalRing InitialForms GradedRingAssembly
open scoped DirectSum BigOperators

attribute [local instance] Classical.propDecidable

variable {σ k : Type} [Fintype σ] [Field k]
local notation "A" => MvPowerSeries σ k
local notation "P" => MvPolynomial σ k
local notation "𝔪" => maximalIdeal A

theorem maxIdeal_eq : 𝔪 = Brent.Formal.mX σ k := by
  refine le_antisymm (Brent.Formal.maximalIdeal_le_span_X (σ := σ) (k := k)) ?_
  rw [Brent.Formal.mX, Ideal.span_le]
  rintro _ ⟨s,rfl⟩
  rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem mem_pow (n : ℕ) (x : A) : x ∈ 𝔪 ^ n ↔ Brent.Formal.LowZero n x := by
  rw [maxIdeal_eq]
  exact Brent.Formal.mem_pow_iff_lowZero n x

noncomputable def H (n : ℕ) : A →ₗ[k] P :=
  (MvPolynomial.homogeneousComponent n).comp
    (MvPowerSeries.trunc' k (Brent.Formal.box (n + 1)))

theorem coeff_H (n : ℕ) (x : A) (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (H n x) = if e.degree = n then MvPowerSeries.coeff e x else 0 := by
  simp only [H, LinearMap.comp_apply, MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h
  · rw [MvPowerSeries.coeff_trunc', if_pos (Brent.Formal.le_box (by omega))]
  · rfl

theorem H_homogeneous (n : ℕ) (x : A) : (H n x).IsHomogeneous n := by
  simp only [H, LinearMap.comp_apply]
  exact MvPolynomial.homogeneousComponent_isHomogeneous n _

theorem H_coe (n : ℕ) (p : P) : H n (p : A) = MvPolynomial.homogeneousComponent n p := by
  ext e
  rw [coeff_H, MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_coe]

theorem H_zero_of_mem {n : ℕ} {x : A} (h : x ∈ 𝔪 ^ (n+1)) : H n x = 0 := by
  ext e
  rw [coeff_H, MvPolynomial.coeff_zero]
  split_ifs with he
  · exact (mem_pow _ _).mp h e (by omega)
  · rfl

theorem sub_H_mem {n : ℕ} {x : A} (hx : x ∈ 𝔪 ^ n) :
    x - (H n x : A) ∈ 𝔪 ^ (n+1) := by
  rw [mem_pow]
  intro e he
  rw [map_sub, MvPolynomial.coeff_coe, coeff_H]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    exact (mem_pow _ _).mp hx e (by omega)

theorem homogeneous_mem {n : ℕ} {p : P} (h : p.IsHomogeneous n) : (p : A) ∈ 𝔪 ^ n := by
  rw [mem_pow]
  intro e he
  rw [MvPolynomial.coeff_coe]
  exact h.coeff_eq_zero (by omega)

/-- Lowest homogeneous parts multiply, at prescribed degrees. -/
theorem H_mul {i j : ℕ} {x y : A} (hx : x ∈ 𝔪 ^ i) (hy : y ∈ 𝔪 ^ j) :
    H (i+j) (x*y) = H i x * H j y := by
  have hx' := sub_H_mem hx
  have hy' := sub_H_mem hy
  have hxh : (H i x : A) ∈ 𝔪 ^ i := homogeneous_mem (H_homogeneous i x)
  have h1 : (x-(H i x : A))*y ∈ 𝔪 ^ (i+j+1) := by
    have h := Ideal.mul_mem_mul hx' hy
    rwa [← pow_add, show i+1+j=i+j+1 by omega] at h
  have h2 : (H i x : A)*(y-(H j y : A)) ∈ 𝔪 ^ (i+j+1) := by
    have h := Ideal.mul_mem_mul hxh hy'
    rwa [← pow_add, show i+(j+1)=i+j+1 by omega] at h
  have he : x*y = ((H i x * H j y : P) : A) +
      ((x-(H i x : A))*y + (H i x : A)*(y-(H j y : A))) := by
    rw [MvPolynomial.coe_mul]
    ring
  rw [he, map_add, H_zero_of_mem (Ideal.add_mem _ h1 h2), add_zero, H_coe,
    MvPolynomial.homogeneousComponent_of_mem ((H_homogeneous i x).mul (H_homogeneous j y)),
    if_pos rfl]

variable (f : ℕ → A) (d : ℕ → ℕ)

/-- A homogeneous component of the actual associated graded ring. -/
noncomputable def toPolyPiece (n : ℕ) : Piece (source f d 0) n →+ P where
  toFun := Quotient.lift (fun a : 𝔪 ^ n => H n a.val) (by
    intro a b hab
    have h : a.val-b.val ∈ 𝔪 ^ (n+1) :=
      (Submodule.quotientRel_def (relation (source f d 0) n)).mp hab
    have hz := H_zero_of_mem h
    rw [map_sub, sub_eq_zero] at hz
    exact hz)
  map_zero' := by change H n 0 = 0; exact map_zero _
  map_add' := by
    intro a b
    induction a using piece_induction (source f d 0) with
    | h a =>
      induction b using piece_induction (source f d 0) with
      | h b =>
        change H n (a.val+b.val) = H n a.val + H n b.val
        exact map_add _ _ _

@[simp] theorem toPolyPiece_mk (n : ℕ) (a : 𝔪 ^ n) :
    toPolyPiece f d n (mk (source f d 0) n a) = H n a.val := rfl

theorem toPolyPiece_injective (n : ℕ) : Function.Injective (toPolyPiece f d n) := by
  intro a b hab
  induction a using piece_induction (source f d 0) with
  | h a =>
    induction b using piece_induction (source f d 0) with
    | h b =>
      rw [toPolyPiece_mk, toPolyPiece_mk] at hab
      have hx : a.val - b.val ∈ 𝔪 ^ n := Ideal.sub_mem _ a.property b.property
      have hh := sub_H_mem hx
      rw [map_sub, hab, sub_self, MvPolynomial.coe_zero, sub_zero] at hh
      exact (Submodule.Quotient.eq _).mpr hh

theorem toPolyPiece_homogeneous (n : ℕ) (a : Piece (source f d 0) n) :
    (toPolyPiece f d n a).IsHomogeneous n := by
  induction a using piece_induction (source f d 0) with
  | h a => exact H_homogeneous n a.val

noncomputable def toPoly : GrBase f d →+* P :=
  DirectSum.toSemiring (toPolyPiece f d)
    (by
      change H 0 (1 : A) = 1
      rw [← MvPolynomial.coe_one, H_coe]
      simp)
    (by
      intro i j a b
      induction a using piece_induction (source f d 0) with
      | h a =>
        induction b using piece_induction (source f d 0) with
        | h b =>
          change toPolyPiece f d (i+j) (product (source f d 0) i j
            (mk (source f d 0) i a) (mk (source f d 0) j b)) = _
          rw [product_mk, toPolyPiece_mk, toPolyPiece_mk, toPolyPiece_mk]
          exact H_mul a.property b.property)

@[simp] theorem toPoly_of (n : ℕ) (a : Piece (source f d 0) n) :
    toPoly f d (DirectSum.of _ n a) = toPolyPiece f d n a :=
  DirectSum.toSemiring_of _ _ _ n a

theorem homogeneousComponent_toPoly (n : ℕ) (a : GrBase f d) :
    MvPolynomial.homogeneousComponent n (toPoly f d a) = toPolyPiece f d n (a n) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    rw [toPoly_of, MvPolynomial.homogeneousComponent_of_mem (toPolyPiece_homogeneous f d i a)]
    by_cases h : n=i
    · subst i; simp
    · rw [if_neg h, DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

theorem toPoly_injective : Function.Injective (toPoly f d) := by
  intro a b h
  apply DirectSum.ext
  intro n
  apply toPolyPiece_injective f d n
  rw [← homogeneousComponent_toPoly, ← homogeneousComponent_toPoly, h]

theorem toPoly_surjective : Function.Surjective (toPoly f d) := by
  intro p
  classical
  let h (n : ℕ) : P := MvPolynomial.homogeneousComponent n p
  let x (n : ℕ) : GrBase f d := DirectSum.of _ n (mk (source f d 0) n
    ⟨(h n : A), homogeneous_mem (MvPolynomial.homogeneousComponent_isHomogeneous n p)⟩)
  refine ⟨∑ n ∈ Finset.range (p.totalDegree+1), x n, ?_⟩
  rw [map_sum]
  calc
    ∑ n ∈ Finset.range (p.totalDegree+1), toPoly f d (x n) =
        ∑ n ∈ Finset.range (p.totalDegree+1), MvPolynomial.homogeneousComponent n p := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [x, toPoly_of, toPolyPiece_mk, H_coe, h]
      rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.homogeneousComponent_isHomogeneous n p), if_pos rfl]
    _ = p := MvPolynomial.sum_homogeneousComponent p

/-- The polynomial ring is isomorphic to the associated graded ring by
sending each homogeneous series class to its actual lowest-degree polynomial. -/
noncomputable def basePolynomialEquiv : GrBase f d ≃+* P :=
  RingEquiv.ofBijective (toPoly f d) ⟨toPoly_injective f d, toPoly_surjective f d⟩

variable (hf : ∀ i, f i ∈ 𝔪 ^ d i)

@[simp] theorem basePolynomialEquiv_initial (i : ℕ) :
    basePolynomialEquiv f d (initialGenerator f d hf i) = H (d i) (f i) :=
  toPoly_of f d _ _

noncomputable def polynomialInitialIdeal (s : ℕ) : Ideal P :=
  Ideal.span (Set.range fun i : Fin s => H (d i) (f i))

theorem map_initialIdeal (s : ℕ) :
    (initialIdeal f d hf s).map (basePolynomialEquiv f d).toRingHom = polynomialInitialIdeal f d s := by
  rw [initialIdeal, Ideal.map_span, polynomialInitialIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨x,⟨i,rfl⟩,rfl⟩
    exact ⟨i, (basePolynomialEquiv_initial f d hf i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_, ⟨i,rfl⟩, basePolynomialEquiv_initial f d hf i⟩

/-- Translate a relation in the homogeneous presentation into membership in
its actual polynomial ideal, and conversely. -/
theorem H_mem_iff_relI (s n : ℕ) (a : 𝔪 ^ n) :
    H n a.val ∈ polynomialInitialIdeal f d s ↔ a.val ∈ relI f d s n := by
  let x : GrBase f d := DirectSum.of _ n (mk (source f d 0) n a)
  let e := basePolynomialEquiv f d
  have hx : e x = H n a.val := toPoly_of f d _ _
  rw [← hx, ← map_initialIdeal f d hf s]
  constructor
  · intro h
    obtain ⟨y,hy,hyx⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp h
    have he : y = x := e.injective hyx
    rw [he, ← projection_ker f d hf s, RingHom.mem_ker, x, projection_of, projectionPiece_mk] at hy
    have hz := congrArg (fun a : GrSource f d s => a n) hy
    have hz' : mk (source f d s) n a = 0 := by simpa using hz
    exact Submodule.Quotient.mk_eq_zero.mp hz'
  · intro h
    exact Ideal.mem_map_of_mem e.toRingHom (relI_mem_initialIdeal f d hf s n a h)

/-- The actual polynomial non-zero-divisor hypotheses imply the filtered
initial-regularity hypotheses. Only earlier steps are used at each stage. -/
theorem initialRegular_of_polynomial
    (hreg : ∀ i (p : P), H (d i) (f i) * p ∈ polynomialInitialIdeal f d i →
      p ∈ polynomialInitialIdeal f d i) :
    ∀ i, InitialRegularRel 𝔪 (firstIdeal f i) (f i) (d i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro n a ha hfa
    obtain ⟨u,hu,j,hj,rfl⟩ := Submodule.mem_sup.mp ha
    have hprod : u * f i ∈ 𝔪 ^ (n+d i+1) ⊔ firstIdeal f i := by
      have hh := Ideal.sub_mem _ hfa (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hj))
      simpa only [add_mul, add_sub_cancel_right] using hh
    obtain ⟨v,hv,w,hw,he⟩ := Submodule.mem_sup.mp hprod
    have huv : u * f i ∈ 𝔪 ^ (n+d i) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul hu (hf i)
    have hv' : v ∈ 𝔪 ^ (n+d i) := Ideal.pow_le_pow_right (Nat.le_succ _) hv
    have hw' : w ∈ 𝔪 ^ (n+d i) := by
      have h := Ideal.sub_mem _ huv hv'
      rw [← he, add_sub_cancel_left] at h
      exact h
    have hr : u * f i ∈ relI f d i (n+d i) := by
      rw [← he]
      exact Ideal.add_mem _ (pow_succ_le_relI (f := f) (d := d) i _ hv)
        (firstIdeal_inf_pow_le_relI_prefix f d hf i _ ih ⟨hw,hw'⟩)
    have hp := (H_mem_iff_relI f d hf i (n+d i) ⟨u*f i,huv⟩).2 hr
    change H (n+d i) (u*f i) ∈ _ at hp
    rw [H_mul hu (hf i), mul_comm] at hp
    have hrel := (H_mem_iff_relI f d hf i n ⟨u,hu⟩).1 (hreg i _ hp)
    have hle := relI_le_of_mem hf (I := firstIdeal f i) i n (fun j hj =>
      Ideal.subset_span ⟨j,hj,rfl⟩)
    have hmem : u ∈ 𝔪 ^ (n+1) ⊔ firstIdeal f i := by
      rw [sup_comm]
      exact hle hrel
    exact Ideal.add_mem _ hmem (Ideal.mem_sup_right hj)

/-- The polynomial quotient in Lemma 4.1, with the actual initial polynomials
of the given series, is isomorphic as a ring to the associated graded of
A/(f_0,...,f_(s-1)). The regularity condition is the same one used by the
existing degreewise lemma, not an assumption of the conclusion. -/
noncomputable def lemma41_polynomialQuotientEquiv
    (hreg : ∀ i, InitialRegularRel 𝔪 (firstIdeal f i) (f i) (d i)) (s : ℕ) :
    (P ⧸ polynomialInitialIdeal f d s) ≃+*
      (⨁ n, Piece (target (firstIdeal f s)) n) :=
  let e := basePolynomialEquiv f d
  let I := initialIdeal f d hf s
  let J := polynomialInitialIdeal f d s
  (Ideal.quotientEquiv I J e (map_initialIdeal f d hf s).symm).symm.trans
    (lemma41_initialQuotientEquiv f d hf hreg s)

/-- Lemma 4.1 with the ordinary polynomial initial-form non-zero-divisor
hypothesis, rather than a separate assumed filtered regularity property. -/
noncomputable def lemma41_polynomialQuotientEquiv_of_regular
    (hreg : ∀ i (p : P), H (d i) (f i) * p ∈ polynomialInitialIdeal f d i →
      p ∈ polynomialInitialIdeal f d i) (s : ℕ) :
    (P ⧸ polynomialInitialIdeal f d s) ≃+*
      (⨁ n, Piece (target (firstIdeal f s)) n) :=
  lemma41_polynomialQuotientEquiv f d hf (initialRegular_of_polynomial f d hf hreg) s

/-- A finite sequence suffices: pad by units in degree zero, without imposing
regularity on any additional input series. The finite prefix ideals are unchanged. -/
noncomputable def lemma41_finite_polynomialQuotientEquiv (s : ℕ)
    (hreg : ∀ i < s, ∀ p : P, H (d i) (f i) * p ∈ polynomialInitialIdeal f d i →
      p ∈ polynomialInitialIdeal f d i) :
    (P ⧸ polynomialInitialIdeal f d s) ≃+*
      (⨁ n, Piece (target (firstIdeal f s)) n) := by
  let F (i : ℕ) : A := if i < s then f i else 1
  let D (i : ℕ) : ℕ := if i < s then d i else 0
  have hF : ∀ i, F i ∈ 𝔪 ^ D i := by
    intro i
    by_cases hi : i < s
    · simpa [F,D,hi] using hf i
    · simp [F,D,hi]
  have hI (j : ℕ) (hj : j ≤ s) : firstIdeal F j = firstIdeal f j := by
    unfold firstIdeal
    congr 1
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      have hs : i < s := lt_of_lt_of_le hi hj
      exact ⟨i,hi,by simp [F,hs]⟩
    · rintro ⟨i,hi,rfl⟩
      have hs : i < s := lt_of_lt_of_le hi hj
      exact ⟨i,hi,by simp [F,hs]⟩
  have hJ (j : ℕ) (hj : j ≤ s) : polynomialInitialIdeal F D j = polynomialInitialIdeal f d j := by
    unfold polynomialInitialIdeal
    congr 1
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      have hi : i.val < s := lt_of_lt_of_le i.isLt hj
      exact ⟨i,by simp [F,D,hi]⟩
    · rintro ⟨i,rfl⟩
      have hi : i.val < s := lt_of_lt_of_le i.isLt hj
      exact ⟨i,by simp [F,D,hi]⟩
  have hunit : H (σ := σ) (k := k) 0 (1 : A) = 1 := by
    rw [← MvPolynomial.coe_one, H_coe]
    simp
  have hr : ∀ i (p : P), H (D i) (F i) * p ∈ polynomialInitialIdeal F D i →
      p ∈ polynomialInitialIdeal F D i := by
    intro i p hp
    by_cases hi : i < s
    · rw [hJ i (Nat.le_of_lt hi)] at hp ⊢
      exact hreg i hi p (by simpa [F,D,hi] using hp)
    · simpa [F,D,hi,hunit] using hp
  have e := lemma41_polynomialQuotientEquiv_of_regular F D hF hr s
  rw [hJ s le_rfl, hI s le_rfl] at e
  exact e

end Brent.CM.GradedPolynomial
