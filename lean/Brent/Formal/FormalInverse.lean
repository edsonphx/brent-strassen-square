import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The formal inverse function theorem

A substitution `f ↦ f(b₁, …, bₙ)` of power series in finitely many variables, with zero constant
terms and invertible linear part, is a bijection. When the linear part is the identity, the
substitution is unitriangular for the total degree: it leaves the lowest nonzero homogeneous part
unchanged. This gives injectivity directly, and surjectivity by a degree-by-degree correction
whose limit is taken coefficientwise. The general case precomposes with a linear substitution.
No topology on the coefficients is used.
-/

open scoped BigOperators

namespace Brent.Formal

open MvPowerSeries Finsupp

variable {σ : Type*} {k : Type*} [CommRing k]

/-! ### Vanishing below a total degree -/

/-- `f` has no terms of total degree below `D`. -/
def LowZero (D : ℕ) (f : MvPowerSeries σ k) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < D → coeff m f = 0

namespace LowZero

theorem zero (D : ℕ) : LowZero D (0 : MvPowerSeries σ k) := fun _ _ => by simp

theorem of_zero (f : MvPowerSeries σ k) : LowZero 0 f := fun _ h => absurd h (Nat.not_lt_zero _)

theorem add {D : ℕ} {f g : MvPowerSeries σ k} (hf : LowZero D f) (hg : LowZero D g) :
    LowZero D (f + g) := fun m h => by simp [hf m h, hg m h]

theorem neg {D : ℕ} {f : MvPowerSeries σ k} (hf : LowZero D f) : LowZero D (-f) :=
  fun m h => by simp [hf m h]

theorem sub {D : ℕ} {f g : MvPowerSeries σ k} (hf : LowZero D f) (hg : LowZero D g) :
    LowZero D (f - g) := fun m h => by simp [hf m h, hg m h]

theorem mono {D E : ℕ} {f : MvPowerSeries σ k} (hf : LowZero D f) (h : E ≤ D) : LowZero E f :=
  fun m hm => hf m (lt_of_lt_of_le hm h)

theorem mul {p q : ℕ} {f g : MvPowerSeries σ k} (hf : LowZero p f) (hg : LowZero q g) :
    LowZero (p + q) (f * g) := by
  classical
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← map_add, hx]
  by_cases h1 : x.1.degree < p
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem one_X (s : σ) : LowZero 1 (X s : MvPowerSeries σ k) := by
  classical
  intro m hm
  rw [coeff_X, if_neg]
  rintro rfl
  simp at hm

theorem pow {p : ℕ} {f : MvPowerSeries σ k} (hf : LowZero p f) (n : ℕ) :
    LowZero (p * n) (f ^ n) := by
  induction n with
  | zero => exact of_zero _
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hf

end LowZero

/-- If `u ≡ v` above degree `p` and `u' ≡ v'` above degree `q`, then the products agree above
degree `p + q`. -/
theorem lowZero_mul_close {p q : ℕ} {u v u' v' : MvPowerSeries σ k}
    (hv : LowZero p v) (hv' : LowZero q v') (hr : LowZero (p + 1) (u - v))
    (hr' : LowZero (q + 1) (u' - v')) : LowZero (p + q + 1) (u * u' - v * v') := by
  have e : u * u' - v * v' = (u - v) * (u' - v') + (u - v) * v' + v * (u' - v') := by ring
  rw [e]
  refine ((hr.mul hr').mono (by omega)).add ((hr.mul hv').mono (by omega)) |>.add
    ((hv.mul hr').mono (by omega))

/-! ### Substitutions with identity linear part -/

/-- `b` has zero constant terms and identity linear part. -/
def IdLinear (b : σ → MvPowerSeries σ k) : Prop := ∀ s, LowZero 2 (b s - X s)

/-- The monomial `bᵈ`. -/
noncomputable def bpow (b : σ → MvPowerSeries σ k) (d : σ →₀ ℕ) : MvPowerSeries σ k :=
  d.prod fun s e => (b s) ^ e

theorem pow_close {b : σ → MvPowerSeries σ k} (hb : IdLinear b) (s : σ) (n : ℕ) :
    LowZero (n + 1) ((b s) ^ n - (X s) ^ n) := by
  induction n with
  | zero => simpa using LowZero.zero 1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have h := lowZero_mul_close (p := n) (q := 1) (by simpa using (LowZero.one_X s).pow n)
      (LowZero.one_X s) ih (hb s)
    exact h.mono (by omega)

theorem prodX_lowZero (d : σ →₀ ℕ) (S : Finset σ) :
    LowZero (∑ i ∈ S, d i) (∏ i ∈ S, (X i : MvPowerSeries σ k) ^ d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact LowZero.of_zero _
  | insert t T ht ihT =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht]
    have := ((LowZero.one_X t).pow (d t)).mul ihT
    simpa using this

theorem bpow_close [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) (d : σ →₀ ℕ) :
    LowZero (d.degree + 1) (bpow b d - monomial d 1) := by
  classical
  rw [bpow, monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum]
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty => simpa using LowZero.zero 1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.prod_insert hs, Finset.sum_insert hs]
    have hX := prodX_lowZero (k := k) d S
    have hXs : LowZero (d s) ((X s : MvPowerSeries σ k) ^ d s) := by
      simpa using (LowZero.one_X s).pow (d s)
    have h := lowZero_mul_close hXs hX (pow_close hb s (d s)) ih
    simpa [add_assoc] using h

theorem coeff_bpow [Fintype σ] [DecidableEq σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) {d m : σ →₀ ℕ}
    (h : m.degree ≤ d.degree) : coeff m (bpow b d) = if m = d then 1 else 0 := by
  have := bpow_close hb d m (by omega)
  rw [map_sub, sub_eq_zero, coeff_monomial] at this
  rw [this]

theorem IdLinear.hasSubst [Finite σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) :
    HasSubst b := by
  refine hasSubst_of_constantCoeff_zero fun s => ?_
  have h := hb s 0 (by simp)
  rw [map_sub, sub_eq_zero] at h
  rw [← coeff_zero_eq_constantCoeff_apply, h, coeff_zero_eq_constantCoeff_apply, constantCoeff_X]

/-- **Unitriangularity.** Substitution preserves vanishing below degree `D` and does not
change the coefficients of degree `D`. -/
theorem subst_lowZero [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) {D : ℕ}
    {f : MvPowerSeries σ k} (hf : LowZero D f) (m : σ →₀ ℕ) (hm : m.degree ≤ D) :
    coeff m (subst b f) = if m.degree < D then 0 else coeff m f := by
  classical
  have key : ∀ d, coeff m (d.prod fun s e => b s ^ e) = coeff m (bpow b d) := fun _ => rfl
  rw [coeff_subst hb.hasSubst, finsum_eq_single _ m]
  all_goals simp only [key]
  · rw [smul_eq_mul, coeff_bpow hb le_rfl, if_pos rfl, mul_one]
    split_ifs with h
    · exact hf m h
    · rfl
  · intro d hd
    rw [smul_eq_mul]
    by_cases hdD : d.degree < D
    · rw [hf d hdD, zero_mul]
    · rw [coeff_bpow hb (by omega), if_neg (Ne.symm hd), mul_zero]

theorem subst_lowZero' [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) {D : ℕ}
    {f : MvPowerSeries σ k} (hf : LowZero D f) : LowZero D (subst b f) := fun m hm => by
  rw [subst_lowZero hb hf m hm.le, if_pos hm]

theorem coeff_subst_eq [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) {D : ℕ}
    {f : MvPowerSeries σ k} (hf : LowZero D f) (m : σ →₀ ℕ) (hm : m.degree = D) :
    coeff m (subst b f) = coeff m f := by
  rw [subst_lowZero hb hf m hm.le, if_neg (by omega)]

theorem subst_injective_of_idLinear [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) :
    Function.Injective (subst (R := k) b) := by
  classical
  intro f g hfg
  by_contra hne
  have hsub : subst b (f - g) = 0 := by rw [subst_sub hb.hasSubst, hfg, sub_self]
  have hex : ∃ D, ∃ m : σ →₀ ℕ, m.degree = D ∧ coeff m (f - g) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hne (sub_eq_zero.mp (MvPowerSeries.ext fun m => by simpa using hall _ m rfl))
  let D := Nat.find hex
  obtain ⟨m, hmD, hm⟩ := Nat.find_spec hex
  have hlow : LowZero D (f - g) := by
    intro n hn
    by_contra h
    exact Nat.find_min hex hn ⟨n, rfl, h⟩
  have := coeff_subst_eq hb hlow m hmD
  rw [hsub, map_zero] at this
  exact hm this.symm

/-- The homogeneous part of degree `D`. -/
noncomputable def homog (D : ℕ) (r : MvPowerSeries σ k) : MvPowerSeries σ k :=
  fun m => if m.degree = D then coeff m r else 0

theorem coeff_homog (D : ℕ) (r : MvPowerSeries σ k) (m : σ →₀ ℕ) :
    coeff m (homog D r) = if m.degree = D then coeff m r else 0 := rfl

theorem homog_lowZero (D : ℕ) (r : MvPowerSeries σ k) : LowZero D (homog D r) := fun m hm => by
  rw [coeff_homog, if_neg (by omega)]

/-- The degree-by-degree approximations of a preimage. -/
noncomputable def approx (b : σ → MvPowerSeries σ k) (g : MvPowerSeries σ k) :
    ℕ → MvPowerSeries σ k
  | 0 => 0
  | D + 1 => approx b g D + homog D (g - subst b (approx b g D))

theorem approx_spec [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b)
    (g : MvPowerSeries σ k) (D : ℕ) : LowZero D (g - subst b (approx b g D)) := by
  induction D with
  | zero => exact LowZero.of_zero _
  | succ D ih =>
    intro m hm
    have hs := subst_add hb.hasSubst (approx b g D) (homog D (g - subst b (approx b g D)))
    simp only [approx]
    rw [hs, ← sub_sub, map_sub]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
    · rw [ih m h, subst_lowZero' hb (homog_lowZero D _) m h, sub_zero]
    · rw [coeff_subst_eq hb (homog_lowZero D _) m h, coeff_homog, if_pos h, sub_self]

theorem approx_stable (b : σ → MvPowerSeries σ k) (g : MvPowerSeries σ k) {D E : ℕ}
    (h : D ≤ E) : LowZero D (approx b g E - approx b g D) := by
  induction E, h using Nat.le_induction with
  | base => simpa using LowZero.zero D
  | succ E hDE ih =>
    simp only [approx]
    rw [add_sub_right_comm]
    exact ih.add ((homog_lowZero E _).mono hDE)

theorem subst_surjective_of_idLinear [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) :
    Function.Surjective (subst (R := k) b) := by
  intro g
  let f : MvPowerSeries σ k := fun m => coeff m (approx b g (m.degree + 1))
  have hf : ∀ D, LowZero (D + 1) (f - approx b g (D + 1)) := by
    intro D m hm
    rw [map_sub, sub_eq_zero]
    have := approx_stable b g (D := m.degree + 1) (E := D + 1) (by omega) m (by omega)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨f, MvPowerSeries.ext fun m => ?_⟩
  have h1 := subst_lowZero' hb (hf m.degree) m (by omega)
  rw [subst_sub hb.hasSubst, map_sub, sub_eq_zero] at h1
  rw [h1]
  have h2 := approx_spec hb g (m.degree + 1) m (by omega)
  rw [map_sub, sub_eq_zero] at h2
  exact h2.symm

theorem subst_bijective_of_idLinear [Fintype σ] {b : σ → MvPowerSeries σ k} (hb : IdLinear b) :
    Function.Bijective (subst (R := k) b) :=
  ⟨subst_injective_of_idLinear hb, subst_surjective_of_idLinear hb⟩

/-! ### General invertible linear part -/

/-- Vanishing in degrees `0` and `1` gives vanishing below degree `2`. -/
theorem lowZero_two {f : MvPowerSeries σ k} (h0 : coeff 0 f = 0)
    (h1 : ∀ l, coeff (single l 1) f = 0) : LowZero 2 f := by
  intro m hm
  by_cases hz : m = 0
  · rw [hz, h0]
  obtain ⟨l, hl⟩ : ∃ l, l ∈ m.support := by
    by_contra h
    push Not at h
    exact hz (Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem h))
  have hle : single l 1 ≤ m := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hl)
  have hsplit : m = (m - single l 1) + single l 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : (m - single l 1).degree = 0 := by
    have := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hdeg
  rw [hsplit, hdeg, zero_add, h1]

/-- The linear part of a substitution. -/
noncomputable def linPart (a : σ → MvPowerSeries σ k) : Matrix σ σ k :=
  fun i j => coeff (single j 1) (a i)

variable [Fintype σ] [DecidableEq σ]

/-- The linear forms `Σⱼ Cᵢⱼ Xⱼ`. -/
noncomputable def linForms (C : Matrix σ σ k) : σ → MvPowerSeries σ k :=
  fun i => ∑ j, C i j • X j

omit [DecidableEq σ] in
theorem linForms_hasSubst (C : Matrix σ σ k) : HasSubst (linForms C) :=
  hasSubst_of_constantCoeff_zero fun i => by simp [linForms]

omit [DecidableEq σ] in
theorem subst_linForms {a : σ → MvPowerSeries σ k} (ha : HasSubst a) (C : Matrix σ σ k)
    (i : σ) : subst a (linForms C i) = ∑ j, C i j • a j := by
  rw [← substAlgHom_apply ha, linForms, map_sum]
  simp only [map_smul, substAlgHom_X]

omit [DecidableEq σ] in
theorem subst_linForms_linForms (C D : Matrix σ σ k) (i : σ) :
    subst (linForms D) (linForms C i) = linForms (C * D) i := by
  rw [subst_linForms (linForms_hasSubst D), linForms]
  simp only [linForms, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem linForms_one : linForms (1 : Matrix σ σ k) = X := by
  funext i
  simp [linForms, Matrix.one_apply, ite_smul]

/-- **Formal inverse function theorem.** A substitution with zero constant terms and invertible
linear part is bijective. -/
theorem subst_bijective {a : σ → MvPowerSeries σ k} (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hA : IsUnit (linPart a)) : Function.Bijective (subst (R := k) a) := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hdet : IsUnit (linPart a).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  let C := (linPart a)⁻¹
  let b : σ → MvPowerSeries σ k := fun s => subst a (linForms C s)
  have hb : IdLinear b := by
    intro s
    refine lowZero_two ?_ fun l => ?_
    · simp only [b, subst_linForms ha, map_sub, map_sum, map_smul, smul_eq_mul,
        coeff_zero_eq_constantCoeff_apply, ha0, mul_zero, Finset.sum_const_zero, constantCoeff_X,
        sub_zero]
    · simp only [b, subst_linForms ha, map_sub, map_sum, map_smul, smul_eq_mul]
      have hCA : C * linPart a = 1 := Matrix.nonsing_inv_mul _ hdet
      have := congrFun (congrFun hCA s) l
      rw [Matrix.mul_apply] at this
      simp only [linPart] at this
      rw [this, coeff_X, Matrix.one_apply]
      by_cases h : s = l
      · subst h; simp
      · simp [h, Ne.symm h, Finsupp.single_left_inj one_ne_zero]
  have hcomp : ∀ f : MvPowerSeries σ k, subst a (subst (linForms C) f) = subst b f := fun f =>
    subst_comp_subst_apply (linForms_hasSubst C) ha f
  have hbij := subst_bijective_of_idLinear hb
  have hC : Function.Surjective (subst (R := k) (linForms C)) := by
    intro f
    refine ⟨subst (linForms (linPart a)) f, ?_⟩
    rw [subst_comp_subst_apply (linForms_hasSubst _) (linForms_hasSubst _)]
    have : (fun s => subst (linForms C) (linForms (linPart a) s)) = X := by
      funext s
      rw [subst_linForms_linForms, Matrix.mul_nonsing_inv _ hdet, linForms_one]
    rw [this, subst_self, id]
  refine ⟨fun f g hfg => ?_, fun g => ?_⟩
  · obtain ⟨u, rfl⟩ := hC f
    obtain ⟨v, rfl⟩ := hC g
    rw [hcomp, hcomp] at hfg
    rw [hbij.1 hfg]
  · obtain ⟨u, hu⟩ := hbij.2 g
    exact ⟨subst (linForms C) u, by rw [hcomp, hu]⟩

/-! ### Linear parts and changes of variable names -/

section Rect

variable {τ : Type*}

omit [Fintype σ] [DecidableEq σ] in
theorem eq_single_of_degree_eq_one {m : σ →₀ ℕ} (h : m.degree = 1) : ∃ l, m = single l 1 := by
  have hz : m ≠ 0 := by rintro rfl; simp at h
  obtain ⟨l, hl⟩ : ∃ l, l ∈ m.support := by
    by_contra h'
    push Not at h'
    exact hz (Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem h'))
  have hle : single l 1 ≤ m := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hl)
  have hsplit : m = (m - single l 1) + single l 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : (m - single l 1).degree = 0 := by
    have := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hdeg
  exact ⟨l, by rw [hsplit, hdeg, zero_add]⟩

omit [DecidableEq σ] in
theorem lowZero_one_of_constantCoeff {f : MvPowerSeries τ k} (h : constantCoeff f = 0) :
    LowZero 1 f := by
  intro m hm
  have : m = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]; omega
  rw [this, coeff_zero_eq_constantCoeff_apply, h]

omit [Fintype σ] [DecidableEq σ] in
theorem prod_lowZero {b : σ → MvPowerSeries τ k} (hb : ∀ s, LowZero 1 (b s)) (d : σ →₀ ℕ)
    (S : Finset σ) : LowZero (∑ i ∈ S, d i) (∏ i ∈ S, b i ^ d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact LowZero.of_zero _
  | insert t T ht ihT =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht]
    have := ((hb t).pow (d t)).mul ihT
    simpa using this

/-- **Chain rule for linear parts.** -/
theorem coeff_single_subst [DecidableEq τ] {b : σ → MvPowerSeries τ k}
    (hb : ∀ s, constantCoeff (b s) = 0) (f : MvPowerSeries σ k) (v : τ) :
    coeff (single v 1) (subst b f) = ∑ w, coeff (single w 1) f * coeff (single v 1) (b w) := by
  have hs : HasSubst b := hasSubst_of_constantCoeff_zero hb
  rw [coeff_subst hs]
  have hsupp : (Function.support fun d : σ →₀ ℕ =>
      coeff d f • coeff (single v 1) (d.prod fun s e => b s ^ e)) ⊆
      (Finset.univ.image fun w => single w 1 : Finset (σ →₀ ℕ)) := by
    intro d hd
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hnot
    apply hd
    have hdeg : d.degree ≠ 1 := fun h1 => by
      obtain ⟨l, hl⟩ := eq_single_of_degree_eq_one h1
      exact hnot ⟨l, hl.symm⟩
    have hlow : LowZero d.degree (d.prod fun s e => b s ^ e) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum]
      exact prod_lowZero (fun s => lowZero_one_of_constantCoeff (hb s)) d _
    rcases Nat.lt_or_ge d.degree 1 with h | h
    · have hd0 : d = 0 := by rw [← Finsupp.degree_eq_zero_iff]; omega
      subst hd0
      simp [coeff_one]
    · dsimp only
      rw [hlow (single v 1) (by rw [Finsupp.degree_single]; omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finsupp.prod_single_index (by simp), pow_one, smul_eq_mul]
  · intro w _ w' _ h
    exact Finsupp.single_left_injective one_ne_zero h

omit [DecidableEq σ] in
theorem subst_X_comp_equiv [Fintype τ] [DecidableEq τ] (e : τ ≃ σ) (f : MvPowerSeries τ k) :
    subst (fun w => (X (e.symm w) : MvPowerSeries τ k))
      (subst (fun w => (X (e w) : MvPowerSeries σ k)) f) = f := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  have : (fun w => subst (fun w => (X (e.symm w) : MvPowerSeries τ k)) (X (e w) :
      MvPowerSeries σ k)) = X := by
    funext w
    rw [subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), Equiv.symm_apply_apply]
  rw [this, subst_self, id]

/-- **Formal inverse function theorem, with renamed variables.** -/
theorem subst_bijective_equiv [Fintype τ] [DecidableEq τ] {a : σ → MvPowerSeries τ k}
    (e : τ ≃ σ) (ha0 : ∀ x, constantCoeff (a x) = 0)
    (hA : IsUnit (Matrix.of fun x v => coeff (single (e.symm v) 1) (a x))) :
    Function.Bijective (subst (R := k) a) := by
  let ρ : τ → MvPowerSeries σ k := fun w => X (e w)
  have hρ : ∀ w, constantCoeff (ρ w) = 0 := fun w => constantCoeff_X _
  let a' : σ → MvPowerSeries σ k := fun x => subst ρ (a x)
  have ha'0 : ∀ x, constantCoeff (a' x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hρ) hρ (ha0 x)
  have hlin : linPart a' = Matrix.of fun x v => coeff (single (e.symm v) 1) (a x) := by
    ext x v
    simp only [linPart, a', Matrix.of_apply]
    rw [coeff_single_subst hρ]
    rw [Finset.sum_eq_single (e.symm v)]
    · simp [ρ, coeff_X]
    · intro w _ hw
      rw [show coeff (single v 1) (ρ w) = 0 by
        simp only [ρ, coeff_X]
        rw [if_neg]
        intro h
        exact hw (by rw [Finsupp.single_left_injective one_ne_zero h, Equiv.symm_apply_apply]),
        mul_zero]
    · simp
  have hbij := subst_bijective ha'0 (hlin ▸ hA)
  have hcomp : ∀ f : MvPowerSeries σ k, subst ρ (subst a f) = subst a' f := fun f =>
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha0)
      (hasSubst_of_constantCoeff_zero hρ) f
  have hρinj : Function.Injective (subst (R := k) ρ) := fun f g h => by
    rw [← subst_X_comp_equiv e f, ← subst_X_comp_equiv e g]
    exact congrArg _ h
  refine ⟨fun f g h => hbij.1 (by rw [← hcomp, ← hcomp, h]), fun g => ?_⟩
  obtain ⟨f, hf⟩ := hbij.2 (subst ρ g)
  exact ⟨f, hρinj (by rw [hcomp, hf])⟩

end Rect

end Brent.Formal
