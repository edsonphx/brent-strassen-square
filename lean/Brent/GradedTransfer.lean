import Brent.TriangularBound
import Brent.QuadraticExpansion
import Brent.FrameBlocks
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nakayama

/-!
# Transfer of the triangular certificate to characteristic zero

Let `R` be a Noetherian local ring in which every nonzero integer is a unit (for instance a
local ring over a field of characteristic zero). Suppose that 251 elements `zᵢ` generate the
maximal ideal modulo `𝔪²`, and that 54 integral quadratic forms `F_ℓ(z) = Σ B_ℓ[i,j] zᵢ zⱼ`
lie in `𝔪³`. Suppose finally that, modulo three, the polarizations of the `F_ℓ` vanish
outside the mixed block and agree there with lexicographically triangular tables with unit
leaders. Then `dim R ≤ 197`.

The proof runs the triangular reduction in `ℤ[z]` modulo the ideal `(F, 3)`, which gives
`(z)⁵⁵ ⊆ (c, u - x, F, 3) + (z)⁵⁶`. Taking degree-55 components and applying Nakayama's lemma
to the finitely generated `ℤ`-module of forms of degree 55 removes the `3`, at the cost of an
integer `r ≡ 1 (mod 3)`. Evaluating at `z` and inverting `r` gives
`𝔪⁵⁵ ⊆ (197 parameters) + 𝔪⁵⁶`.
-/

open scoped BigOperators
open MvPolynomial IsLocalRing

namespace Brent.Transfer

open TangentData

/-! ### Index bookkeeping -/

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

/-- The 143 coordinates outside the mixed block. -/
def cIndex (i : Fin 143) : Fin 251 := Fin.castLE (by norm_num) i

theorem span_split {R : Type*} [CommRing R] (z : Fin 251 → R) :
    Ideal.span (Set.range z) ≤ Ideal.span (Set.range (z ∘ cIndex)) ⊔
      Ideal.span (Set.range (z ∘ xFrameIndex)) ⊔ Ideal.span (Set.range (z ∘ yFrameIndex)) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases h1 : i.val < 143
  · have : i = cIndex ⟨i.val, h1⟩ := Fin.ext rfl
    rw [this]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨_, rfl⟩))
  by_cases h2 : i.val < 197
  · have hi : i = xFrameIndex ⟨i.val - 143, by omega⟩ :=
      Fin.ext (by simp only [xFrameIndex]; omega)
    rw [hi]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨_, rfl⟩))
  · have hi : i = yFrameIndex ⟨i.val - 197, by have := i.isLt; omega⟩ :=
      Fin.ext (by simp only [yFrameIndex]; omega)
    rw [hi]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨_, rfl⟩)

/-- Ordered pairs outside the mixed block drop out of an ordered quadratic sum. -/
theorem ordered_to_mixed {R : Type*} [CommRing R] (z : Fin 251 → R) (G : Fin 251 → Fin 251 → R)
    (hG : ∀ i j, i < j → ¬ (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) → G i j = 0) :
    ∑ i, ∑ j, (if i < j then z i * z j * G i j else 0) =
      ∑ a, ∑ b, z (xFrameIndex a) * z (yFrameIndex b) * G (xFrameIndex a) (yFrameIndex b) := by
  have hx : ∀ i : Fin 251, (∀ a, xFrameIndex a ≠ i) → ¬ (143 ≤ i.val ∧ i.val < 197) := by
    intro i hi ⟨h1, h2⟩
    exact hi ⟨i.val - 143, by omega⟩ (Fin.ext (by simp only [xFrameIndex]; omega))
  have hy : ∀ j : Fin 251, (∀ b, yFrameIndex b ≠ j) → ¬ (197 ≤ j.val) := by
    intro j hj h1
    exact hj ⟨j.val - 197, by have := j.isLt; omega⟩ (Fin.ext (by simp only [yFrameIndex]; omega))
  have hG' : ∀ i j : Fin 251, ¬ (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) →
      (if i < j then z i * z j * G i j else 0) = 0 := by
    intro i j hij
    split_ifs with hlt
    · rw [hG i j hlt hij, mul_zero]
    · rfl
  rw [sum_comp_of_zero _ xFrameIndex xFrameIndex_injective
    (fun i hi => Finset.sum_eq_zero fun j _ => hG' _ _ fun hh => hx i hi ⟨hh.1, hh.2.1⟩)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_comp_of_zero _ yFrameIndex yFrameIndex_injective
    (fun j hj => hG' _ _ fun hh => hy j hj hh.2.2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hlt : xFrameIndex a < yFrameIndex b := by
    show (xFrameIndex a).val < (yFrameIndex b).val
    simp only [xFrameIndex, yFrameIndex]
    omega
  rw [if_pos hlt]

/-! ### Homogeneous components -/

section Homogeneous

variable {σ : Type*} {R : Type*} [CommSemiring R]

theorem homogeneousComponent_mul_of_isHomogeneous (p q : MvPolynomial σ R) {d n : ℕ}
    (hq : q.IsHomogeneous d) (hdn : d ≤ n) :
    homogeneousComponent n (p * q) = homogeneousComponent (n - d) p * q := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [Finset.sum_mul, map_sum]
  have h : ∀ i, homogeneousComponent n (homogeneousComponent i p * q) =
      if i = n - d then homogeneousComponent i p * q else 0 := by
    intro i
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      ((homogeneousComponent_isHomogeneous i p).mul hq))]
    by_cases hi : i = n - d
    · rw [if_pos (by omega), if_pos hi]
    · rw [if_neg (by omega), if_neg hi]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [Finset.mem_range, not_lt] at hm
    rw [homogeneousComponent_eq_zero _ _ (by omega), zero_mul]

theorem homogeneousComponent_eq_zero_of_mem_pow [Fintype σ] {p : MvPolynomial σ R} {n k : ℕ}
    (hp : p ∈ idealOfVars σ R ^ k) (hn : n < k) : homogeneousComponent n p = 0 := by
  ext d
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with hd
  · exact (mem_pow_idealOfVars_iff' k p).mp hp d (by omega)
  · rfl

theorem homogeneousSubmodule_fg [Finite σ] (n : ℕ) :
    (homogeneousSubmodule σ R n).FG := by
  rw [homogeneousSubmodule_eq_finsupp_supported, Finsupp.supported_eq_span_single]
  apply Submodule.fg_span
  apply Set.Finite.image
  exact (Finsupp.finite_of_degree_le n).subset fun d hd => le_of_eq hd

end Homogeneous

/-- An integral form of degree `d` evaluated at elements of an ideal `m` lies in `m ^ d`. -/
theorem eval_isHomogeneous_mem {R : Type*} [CommRing R] {n : ℕ} (m : Ideal R) (z : Fin n → R)
    (hz : ∀ i, z i ∈ m) {p : MvPolynomial (Fin n) ℤ} {d : ℕ} (hp : p.IsHomogeneous d) :
    eval₂ (Int.castRingHom R) z p ∈ m ^ d := by
  rw [p.as_sum, eval₂_sum]
  refine Submodule.sum_mem _ fun v hv => ?_
  rw [eval₂_monomial]
  refine Ideal.mul_mem_left _ _ ?_
  have hdeg := hp.degree_eq_sum_deg_support hv
  rw [Finsupp.prod, hdeg, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

/-- A form of degree `n` lies in the `n`-th power of the ideal of variables. -/
theorem hom_mem_pow {σ : Type*} {p : MvPolynomial σ ℤ} {n : ℕ} (hp : p.IsHomogeneous n) :
    p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ ℤ)) ^ n := by
  rw [mem_pow_idealOfVars_iff]
  intro x hx
  exact (hp.degree_eq_sum_deg_support hx).le

theorem comp_eq_zero_of_mem_pow {σ : Type*} {p : MvPolynomial σ ℤ} {n k : ℕ}
    (hp : p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ ℤ)) ^ k) (hn : n < k) :
    homogeneousComponent n p = 0 := by
  ext d
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with hd
  · exact (mem_pow_idealOfVars_iff' k p).mp hp d (by omega)
  · rfl

/-! ### The transfer theorem -/


theorem charZero_dim_le {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hunit : ∀ t : ℤ, t ≠ 0 → IsUnit (t : R))
    (z : Fin 251 → R) (hz : ∀ i, z i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ maximalIdeal R ^ 2)
    (B : Fin 54 → Fin 251 → Fin 251 → ℤ)
    (hrel : ∀ ell, ∑ i, ∑ j, z i * z j * (B ell i j : R) ∈ maximalIdeal R ^ 3)
    (P : Fin 54 → Fin 251 → Fin 251 → ZMod 3)
    (hdiag : ∀ ell i, ((B ell i i : ℤ) : ZMod 3) = 0)
    (hpolar : ∀ ell i j, ((B ell i j + B ell j i : ℤ) : ZMod 3) = P ell i j)
    (hnonmixed : ∀ ell i j, i < j → ¬ (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val) →
      P ell i j = 0)
    (π : Fin 54 → Fin 54) (hπ : Function.Surjective π)
    (hlead : ∀ ell, P ell (xFrameIndex ell) (yFrameIndex (π ell)) = 1)
    (hzero : ∀ ell a b, 54 * a.val + b.val < 54 * ell.val + (π ell).val →
      P ell (xFrameIndex a) (yFrameIndex b) = 0) :
    ringKrullDim R ≤ ((143 + 54 : ℕ) : WithBot ℕ∞) := by
  classical
  set m := maximalIdeal R with hm
  -- The polynomial side.
  let mS : Ideal (MvPolynomial (Fin 251) ℤ) := idealOfVars (Fin 251) ℤ
  let F : Fin 54 → MvPolynomial (Fin 251) ℤ := fun ell =>
    ∑ i, ∑ j, X i * X j * C (B ell i j)
  let Mh : Fin 54 → Fin 54 → Fin 54 → ℤ := fun ell a b =>
    ((P ell (xFrameIndex a) (yFrameIndex b)).val : ℤ)
  let cS : Fin 143 → MvPolynomial (Fin 251) ℤ := fun i => X (cIndex i)
  let xS : Fin 54 → MvPolynomial (Fin 251) ℤ := fun a => X (xFrameIndex a)
  let yS : Fin 54 → MvPolynomial (Fin 251) ℤ := fun b => X (yFrameIndex b)
  let McS : Fin 54 → Fin 54 → Fin 54 → MvPolynomial (Fin 251) ℤ := fun ell a b => C (Mh ell a b)
  let T : Ideal (MvPolynomial (Fin 251) ℤ) := Ideal.span {(3 : MvPolynomial (Fin 251) ℤ)}
  let K : Ideal (MvPolynomial (Fin 251) ℤ) := Ideal.span (Set.range F) ⊔ T
  have hT : ∀ t : ℤ, (t : ZMod 3) = 0 → (C t : MvPolynomial (Fin 251) ℤ) ∈ T := by
    intro t ht
    obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd t 3).mp ht
    rw [Ideal.mem_span_singleton]
    exact ⟨C u, by rw [hu, map_mul]; rfl⟩
  have hval : ∀ x : ZMod 3, (((x.val : ℤ)) : ZMod 3) = x := fun x => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hrelS : ∀ ell, ∑ a, ∑ b, xS a * yS b * McS ell a b ∈ mS ^ 3 ⊔ K := by
    intro ell
    apply Ideal.mem_sup_right
    have hF : F ell ∈ K := Ideal.mem_sup_left (Ideal.subset_span ⟨ell, rfl⟩)
    have e1 : F ell = ∑ i, ∑ j, (if i < j then X i * X j * C (B ell i j + B ell j i)
        else if i = j then X i * X i * C (B ell i i) else 0) := by
      simp only [F]
      rw [sum_sum_eq_ordered]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h1 h2
      · rw [map_add]; ring
      · subst h2; rfl
      · rfl
    have e2 : ∑ a, ∑ b, xS a * yS b * McS ell a b = ∑ i, ∑ j, (if i < j then
        X i * X j * C (((P ell i j).val : ℤ)) else 0) := by
      rw [ordered_to_mixed (fun i => (X i : MvPolynomial (Fin 251) ℤ))
        (fun i j => C (((P ell i j).val : ℤ))) fun i j hij hn => by
          show C (((P ell i j).val : ℤ)) = 0
          rw [hnonmixed ell i j hij hn]; simp]
    have hdiff : F ell - ∑ a, ∑ b, xS a * yS b * McS ell a b ∈ T := by
      rw [e1, e2, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      split_ifs with h1 h2
      · rw [← mul_sub, ← map_sub]
        refine Ideal.mul_mem_left _ _ (hT _ ?_)
        rw [Int.cast_sub, hpolar, hval, sub_self]
      · rw [sub_zero]
        exact Ideal.mul_mem_left _ _ (hT _ (hdiag ell i))
      · rw [sub_zero]; exact Ideal.zero_mem _
    have := Ideal.sub_mem K hF (Ideal.mem_sup_right hdiff)
    rwa [sub_sub_cancel] at this
  have hgenS : mS ≤ Ideal.span (Set.range cS) ⊔ Ideal.span (Set.range xS) ⊔
      Ideal.span (Set.range yS) ⊔ K :=
    (span_split (fun i => (X i : MvPolynomial (Fin 251) ℤ))).trans le_sup_left
  have hleadS : ∀ ell, McS ell ell (π ell) = 1 := fun ell => by
    simp only [McS, Mh, hlead]
    rw [show ((1 : ZMod 3).val : ℤ) = 1 by decide, map_one]
  have hzeroS : ∀ ell a b, 54 * a.val + b.val < 54 * ell.val + (π ell).val →
      McS ell a b = 0 := fun ell a b h => by
    simp only [McS, Mh, hzero ell a b h]
    rw [ZMod.val_zero, Nat.cast_zero, map_zero]
  have core := triangular_pow_le mS K cS xS yS McS π hπ
    (fun a => Ideal.subset_span ⟨_, rfl⟩) (fun b => Ideal.subset_span ⟨_, rfl⟩)
    hgenS hrelS hleadS hzeroS
  let dS : Fin 54 → MvPolynomial (Fin 251) ℤ := fun ell => ∑ b, McS ell ell b * yS b - xS ell
  let G : Ideal (MvPolynomial (Fin 251) ℤ) :=
    Ideal.span (Set.range cS) ⊔ Ideal.span (Set.range dS) ⊔ Ideal.span (Set.range F)
  generalize hA : 54 + 1 = N55 at core
  generalize hB : 54 + 2 = N56 at core
  have core' : mS ^ N55 ≤ G ⊔ T ⊔ mS ^ N56 := by
    refine le_trans core ?_
    refine sup_le_sup_right ?_ _
    refine sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans (le_sup_left.trans le_sup_left))) ?_
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  -- Graded Nakayama over `ℤ`.
  let π55 := homogeneousComponent (σ := Fin 251) (R := ℤ) N55
  let V : Submodule ℤ (MvPolynomial (Fin 251) ℤ) := homogeneousSubmodule (Fin 251) ℤ N55
  let W : Submodule ℤ (MvPolynomial (Fin 251) ℤ) := (G.restrictScalars ℤ).map π55
  let I3 : Ideal ℤ := Ideal.span {3}
  have hVW : V ≤ W ⊔ I3 • V := by
    intro v hv
    have hvm : v ∈ mS ^ N55 := hom_mem_pow ((mem_homogeneousSubmodule _ _).mp hv)
    obtain ⟨gt, hgt, h, hh, rfl⟩ := Submodule.mem_sup.mp (core' hvm)
    obtain ⟨g, hg, t, ht, rfl⟩ := Submodule.mem_sup.mp hgt
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    have hself : π55 (g + s * 3 + h) = g + s * 3 + h := by
      simp only [π55]
      rw [homogeneousComponent_of_mem hv, if_pos rfl]
    rw [← hself, map_add, map_add]
    have hh0 : π55 h = 0 := comp_eq_zero_of_mem_pow hh (by omega)
    rw [hh0, add_zero]
    have h3 : π55 (s * 3) = (3 : ℤ) • π55 s := by
      rw [← map_zsmul]
      congr 1
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [h3]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hg)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 3)
        (homogeneousComponent_mem N55 s))
  let Nq := V.map W.mkQ
  have hNfg : Nq.FG := (homogeneousSubmodule_fg N55).map _
  have hle : Nq ≤ I3 • Nq := by
    calc Nq ≤ (W ⊔ I3 • V).map W.mkQ := Submodule.map_mono hVW
      _ = I3 • Nq := by
        rw [Submodule.map_sup, Submodule.map_smul'', Submodule.mkQ_map_self, bot_sup_eq]
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    I3 Nq hNfg hle
  have hrW : ∀ v ∈ V, r • v ∈ W := by
    intro v hv
    have := hr (W.mkQ v) (Submodule.mem_map_of_mem hv)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hr0 : r ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hr1
    omega
  -- Evaluation at `z`.
  let ψ : MvPolynomial (Fin 251) ℤ →+* R := eval₂Hom (Int.castRingHom R) z
  let Ip : Ideal R := Ideal.span (Set.range (ψ ∘ cS)) ⊔ Ideal.span (Set.range (ψ ∘ dS))
  have hψ_hom : ∀ {p : MvPolynomial (Fin 251) ℤ} {d : ℕ}, p.IsHomogeneous d → ψ p ∈ m ^ d :=
    fun hp => eval_isHomogeneous_mem m z hz hp
  have hc_hom : ∀ i, (cS i).IsHomogeneous 1 := fun i => isHomogeneous_X _ _
  have hd_hom : ∀ ell, (dS ell).IsHomogeneous 1 := fun ell =>
    (IsHomogeneous.sum _ _ _ fun b _ => by
      simpa [McS] using isHomogeneous_C_mul_X (Mh ell ell b) (yFrameIndex b)).sub
      (isHomogeneous_X _ _)
  have hF_hom : ∀ ell, (F ell).IsHomogeneous 2 := fun ell =>
    IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using ((isHomogeneous_X ℤ i).mul (isHomogeneous_X ℤ j)).mul (isHomogeneous_C _ _)
  have hψF : ∀ ell, ψ (F ell) ∈ m ^ 3 := fun ell => by
    have e : ψ (F ell) = ∑ i, ∑ j, z i * z j * (B ell i j : R) := by
      simp only [F, map_sum, map_mul, ψ, eval₂Hom_X', eval₂Hom_C, eq_intCast, map_intCast]
    rw [e]; exact hrel ell
  have hW : ∀ w ∈ W, ψ w ∈ Ip ⊔ m ^ (N55 + 1) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g12, hg12, g3, hg3, rfl⟩ := Submodule.mem_sup.mp hg
    obtain ⟨g1, hg1, g2, hg2, rfl⟩ := Submodule.mem_sup.mp hg12
    obtain ⟨a1, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg1
    obtain ⟨a2, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg2
    obtain ⟨a3, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg3
    simp only [π55, LinearMap.map_add, map_sum, map_add]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · refine Submodule.sum_mem _ fun i _ => Ideal.mem_sup_left (Ideal.mem_sup_left ?_)
      have e := homogeneousComponent_mul_of_isHomogeneous (n := N55) (a1 i) _ (hc_hom i)
        (by omega)
      erw [e]; rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · refine Submodule.sum_mem _ fun i _ => Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
      have e := homogeneousComponent_mul_of_isHomogeneous (n := N55) (a2 i) _ (hd_hom i)
        (by omega)
      erw [e]; rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · refine Submodule.sum_mem _ fun i _ => Ideal.mem_sup_right ?_
      have e := homogeneousComponent_mul_of_isHomogeneous (n := N55) (a3 i) _ (hF_hom i)
        (by omega)
      erw [e]; rw [map_mul]
      have := Ideal.mul_mem_mul (hψ_hom (homogeneousComponent_isHomogeneous (N55 - 2) (a3 i)))
        (hψF i)
      rwa [← pow_add, show N55 - 2 + 3 = N55 + 1 by omega] at this
  have hmono : ∀ α : Fin 251 → ℕ, deg α = N55 → mono z α ∈ Ip ⊔ m ^ (N55 + 1) := by
    intro α hα
    let v : MvPolynomial (Fin 251) ℤ := monomial (Finsupp.equivFunOnFinite.symm α) 1
    have hdeg : (Finsupp.equivFunOnFinite.symm α).degree = N55 := by
      rw [Finsupp.degree_eq_sum]
      exact hα
    have hv : v ∈ V := (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ hdeg)
    have h1 := hW _ (hrW v hv)
    have hψv : ψ v = mono z α := by
      simp only [v, ψ, coe_eval₂Hom, eval₂_monomial, map_one, one_mul]
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
      rfl
    rw [zsmul_eq_mul, map_mul, map_intCast, hψv] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ (hunit r hr0)).mp h1
  -- The parameter certificate in `R`.
  have hmz : m ≤ Ideal.span (Set.range z) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian m) (I := m) (N := Ideal.span (Set.range z)) (N' := m)
    · rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rw [Ideal.smul_eq_mul, ← pow_two]; exact hgen
  have h55 : m ^ N55 ≤ Ip ⊔ m ^ (N55 + 1) := by
    refine (Ideal.pow_right_mono hmz N55).trans ?_
    refine (pow_le_monoSpan z (I := ⊥) (by rw [sup_bot_eq]) N55).trans ?_
    rw [sup_bot_eq, monoSpan, Ideal.span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact hmono α hα
  let par : Fin (143 + 54) → R := Fin.append (ψ ∘ cS) (ψ ∘ dS)
  have par_mem : ∀ i, par i ∈ m := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun ell => ?_) i
    · simp only [par, Fin.append_left]
      exact (pow_one m) ▸ hψ_hom (hc_hom i)
    · simp only [par, Fin.append_right]
      exact (pow_one m) ▸ hψ_hom (hd_hom ell)
  have hspan : Ip ≤ Ideal.span (Set.range par) := by
    refine sup_le ?_ ?_ <;> rw [Ideal.span_le] <;> rintro _ ⟨i, rfl⟩
    · exact Ideal.subset_span ⟨Fin.castAdd 54 i, by simp [par]⟩
    · exact Ideal.subset_span ⟨Fin.natAdd 143 i, by simp [par]⟩
  exact localDimension_le_of_power_le_span_sup_pow par par_mem (d := N55) (by omega)
    (h55.trans (sup_le_sup_right hspan _))

end Brent.Transfer
