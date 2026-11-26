import Brent.Census.AnchorClosure
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Lemma 3.1 and the injectivity of the block derivatives (`paper.tex` lines 231–288)

DRAFT, NOT YET COMPILED.

Work over a field with `2 ≠ 0`. Write `A_i, B_i` for the first two Strassen factors and
`D_i = C_iᵗ` for the transposed output factor (`fac k m i`). The infinitesimal action of
`(a, b, c)` is cyclic (lines 236–240): `δA = aA − Ab`, `δB = bB − Bc`, `δD = cD − Da` (`act`).

* `lemma_base` (Lemma 3.1, lines 245–257): if `a, b, c` are trace-free and every derivative is a
  multiple of its factor at every summand, then `a = b = c = 0`.
* `kron_line` (lines 268–275): `d F⊗G + F⊗U + V⊗G = 0` with `F, G ≠ 0` forces `U ∈ kG`, `V ∈ kF`.
* `derivative_injective` (lines 277–288): the map from the rescaling scalars and the two lists of
  trace-free block parameters to the tangent space is injective.
-/

open scoped Kronecker

namespace Brent.Section3

open Brent Brent.Census

variable {k : Type} [Field k]

/-- The factor matrices in the cyclic convention: `A_i`, `B_i` and `D_i = C_iᵗ`. -/
def fac (k : Type) [Field k] : Mode → Fin 7 → Matrix (Fin 2) (Fin 2) k
  | .u, i => sMat k i .u
  | .v, i => sMat k i .v
  | .w, i => (sMat k i .w)ᵀ

/-- `X` lies on the line through `F`. -/
def InLine (X F : Matrix (Fin 2) (Fin 2) k) : Prop := ∃ t : k, X = t • F

/-- The infinitesimal action of `(a, b, c)` on a factor of the given mode (lines 236–240). -/
def act (a b c : Matrix (Fin 2) (Fin 2) k) : Mode → Matrix (Fin 2) (Fin 2) k →
    Matrix (Fin 2) (Fin 2) k
  | .u, F => a * F - F * b
  | .v, F => b * F - F * c
  | .w, F => c * F - F * a

theorem act_zero (m : Mode) (F : Matrix (Fin 2) (Fin 2) k) : act 0 0 0 m F = 0 := by
  cases m <;> simp [act]

theorem sMat_apply' (i : Fin 7) (m : Mode) (x y : Fin 2) :
    sMat k i m x y = ((strassen.coordinates (i, m, (x, y)) : ℤ) : k) := rfl

theorem strassen_entry_unit : ∀ i : Fin 7, ∀ m : Mode, ∃ x y : Fin 2,
    strassen.coordinates (i, m, (x, y)) = 1 ∨ strassen.coordinates (i, m, (x, y)) = -1 := by
  decide

/-- Every Strassen factor is nonzero, over every field. -/
theorem fac_ne_zero (m : Mode) (i : Fin 7) : fac k m i ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := strassen_entry_unit i m
  have key : sMat k i m ≠ 0 := by
    intro h
    have := congrFun (congrFun h x) y
    rw [sMat_apply', Matrix.zero_apply] at this
    rcases hxy with e | e <;> rw [e] at this <;> simp at this
  cases m
  · exact key
  · exact key
  · intro h
    change (sMat k i .w)ᵀ = 0 at h
    apply key
    rw [← Matrix.transpose_transpose (sMat k i .w), h, Matrix.transpose_zero]

theorem fac_zero (m : Mode) : fac k m 0 = 1 := by
  cases m
  · exact sMat_zero (k := k) _
  · exact sMat_zero (k := k) _
  · change (sMat k 0 .w)ᵀ = 1
    rw [sMat_zero (k := k), Matrix.transpose_one]

/-! The first-mode factors `E₁₁` (summand 2) and `E₁₁ + E₁₂` (summand 4). -/

theorem strassen_u_two : strassen.coordinates (2, Mode.u, ((0 : Fin 2), (0 : Fin 2))) = 1 ∧
    strassen.coordinates (2, Mode.u, ((0 : Fin 2), (1 : Fin 2))) = 0 ∧
    strassen.coordinates (2, Mode.u, ((1 : Fin 2), (0 : Fin 2))) = 0 ∧
    strassen.coordinates (2, Mode.u, ((1 : Fin 2), (1 : Fin 2))) = 0 := by
  decide

theorem strassen_u_four : strassen.coordinates (4, Mode.u, ((0 : Fin 2), (0 : Fin 2))) = 1 ∧
    strassen.coordinates (4, Mode.u, ((0 : Fin 2), (1 : Fin 2))) = 1 ∧
    strassen.coordinates (4, Mode.u, ((1 : Fin 2), (0 : Fin 2))) = 0 ∧
    strassen.coordinates (4, Mode.u, ((1 : Fin 2), (1 : Fin 2))) = 0 := by
  decide

/-- If `x * 1 − 1 * y` is scalar and both are trace-free, then `x = y` (`2 ≠ 0`). -/
theorem eq_of_scalar (h2 : (2 : k) ≠ 0) {x y : Matrix (Fin 2) (Fin 2) k} (hx : x.trace = 0)
    (hy : y.trace = 0) (h : InLine (x * 1 - 1 * y) 1) : x = y := by
  obtain ⟨t, ht⟩ := h
  rw [Matrix.mul_one, Matrix.one_mul] at ht
  have e00 := congrFun (congrFun ht 0) 0
  have e11 := congrFun (congrFun ht 1) 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at e00 e11
  rw [Matrix.trace_fin_two] at hx hy
  have h2t : (2 : k) * t = 0 := by linear_combination -e00 - e11 + hx - hy
  have ht0 : t = 0 := (mul_eq_zero.mp h2t).resolve_left h2
  rw [ht0, zero_smul] at ht
  exact sub_eq_zero.mp ht

/-- A trace-free `h` whose commutators with `E₁₁` and `E₁₁ + E₁₂` are multiples of them is zero
(the last part of the proof of Lemma 3.1). -/
theorem eq_zero_of_comm (h2 : (2 : k) ≠ 0) {x : Matrix (Fin 2) (Fin 2) k} (hx : x.trace = 0)
    (h₂ : InLine (x * sMat k 2 .u - sMat k 2 .u * x) (sMat k 2 .u))
    (h₄ : InLine (x * sMat k 4 .u - sMat k 4 .u * x) (sMat k 4 .u)) : x = 0 := by
  obtain ⟨a00, a01, a10, a11⟩ := strassen_u_two
  obtain ⟨b00, b01, b10, b11⟩ := strassen_u_four
  obtain ⟨t, ht⟩ := h₂
  obtain ⟨t', ht'⟩ := h₄
  have E : ∀ p q, (x * sMat k 2 .u - sMat k 2 .u * x) p q = (t • sMat k 2 .u) p q :=
    fun p q => by rw [ht]
  have E' : ∀ p q, (x * sMat k 4 .u - sMat k 4 .u * x) p q = (t' • sMat k 4 .u) p q :=
    fun p q => by rw [ht']
  have e01 := E 0 1
  have e10 := E 1 0
  have f00 := E' 0 0
  have f01 := E' 0 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul, sMat_apply', a00, a01, a10, a11, b00, b01, b10, b11, Int.cast_one,
    Int.cast_zero] at e01 e10 f00 f01
  rw [Matrix.trace_fin_two] at hx
  have x01 : x 0 1 = 0 := by linear_combination -e01
  have x10 : x 1 0 = 0 := by linear_combination e10
  have tz : t' = 0 := by linear_combination -f00 - x10
  have h2x : (2 : k) * x 0 0 = 0 := by linear_combination f01 + x01 + hx + tz
  have x00 : x 0 0 = 0 := (mul_eq_zero.mp h2x).resolve_left h2
  have x11 : x 1 1 = 0 := by linear_combination hx - x00
  ext p q
  fin_cases p <;> fin_cases q <;> simp [x00, x01, x10, x11]

/-- **Lemma 3.1** (lines 245–257): "The three copies of `H` act injectively on the seven ordered
triples of factor lines of Strassen's decomposition, at the infinitesimal level." -/
theorem lemma_base (h2 : (2 : k) ≠ 0) (a b c : Matrix (Fin 2) (Fin 2) k) (ha : a.trace = 0)
    (hb : b.trace = 0) (hc : c.trace = 0)
    (h : ∀ m i, InLine (act a b c m (fac k m i)) (fac k m i)) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hu := h .u 0
  have hv := h .v 0
  simp only [act, fac_zero] at hu hv
  have hab := eq_of_scalar h2 ha hb hu
  have hbc := eq_of_scalar h2 hb hc hv
  subst hab hbc
  have h₂ := h .u 2
  have h₄ := h .u 4
  simp only [act, fac] at h₂ h₄
  have := eq_zero_of_comm h2 ha h₂ h₄
  exact ⟨this, this, this⟩

/-- Lines 268–275: projecting `d F⊗G + F⊗U + V⊗G = 0` to `Mat₂ / kG` and `Mat₂ / kF`. -/
theorem kron_line (d : k) {F G U V : Matrix (Fin 2) (Fin 2) k} (hF : F ≠ 0) (hG : G ≠ 0)
    (h : d • (F ⊗ₖ G) + F ⊗ₖ U + V ⊗ₖ G = 0) : InLine U G ∧ InLine V F := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, F p q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hF (by ext p q; simp [hc])
  obtain ⟨r, s, hrs⟩ : ∃ r s, G r s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hG (by ext p q; simp [hc])
  have e : ∀ p r q s, d * (F p q * G r s) + F p q * U r s + V p q * G r s = 0 := by
    intro p r q s
    have := congrFun (congrFun h (p, r)) (q, s)
    simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul,
      Matrix.zero_apply] using this
  have hF' := mul_inv_cancel₀ hpq
  have hG' := mul_inv_cancel₀ hrs
  refine ⟨⟨-d - V p q * (F p q)⁻¹, ?_⟩, ⟨-d - U r s * (G r s)⁻¹, ?_⟩⟩
  · ext r' s'
    rw [Matrix.smul_apply, smul_eq_mul]
    linear_combination (F p q)⁻¹ * e p r' q s' - (U r' s' + d * G r' s') * hF'
  · ext p' q'
    rw [Matrix.smul_apply, smul_eq_mul]
    linear_combination (G r s)⁻¹ * e p' r q' s - (V p' q' + d * F p' q') * hG'

theorem kron_ne_zero {F G : Matrix (Fin 2) (Fin 2) k} (hF : F ≠ 0) (hG : G ≠ 0) :
    F ⊗ₖ G ≠ 0 := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, F p q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hF (by ext p q; simp [hc])
  obtain ⟨r, s, hrs⟩ : ∃ r s, G r s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hG (by ext p q; simp [hc])
  intro h
  have := congrFun (congrFun h (p, r)) (q, s)
  rw [Matrix.kronecker_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hpq hrs this

/-- The derivative at summand `(i, j)` in mode `m` of a rescaling `d` (lines 259–260), inner block
parameters `x i = (a, b, c)` acting on `F_j` and outer block parameters `y j` acting on `F_i`
(lines 261–267). -/
def derivative (d : SquareSummand → Mode → k) (x y : Fin 7 → Fin 3 → Matrix (Fin 2) (Fin 2) k)
    (s : SquareSummand) (m : Mode) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  d s m • (fac k m s.1 ⊗ₖ fac k m s.2) +
    fac k m s.1 ⊗ₖ act (x s.1 0) (x s.1 1) (x s.1 2) m (fac k m s.2) +
    act (y s.2 0) (y s.2 1) (y s.2 2) m (fac k m s.1) ⊗ₖ fac k m s.2

/-- Lines 277–288: "Thus the map from the rescaling space and the two lists of block parameters to
the tangent space is injective." Block parameters are trace-free (`H³` per block). -/
theorem derivative_injective (h2 : (2 : k) ≠ 0) (d : SquareSummand → Mode → k)
    (x y : Fin 7 → Fin 3 → Matrix (Fin 2) (Fin 2) k) (hx : ∀ i n, (x i n).trace = 0)
    (hy : ∀ j n, (y j n).trace = 0) (h : ∀ s m, derivative d x y s m = 0) :
    d = 0 ∧ x = 0 ∧ y = 0 := by
  have lines : ∀ i j m, InLine (act (x i 0) (x i 1) (x i 2) m (fac k m j)) (fac k m j) ∧
      InLine (act (y j 0) (y j 1) (y j 2) m (fac k m i)) (fac k m i) :=
    fun i j m => kron_line (d (i, j) m) (fac_ne_zero m i) (fac_ne_zero m j) (h (i, j) m)
  have hx0 : x = 0 := by
    funext i n
    obtain ⟨h0, h1, h2'⟩ := lemma_base h2 (x i 0) (x i 1) (x i 2) (hx i 0) (hx i 1) (hx i 2)
      (fun m j => (lines i j m).1)
    fin_cases n
    exacts [h0, h1, h2']
  have hy0 : y = 0 := by
    funext j n
    obtain ⟨h0, h1, h2'⟩ := lemma_base h2 (y j 0) (y j 1) (y j 2) (hy j 0) (hy j 1) (hy j 2)
      (fun m i => (lines i j m).2)
    fin_cases n
    exacts [h0, h1, h2']
  refine ⟨?_, hx0, hy0⟩
  funext s m
  have := h s m
  simp only [derivative, hx0, hy0, Pi.zero_apply, act_zero, Matrix.kronecker_zero,
    Matrix.zero_kronecker, add_zero] at this
  exact (smul_eq_zero.mp this).resolve_right (kron_ne_zero (fac_ne_zero m s.1) (fac_ne_zero m s.2))

/-- Characteristic three or zero gives `2 ≠ 0`. -/
theorem two_ne_zero_of (hk : CharP k 3 ∨ CharZero k) : (2 : k) ≠ 0 := by
  rcases hk with h | h
  · intro h2
    have h3 : (3 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 3
    have : (1 : k) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  · exact two_ne_zero


/-! ### Lines 289–320: the 27 mixed global directions

`Mat₄ = (kI ⊗ kI) ⊕ (H ⊗ kI) ⊕ (kI ⊗ H) ⊕ (H ⊗ H)`. An element of `H ⊗ H` is `∑ᵥ hᵥ ⊗ eᵥ` with
`hᵥ ∈ H` and the basis `e₀ = E₁₂`, `e₁ = E₂₁`, `e₂ = diag(1, −1)` of `H` (`KMat`). The global
action of `(K_u, K_v, K_w)` has the same cyclic form as `act` (`globalDerivative`). -/

/-- The basis `E₁₂, E₂₁, diag(1, −1)` of `H = 𝔰𝔩₂`. -/
def eB (k : Type) [Field k] : Fin 3 → Matrix (Fin 2) (Fin 2) k :=
  ![!![0, 1; 0, 0], !![0, 0; 1, 0], !![1, 0; 0, -1]]

/-- `∑ᵥ gᵥ ⊗ eᵥ ∈ Mat₂ ⊗ H`. -/
def KMat (g : Fin 3 → Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  ∑ ν, g ν ⊗ₖ eB k ν

/-- The next mode in the cyclic order `u → v → w → u`. -/
def Mode.next : Mode → Mode
  | .u => .v
  | .v => .w
  | .w => .u

/-- The derivative of the mixed global generators `K_m = KMat (h m)` at summand `s`, mode `m`:
`K_m F − F K_{next m}` with `F = F_i ⊗ F_j`. -/
def globalDerivative (h : Mode → Fin 3 → Matrix (Fin 2) (Fin 2) k) (s : SquareSummand)
    (m : Mode) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  KMat (h m) * (fac k m s.1 ⊗ₖ fac k m s.2) - (fac k m s.1 ⊗ₖ fac k m s.2) * KMat (h m.next)

theorem kron_sub' (A B C : Matrix (Fin 2) (Fin 2) k) : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kronecker_apply, sub_mul]

theorem KMat_sub (g g' : Fin 3 → Matrix (Fin 2) (Fin 2) k) :
    KMat g - KMat g' = KMat (g - g') := by
  unfold KMat
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Pi.sub_apply, kron_sub']

theorem KMat_comm (g : Fin 3 → Matrix (Fin 2) (Fin 2) k) (F : Matrix (Fin 2) (Fin 2) k) :
    KMat g * (F ⊗ₖ 1) - (F ⊗ₖ 1) * KMat g = KMat fun ν => g ν * F - F * g ν := by
  unfold KMat
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul, kron_sub']

/-- Projecting the second tensor factor onto the coefficients of `e₀, e₁, e₂` (which vanish on
`I`): if `∑ᵥ gᵥ ⊗ eᵥ = d F⊗I + F⊗U + V⊗I`, every `gᵥ` is a multiple of `F`. -/
theorem KMat_line (h2 : (2 : k) ≠ 0) (g : Fin 3 → Matrix (Fin 2) (Fin 2) k) (d : k)
    (F U V : Matrix (Fin 2) (Fin 2) k)
    (h : KMat g = d • (F ⊗ₖ 1) + F ⊗ₖ U + V ⊗ₖ 1) : ∀ ν, InLine (g ν) F := by
  have E : ∀ p r q s, ∑ ν, g ν p q * eB k ν r s =
      d * (F p q * (1 : Matrix (Fin 2) (Fin 2) k) r s) + F p q * U r s +
        V p q * (1 : Matrix (Fin 2) (Fin 2) k) r s := by
    intro p r q s
    have := congrFun (congrFun h (p, r)) (q, s)
    simpa only [KMat, Matrix.sum_apply, Matrix.kronecker_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul] using this
  have b00 : eB k 0 0 0 = 0 := rfl
  have b01 : eB k 0 0 1 = 1 := rfl
  have b10 : eB k 0 1 0 = 0 := rfl
  have b11 : eB k 0 1 1 = 0 := rfl
  have c00 : eB k 1 0 0 = 0 := rfl
  have c01 : eB k 1 0 1 = 0 := rfl
  have c10 : eB k 1 1 0 = 1 := rfl
  have c11 : eB k 1 1 1 = 0 := rfl
  have d00 : eB k 2 0 0 = 1 := rfl
  have d01 : eB k 2 0 1 = 0 := rfl
  have d10 : eB k 2 1 0 = 0 := rfl
  have d11 : eB k 2 1 1 = -1 := rfl
  have o00 : (1 : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by simp
  have o01 : (1 : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by simp
  have o10 : (1 : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by simp
  have o11 : (1 : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := by simp
  have hinv : (2 : k) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have g0 : InLine (g 0) F := by
    refine ⟨U 0 1, ?_⟩
    ext p q
    have e := E p 0 q 1
    simp only [Fin.sum_univ_three, b01, c01, d01, o01] at e
    rw [Matrix.smul_apply, smul_eq_mul]
    linear_combination e
  have g1 : InLine (g 1) F := by
    refine ⟨U 1 0, ?_⟩
    ext p q
    have e := E p 1 q 0
    simp only [Fin.sum_univ_three, b10, c10, d10, o10] at e
    rw [Matrix.smul_apply, smul_eq_mul]
    linear_combination e
  have g2 : InLine (g 2) F := by
    refine ⟨(U 0 0 - U 1 1) * 2⁻¹, ?_⟩
    ext p q
    have e0 := E p 0 q 0
    have e1 := E p 1 q 1
    simp only [Fin.sum_univ_three, b00, c00, d00, o00, b11, c11, d11, o11] at e0 e1
    rw [Matrix.smul_apply, smul_eq_mul]
    linear_combination 2⁻¹ * (e0 - e1) - g 2 p q * hinv
  intro ν
  fin_cases ν
  exacts [g0, g1, g2]

/-- Lines 289–320: "the three copies of `H ⊗ H` give 27 independent directions modulo
`S + L + R'`." If the derivative of mixed generators `K_m = ∑ᵥ h_{m,ν} ⊗ eᵥ ∈ H ⊗ H` equals, at
every summand and mode, a derivative from rescalings and the two block lists, all `h` vanish. -/
theorem mixed_independent (h2 : (2 : k) ≠ 0) (h : Mode → Fin 3 → Matrix (Fin 2) (Fin 2) k)
    (htr : ∀ m ν, (h m ν).trace = 0) (d : SquareSummand → Mode → k)
    (x y : Fin 7 → Fin 3 → Matrix (Fin 2) (Fin 2) k)
    (heq : ∀ s m, globalDerivative h s m = derivative d x y s m) : h = 0 := by
  -- Step 1, at the identity position `(0, 0)`: `K_m = K_{next m}`.
  have step1 : ∀ m, h m = h m.next := by
    intro m
    have L : globalDerivative h (0, 0) m = KMat (h m - h m.next) := by
      simp only [globalDerivative, fac_zero, Matrix.one_kronecker_one, mul_one, one_mul, KMat_sub]
    have R : derivative d x y (0, 0) m =
        d (0, 0) m • ((1 : Matrix (Fin 2) (Fin 2) k) ⊗ₖ 1) +
          (1 : Matrix (Fin 2) (Fin 2) k) ⊗ₖ act (x 0 0) (x 0 1) (x 0 2) m 1 +
          act (y 0 0) (y 0 1) (y 0 2) m 1 ⊗ₖ 1 := by
      simp only [derivative, fac_zero]
    have e := (L.symm.trans (heq (0, 0) m)).trans R
    have lines := KMat_line h2 _ _ _ _ _ e
    funext ν
    obtain ⟨t, ht⟩ := lines ν
    have tr := congrArg Matrix.trace ht
    rw [Pi.sub_apply, Matrix.trace_sub, htr, htr, sub_zero, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul] at tr
    have t0 : t = 0 := by
      have t2 : t * 2 = 0 := by
        have h' := tr.symm
        push_cast at h'
        exact h'
      exact (mul_eq_zero.mp t2).resolve_right h2
    rw [t0, zero_smul, Pi.sub_apply] at ht
    exact sub_eq_zero.mp ht
  have huv := step1 .u
  have hvw := step1 .v
  simp only [Mode.next] at huv hvw
  -- Step 2, at `(i, 0)` in the first mode with `i = 2, 4`: `[hᵥ, A_i] ∈ k A_i`.
  have comm : ∀ i : Fin 7, ∀ ν, InLine (h .u ν * fac k .u i - fac k .u i * h .u ν)
      (fac k .u i) := by
    intro i
    have e := heq (i, 0) .u
    simp only [globalDerivative, derivative, Mode.next, fac_zero, ← huv] at e
    rw [KMat_comm] at e
    exact KMat_line h2 _ _ _ _ _ e
  have hu0 : h .u = 0 := by
    funext ν
    exact eq_zero_of_comm h2 (htr .u ν) (comm 2 ν) (comm 4 ν)
  funext m
  cases m
  · exact hu0
  · rw [← huv, hu0]
  · rw [← hvw, ← huv, hu0]

/-- The domain `(H ⊗ H)³` has dimension `3 · 3 · 3 = 27`: three modes, three basis vectors `eᵥ`
and a trace-free `hᵥ ∈ H` (dimension three) for each. -/
theorem mixed_count : Fintype.card Mode * Fintype.card (Fin 3) * 3 = 27 := by decide

end Brent.Section3
