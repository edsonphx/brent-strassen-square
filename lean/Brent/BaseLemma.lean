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
    fin_cases n <;> simp [h0, h1, h2']
  have hy0 : y = 0 := by
    funext j n
    obtain ⟨h0, h1, h2'⟩ := lemma_base h2 (y j 0) (y j 1) (y j 2) (hy j 0) (hy j 1) (hy j 2)
      (fun m i => (lines i j m).2)
    fin_cases n <;> simp [h0, h1, h2']
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

end Brent.Section3
