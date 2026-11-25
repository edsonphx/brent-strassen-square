import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Second-order jet rings

For a symmetric table `T : Sym2 (Fin n) → k`, the ring `k ⊕ kⁿ ⊕ k` with product
`(a, u, c)(a', u', c') = (aa', au' + a'u, ac' + a'c + Σ T(i,j) uᵢ u'ⱼ)` is a commutative
local ring whose maximal ideal cubes to zero. Maps from the Brent local ring into it are
second-order points, and the last coordinate pairs `𝔪²/𝔪³` with `T`.
-/

open scoped BigOperators

namespace Brent

variable {k : Type*} [CommRing k] {n : ℕ}

/-- The second-order jet ring of a symmetric table. -/
@[ext]
structure SecondJet (T : Sym2 (Fin n) → k) where
  a : k
  u : Fin n → k
  c : k

namespace SecondJet

variable (T : Sym2 (Fin n) → k)

/-- The pairing defined by the table. -/
def bil (u u' : Fin n → k) : k := ∑ i, ∑ j, T s(i, j) * u i * u' j

theorem bil_comm (u u' : Fin n → k) : bil T u u' = bil T u' u := by
  unfold bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Sym2.eq_swap]; ring

theorem bil_add_left (u v w : Fin n → k) : bil T (u + v) w = bil T u w + bil T v w := by
  simp only [bil, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem bil_smul_left (r : k) (u w : Fin n → k) : bil T (r • u) w = r * bil T u w := by
  simp only [bil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem bil_neg_left (u w : Fin n → k) : bil T (-u) w = -bil T u w := by
  simp only [bil, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem bil_zero_left (w : Fin n → k) : bil T 0 w = 0 := by simp [bil]

theorem bil_add_right (u v w : Fin n → k) : bil T w (u + v) = bil T w u + bil T w v := by
  rw [bil_comm, bil_add_left, bil_comm T u, bil_comm T v]

theorem bil_smul_right (r : k) (u w : Fin n → k) : bil T w (r • u) = r * bil T w u := by
  rw [bil_comm, bil_smul_left, bil_comm]

theorem bil_zero_right (w : Fin n → k) : bil T w 0 = 0 := by rw [bil_comm, bil_zero_left]

instance : Zero (SecondJet T) := ⟨⟨0, 0, 0⟩⟩
instance : One (SecondJet T) := ⟨⟨1, 0, 0⟩⟩
instance : Add (SecondJet T) := ⟨fun x y => ⟨x.a + y.a, x.u + y.u, x.c + y.c⟩⟩
instance : Neg (SecondJet T) := ⟨fun x => ⟨-x.a, -x.u, -x.c⟩⟩
instance : Mul (SecondJet T) :=
  ⟨fun x y => ⟨x.a * y.a, x.a • y.u + y.a • x.u, x.a * y.c + y.a * x.c + bil T x.u y.u⟩⟩

@[simp] theorem zero_a : (0 : SecondJet T).a = 0 := rfl
@[simp] theorem zero_u : (0 : SecondJet T).u = 0 := rfl
@[simp] theorem zero_c : (0 : SecondJet T).c = 0 := rfl
@[simp] theorem one_a : (1 : SecondJet T).a = 1 := rfl
@[simp] theorem one_u : (1 : SecondJet T).u = 0 := rfl
@[simp] theorem one_c : (1 : SecondJet T).c = 0 := rfl
@[simp] theorem add_a (x y : SecondJet T) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_u (x y : SecondJet T) : (x + y).u = x.u + y.u := rfl
@[simp] theorem add_c (x y : SecondJet T) : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_a (x : SecondJet T) : (-x).a = -x.a := rfl
@[simp] theorem neg_u (x : SecondJet T) : (-x).u = -x.u := rfl
@[simp] theorem neg_c (x : SecondJet T) : (-x).c = -x.c := rfl
@[simp] theorem mul_a (x y : SecondJet T) : (x * y).a = x.a * y.a := rfl
@[simp] theorem mul_u (x y : SecondJet T) : (x * y).u = x.a • y.u + y.a • x.u := rfl
@[simp] theorem mul_c (x y : SecondJet T) :
    (x * y).c = x.a * y.c + y.a * x.c + bil T x.u y.u := rfl

instance : CommRing (SecondJet T) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  mul_assoc x y z := by
    ext
    · simp [mul_assoc]
    · simp only [mul_u, mul_a, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · simp only [mul_c, mul_a, mul_u, bil_add_left, bil_add_right, bil_smul_left,
        bil_smul_right]; ring
  one_mul x := by ext <;> simp [bil_zero_left]
  mul_one x := by ext <;> simp [bil_zero_right]
  zero_mul x := by ext <;> simp [bil_zero_left]
  mul_zero x := by ext <;> simp [bil_zero_right]
  left_distrib x y z := by
    ext
    · simp [mul_add]
    · simp only [mul_u, add_u, add_a, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · simp only [mul_c, add_c, add_a, add_u, bil_add_right]; ring
  right_distrib x y z := by
    ext
    · simp [add_mul]
    · simp only [mul_u, add_u, add_a, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · simp only [mul_c, add_c, add_a, add_u, bil_add_left]; ring
  neg_add_cancel x := by ext <;> simp
  mul_comm x y := by
    ext
    · simp [mul_comm]
    · simp [add_comm]
    · simp only [mul_c]; rw [bil_comm]; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The constant embedding. -/
def const : k →+* SecondJet T where
  toFun r := ⟨r, 0, 0⟩
  map_one' := rfl
  map_mul' r s := by ext <;> simp [bil_zero_left]
  map_zero' := rfl
  map_add' r s := by ext <;> simp

@[simp] theorem const_a (r : k) : (const T r).a = r := rfl
@[simp] theorem const_u (r : k) : (const T r).u = 0 := rfl
@[simp] theorem const_c (r : k) : (const T r).c = 0 := rfl

theorem mul_eq_of_a_zero {x y : SecondJet T} (hx : x.a = 0) (hy : y.a = 0) :
    x * y = ⟨0, 0, bil T x.u y.u⟩ := by
  ext <;> simp [hx, hy]

theorem mul_mul_eq_zero {x y z : SecondJet T} (hx : x.a = 0) (hy : y.a = 0) (hz : z.a = 0) :
    x * y * z = 0 := by
  ext <;> simp [hx, hy, hz, bil_zero_left, bil_zero_right]

theorem isUnit_of_a {k : Type*} [Field k] {T : Sym2 (Fin n) → k} (x : SecondJet T)
    (hx : x.a ≠ 0) : IsUnit x := by
  -- `x = a(1 + m)` with `m³ = 0`.
  let m : SecondJet T := ⟨0, x.a⁻¹ • x.u, x.a⁻¹ * x.c⟩
  have hxm : x = const T x.a * (1 + m) := by
    ext <;> simp [m, hx, bil_zero_left, smul_smul]
  have hm3 : m * m * m = 0 := mul_mul_eq_zero T rfl rfl rfl
  have hu : IsUnit (1 + m) := by
    have h : (1 + m) * (1 - m + m * m) = 1 := by
      have : (1 + m) * (1 - m + m * m) = 1 + m * m * m := by ring
      rw [this, hm3, add_zero]
    exact ⟨⟨1 + m, 1 - m + m * m, h, by rw [mul_comm]; exact h⟩, rfl⟩
  rw [hxm]
  exact ((isUnit_iff_ne_zero.mpr hx).map (const T)).mul hu

end SecondJet

end Brent
