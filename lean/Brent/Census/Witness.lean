import Brent.Census.RankBound

/-!
# §7 census: the witness checker (F18, part 2)

A `MinorW n` records one `n × n` minor of one mode matrix: the summand, the mode, the rows and
columns (as vertices, zero-based) and the `n × n` integer entries found there in the catalogue
point. `MinorW.ok` evaluates the determinant by the explicit formula (`Matrix.det_fin_two`,
`Matrix.det_fin_three`) and asks for it to be nonzero mod 3.

A `BoundW` is a rank-bound exclusion certificate:

* `many ws`: 14 distinct summands, each with a `2 × 2` minor nonzero mod 3, or
* `pair w w'`: two distinct summands, each with a `3 × 3` minor nonzero mod 3.

`BoundW.not_mem_rankBound`: if `b.check = true` and a point `v` agrees with the recorded entries,
then `v ∉ RankBound k` for every field `k` of characteristic 0 or 3. A determinant nonzero mod 3
is a nonzero integer, so one certificate serves both characteristics. The statement is
one-sided: `check = true` excludes, `check = false` says nothing.
-/

open MvPolynomial
open scoped BigOperators

namespace Brent.Census

open Brent Brent.Formal Brent.Formal.FamilyClosure

/-- One recorded minor of a catalogue point. -/
structure MinorW (n : ℕ) where
  s : SquareSummand
  m : Mode
  r : Fin n → SquareVertex
  c : Fin n → SquareVertex
  e : Matrix (Fin n) (Fin n) ℤ

/-- The explicit determinant. -/
def det2 (e : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := e 0 0 * e 1 1 - e 0 1 * e 1 0

/-- The explicit determinant. -/
def det3 (e : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  e 0 0 * e 1 1 * e 2 2 - e 0 0 * e 1 2 * e 2 1 - e 0 1 * e 1 0 * e 2 2 +
    e 0 1 * e 1 2 * e 2 0 + e 0 2 * e 1 0 * e 2 1 - e 0 2 * e 1 1 * e 2 0

theorem det2_eq (e : Matrix (Fin 2) (Fin 2) ℤ) : det2 e = e.det := (Matrix.det_fin_two e).symm

theorem det3_eq (e : Matrix (Fin 3) (Fin 3) ℤ) : det3 e = e.det := (Matrix.det_fin_three e).symm

def MinorW.ok2 (w : MinorW 2) : Bool := det2 w.e % 3 != 0

def MinorW.ok3 (w : MinorW 3) : Bool := det3 w.e % 3 != 0

/-- The minor choice of a recorded minor. -/
def MinorW.choice {n : ℕ} (w : MinorW n) : MinorChoice n := (w.m, w.r, w.c)

/-- A point agrees with a recorded minor. -/
def MinorW.Agrees {k : Type} [Field k] {n : ℕ} (w : MinorW n) (v : Var → k) : Prop :=
  ∀ i j, v (w.s, w.m, (w.r i, w.c j)) = (w.e i j : k)

/-- A rank-bound exclusion certificate. -/
inductive BoundW
  | many (ws : Fin 14 → MinorW 2)
  | pair (w w' : MinorW 3)

/-- The kernel-evaluated check. -/
def BoundW.check : BoundW → Bool
  | .many ws => decide (∀ i j, (ws i).s = (ws j).s → i = j) && decide (∀ i, (ws i).ok2 = true)
  | .pair w w' => decide (w.s ≠ w'.s) && w.ok3 && w'.ok3

/-- A point agrees with a certificate. -/
def BoundW.Agrees {k : Type} [Field k] : BoundW → (Var → k) → Prop
  | .many ws, v => ∀ i, (ws i).Agrees v
  | .pair w w', v => w.Agrees v ∧ w'.Agrees v

variable {k : Type} [Field k]

/-- An integer that is nonzero mod 3 is nonzero in a field of characteristic 0 or 3. -/
theorem intCast_ne_zero_of_emod (hk : CharP k 3 ∨ CharZero k) {x : ℤ} (hx : x % 3 ≠ 0) :
    (x : k) ≠ 0 := by
  rcases hk with hk | hk
  · rw [Ne, CharP.intCast_eq_zero_iff k 3, Int.dvd_iff_emod_eq_zero]
    exact_mod_cast hx
  · rw [Ne, Int.cast_eq_zero]
    rintro rfl
    exact hx (Int.zero_emod 3)

theorem MinorW.eval_ne_zero {n : ℕ} (hk : CharP k 3 ∨ CharZero k) (w : MinorW n)
    (hdet : w.e.det % 3 ≠ 0) (v : Var → k) (hv : w.Agrees v) :
    eval v (minorPoly w.s w.choice) ≠ 0 := by
  rw [eval_minorPoly]
  have hsub : (modeMat v w.s w.choice.1).submatrix w.choice.2.1 w.choice.2.2 =
      (Int.castRingHom k).mapMatrix w.e := by
    ext i j
    exact hv i j
  rw [hsub, ← RingHom.map_det]
  exact intCast_ne_zero_of_emod hk hdet

theorem MinorW.ok2_spec (w : MinorW 2) (h : w.ok2 = true) : w.e.det % 3 ≠ 0 := by
  rw [← det2_eq]
  simpa [MinorW.ok2] using h

theorem MinorW.ok3_spec (w : MinorW 3) (h : w.ok3 = true) : w.e.det % 3 ≠ 0 := by
  rw [← det3_eq]
  simpa [MinorW.ok3] using h

/-- **Soundness of the checker.** A checked certificate excludes every agreeing point from the
rank bounds, in characteristic 0 and 3. -/
theorem BoundW.not_mem_rankBound (hk : CharP k 3 ∨ CharZero k) (b : BoundW) (hb : b.check = true)
    (v : Affine k) (hv : b.Agrees v) : v ∉ RankBound k := by
  intro hmem
  have hz : ∀ f ∈ boundPolys (k := k), eval v f = 0 := hmem
  cases b with
  | many ws =>
    simp only [BoundW.check, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hinj, hok⟩ := hb
    have hf : (∏ i, minorPoly (ws i).s (ws i).choice : MvPolynomial Var k) ∈ boundPolys (k := k) :=
      Or.inl ⟨fun i => (ws i).s, fun i => (ws i).choice, fun i j h => hinj i j h, rfl⟩
    have h0 := hz _ hf
    rw [map_prod] at h0
    exact (Finset.prod_ne_zero_iff.mpr fun i _ =>
      (ws i).eval_ne_zero hk ((ws i).ok2_spec (hok i)) v (hv i)) h0
  | pair w w' =>
    simp only [BoundW.check, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hne, h1⟩, h2⟩ := hb
    have hf : (minorPoly w.s w.choice * minorPoly w'.s w'.choice : MvPolynomial Var k) ∈
        boundPolys (k := k) :=
      Or.inr ⟨w.s, w'.s, w.choice, w'.choice, hne, rfl⟩
    have h0 := hz _ hf
    rw [map_mul] at h0
    exact mul_ne_zero (w.eval_ne_zero hk (w.ok3_spec h1) v hv.1)
      (w'.eval_ne_zero hk (w'.ok3_spec h2) v hv.2) h0

/-- **Exclusion from the closure.** A checked certificate excludes every agreeing point from the
Zariski closure of the saturated union of both families. -/
theorem BoundW.not_mem_closure (hk : CharP k 3 ∨ CharZero k) (b : BoundW) (hb : b.check = true)
    (v : Affine k) (hv : b.Agrees v) :
    v ∉ closure (saturation (imageA k true) ∪ saturation (imageA k false)) :=
  fun h => b.not_mem_rankBound hk hb v hv (closure_saturation_subset_rankBound h)

end Brent.Census
