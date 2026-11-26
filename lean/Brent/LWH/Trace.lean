import Brent.Generated.LWHData
import Brent.SmoothL
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# The Li–Wang–Hu point and a mod-3 certificate for a `2155 × 2155` Jacobian minor

The point is the AlphaTensor rank-49 decomposition selected in Section 5.2.2 of
X. Li, Y. Wang, S. Hu, *Substitution and quotient of the isotropy group action*
(arXiv:2607.15069v2), stored in their repository as `s526.ipynb`. It is entry 1403 of
DeepMind's catalogue of 14,236 nonequivalent factorizations. Their table is in the cyclic
convention; the data here is in the repository's direct convention (`w = Wᵀ`).

The certificate has the shape of `Brent.SmoothL`: each certified row is a Jacobian column minus
`3 · correction`, so it has the same image in every field of characteristic three, and signed
unit pivots and multipliers certify the rank. The digit width is 16 bits.
-/

namespace Brent.LWH

open SparseRow

def pick {α : Type} [Inhabited α] (data : Array (Array α)) (i : Nat) : α :=
  (data[i / 48]!)[i % 48]!

/-- The Li–Wang–Hu point, as stored integer coordinates. -/
def point (x : Variable SquareVertex SquareSummand) : ℤ := pick pointData (squareVariableNumber x).val

def pointDec : Decomposition ℤ SquareVertex SquareSummand where
  u s a := point (s, .u, a)
  v s a := point (s, .v, a)
  w s a := point (s, .w, a)

/-! ### The trace -/

/-- The selected variables, in increasing order. -/
def col (i : Fin 2155) : Variable SquareVertex SquareSummand :=
  squareVariableNumber.symm (Fin.ofNat 2352 (pick columnData i.val))

/-- The selected equations, in increasing order. -/
def coord (j : Fin 2155) : Fin 4096 := Fin.ofNat 4096 (pick pivotData j.val)

def correction (i : Fin 2155) : Row := SmoothL.unpack 1024 (pick correctionData i.val)

def original (i : Fin 2155) : Row := subScaled 3 (SmoothL.column pointDec (col i)) (correction i)

def reduced (i : Fin 2155) : Row := SmoothL.unpack 1024 (pick reducedData i.val)

def operations (i : Fin 2155) : List (Fin 2155 × Int) :=
  (SmoothL.unpack 1024 (pick operationsData i.val)).map fun (j, x) => (Fin.ofNat 2155 j, x)

def select (j : Fin 2155) : Fin 2155 := Fin.ofNat 2155 (pick selectData j.val)

def index (i : Fin 2155) : Option (Fin 2155) := some (Fin.ofNat 2155 (pick indexData i.val))

/-- All checks for one row. -/
def checkRow (i : Fin 2155) : Bool :=
  checkRadixStep 4096 16 original reduced operations i &&
    checkCover reduced select index i &&
    checkPivot (reduced (select i)) (coord i).val &&
    if h : i.val + 1 < 2155 then decide ((coord i).val < (coord ⟨i.val + 1, h⟩).val) else true

def checkAt (i : Fin 2160) : Bool := if h : i.val < 2155 then checkRow ⟨i.val, h⟩ else true

theorem rank_of_checks (h : ∀ i, checkAt i = true) (K : Type*) [Field K] :
    Module.finrank K (Submodule.span K (Set.range (fun i =>
      decode (K := K) (fun j => (coord j).val) (original i)))) = 2155 := by
  have hr (i : Fin 2155) : checkRow i = true := by
    have := h ⟨i.val, by omega⟩
    simpa [checkAt, i.isLt] using this
  have hr' (i : Fin 2155) := hr i
  simp only [checkRow, Bool.and_eq_true] at hr'
  refine rank_of_checked_radix_trace 16 coord original reduced operations select id index
    ?_ (fun i => (hr' i).1.1.1) (fun i => (hr' i).1.2) (fun i => (hr' i).1.1.2)
  rw [Fin.strictMono_iff_lt_succ]
  intro (j : Fin 2154)
  have v := (hr' ⟨j.val, by omega⟩).2
  have h2 : j.val + 1 < 2155 := by omega
  simp only [dif_pos h2, decide_eq_true_eq] at v
  exact v

/-! ### The integer minor -/

def eqn (j : Fin 2155) : EquationIndex SquareVertex := squareEquationNumber.symm (coord j)

/-- The integer minor: selected Jacobian columns at the selected equations. -/
def minorInt : Matrix (Fin 2155) (Fin 2155) ℤ :=
  Matrix.of fun i j => pointDec.jacobianColumn (col i) (eqn j).1 (eqn j).2.1 (eqn j).2.2

theorem decode_original (K : Type*) [Field K] [CharP K 3] (i j : Fin 2155) :
    decode (K := K) (fun j => (coord j).val) (original i) j = (minorInt i j : K) := by
  have hc : (coord j).val = (squareEquationNumber (eqn j)).val := by simp [eqn]
  simp only [decode, original, coefficient_subScaled, hc, SmoothL.column_correct, minorInt,
    Matrix.of_apply, Int.cast_sub, Int.cast_mul]
  have : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  simp [this]

theorem det_minor_charThree (h : ∀ i, checkAt i = true) (K : Type*) [Field K] [CharP K 3] :
    (minorInt.map (Int.castRingHom K)).det ≠ 0 := by
  have hr := rank_of_checks h K
  have hli : LinearIndependent K (fun i => decode (K := K) (fun j => (coord j).val) (original i)) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hr, Fintype.card_fin]
  have heq : (fun i => decode (K := K) (fun j => (coord j).val) (original i)) =
      (minorInt.map (Int.castRingHom K)).row := by
    funext i j; simp [decode_original, Matrix.row]
  rw [heq, Matrix.linearIndependent_rows_iff_isUnit] at hli
  exact (Matrix.isUnit_iff_isUnit_det _).mp hli |>.ne_zero

theorem det_minorInt_ne_zero (h : ∀ i, checkAt i = true) : minorInt.det ≠ 0 := by
  intro h0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply det_minor_charThree h (ZMod 3)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

/-- **The minor is nonsingular in characteristic three and zero.** -/
theorem det_minor_ne_zero (h : ∀ i, checkAt i = true) (K : Type*) [Field K]
    (hK : CharP K 3 ∨ CharZero K) : (minorInt.map (Int.castRingHom K)).det ≠ 0 := by
  rcases hK with hK | hK
  · exact det_minor_charThree h K
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [eq_intCast]
    exact Int.cast_ne_zero.mpr (det_minorInt_ne_zero h)

end Brent.LWH
