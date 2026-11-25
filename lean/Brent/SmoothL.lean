import Brent.Generated.SmoothLData
import Brent.RadixReplay
import Brent.SquareJacobian

/-!
# A mod-3 certificate for a `2155 × 2155` Jacobian minor at the left `t = 1` point

The point `q_L` is stored as integer data. The Jacobian columns at `q_L` are rebuilt from the
data. Each certified row is `column - 3 · correction`, so it has the same image in every
field of characteristic three. Signed unit pivots and multipliers then certify the rank.
-/

namespace Brent.SmoothL

open SparseRow

private def pick {α : Type} [Inhabited α] (data : Array (Array α)) (i : Nat) : α :=
  (data[i / 48]!)[i % 48]!

/-- Each 24-bit word holds a coordinate and a signed 7-bit value. -/
def unpack (fuel packed : Nat) : Row :=
  match fuel with
  | 0 => []
  | n + 1 => if packed = 0 then [] else
    let word := packed % 16777216
    let magnitude : Int := (word % 256 : Nat) / 2
    (word / 256, if word % 2 = 0 then magnitude else -magnitude) :: unpack n (packed / 16777216)

/-- The left `t = 1` point, as stored integer coordinates. -/
def point (x : Variable SquareVertex SquareSummand) : ℤ := pick pointData (squareVariableNumber x).val

def pointDec : Decomposition ℤ SquareVertex SquareSummand where
  u s a := point (s, .u, a)
  v s a := point (s, .v, a)
  w s a := point (s, .w, a)

def coordNum : SquareVertex × SquareVertex ≃ Fin 16 :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

def twoCoords : (SquareVertex × SquareVertex) × (SquareVertex × SquareVertex) ≃ Fin 256 :=
  (Equiv.prodCongr coordNum coordNum).trans finProdFinEquiv

def block (place : (SquareVertex × SquareVertex) × (SquareVertex × SquareVertex) →
    EquationIndex SquareVertex)
    (value : (SquareVertex × SquareVertex) × (SquareVertex × SquareVertex) → ℤ) : Row :=
  ofIndexed fun i =>
    let x := twoCoords.symm i
    ((squareEquationNumber (place x)).val, value x)

theorem coefficient_block
    (place : (SquareVertex × SquareVertex) × (SquareVertex × SquareVertex) →
      EquationIndex SquareVertex)
    (value : (SquareVertex × SquareVertex) × (SquareVertex × SquareVertex) → ℤ)
    (e : EquationIndex SquareVertex) :
    coefficient (squareEquationNumber e).val (block place value) =
      ∑ x, if place x = e then value x else 0 := by
  rw [block, coefficient_ofIndexed]
  simp only [Fin.val_inj, Equiv.apply_eq_iff_eq]
  exact twoCoords.symm.sum_comp (fun x => if place x = e then value x else 0)

/-- Sparse Jacobian columns of an integer decomposition. -/
def column (p : Decomposition ℤ SquareVertex SquareSummand)
    (x : Variable SquareVertex SquareSummand) : Row :=
  let (s, m, a) := x
  match m with
  | .u => block (fun (b, c) => (a, b, c)) (fun (b, c) => p.v s b * p.w s c)
  | .v => block (fun (b, c) => (b, a, c)) (fun (b, c) => p.u s b * p.w s c)
  | .w => block (fun (b, c) => (b, c, a)) (fun (b, c) => p.u s b * p.v s c)

theorem column_correct (p : Decomposition ℤ SquareVertex SquareSummand)
    (x : Variable SquareVertex SquareSummand) (e : EquationIndex SquareVertex) :
    coefficient (squareEquationNumber e).val (column p x) = p.jacobianColumn x e.1 e.2.1 e.2.2 := by
  obtain ⟨s, m, x⟩ := x
  obtain ⟨a, b, c⟩ := e
  rw [Decomposition.jacobianColumn_eq]
  cases m <;>
    simp [column, coefficient_block, Fintype.sum_prod_type, Prod.mk.injEq, ite_and, and_left_comm]

/-! ### The trace -/

/-- The selected variables. -/
def col (i : Fin 2155) : Variable SquareVertex SquareSummand :=
  squareVariableNumber.symm (Fin.ofNat 2352 (pick columnData i.val))

/-- The selected equations, in increasing order. -/
def coord (j : Fin 2155) : Fin 4096 := Fin.ofNat 4096 (pick pivotData j.val)

def correction (i : Fin 2155) : Row := unpack 1024 (pick correctionData i.val)

def original (i : Fin 2155) : Row := subScaled 3 (column pointDec (col i)) (correction i)

def reduced (i : Fin 2155) : Row := unpack 1024 (pick reducedData i.val)

def operations (i : Fin 2155) : List (Fin 2155 × Int) :=
  (unpack 1024 (pick operationsData i.val)).map fun (j, x) => (Fin.ofNat 2155 j, x)

def select (j : Fin 2155) : Fin 2155 := Fin.ofNat 2155 (pick selectData j.val)

def index (i : Fin 2155) : Option (Fin 2155) := some (Fin.ofNat 2155 (pick indexData i.val))

/-- All checks for one row. -/
def checkRow (i : Fin 2155) : Bool :=
  checkRadixStep 4096 14 original reduced operations i &&
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
  refine rank_of_checked_radix_trace 14 coord original reduced operations select id index
    ?_ (fun i => (hr' i).1.1.1) (fun i => (hr' i).1.2) (fun i => (hr' i).1.1.2)
  rw [Fin.strictMono_iff_lt_succ]
  intro (j : Fin 2154)
  have v := (hr' ⟨j.val, by omega⟩).2
  have h2 : j.val + 1 < 2155 := by omega
  simp only [dif_pos h2, decide_eq_true_eq] at v
  exact v

end Brent.SmoothL
