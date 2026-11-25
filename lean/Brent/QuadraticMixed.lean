import Brent.SparseTensor
import Brent.QuadraticAnnihilator
import Brent.Generated.MixedData
import Brent.Matching

open scoped BigOperators

namespace Brent.QuadraticData

private def pick {α : Type*} [Inhabited α] (a : Array (Array α)) (i : Nat) : α :=
  (a[i / 48]!)[i % 48]!

private def unpack (fuel packed : Nat) : SparseRow.Row :=
  match fuel with
  | 0 => []
  | n + 1 => if packed = 0 then [] else
    let word := packed % 65536
    let magnitude : Int := (word % 256) / 2
    (word / 256, if word % 2 = 0 then magnitude else -magnitude) ::
      unpack n (packed / 65536)

private def modeCode : Mode → Nat
  | .u => 0
  | .v => 1
  | .w => 2

def xBlock (i : Fin 54) : Fin 7 := pick xBlockData i.val
def yBlock (j : Fin 54) : Fin 7 := pick yBlockData j.val

private def xFactor (i : Fin 54) (j : Fin 7) (m : Mode) : SparseTensor.Factor :=
  (unpack 16 (pick xFactorData (21 * i.val + 3 * j.val + modeCode m))).map
    fun (a, v) => (Fin.ofNat 16 a, v)

private def yFactor (j : Fin 54) (i : Fin 7) (m : Mode) : SparseTensor.Factor :=
  (unpack 16 (pick yFactorData (21 * j.val + 3 * i.val + modeCode m))).map
    fun (a, v) => (Fin.ofNat 16 a, v)

private def xEntry (i : Fin 54) (s : SquareSummand) (m : Mode) (a : SparseTensor.Coordinate) : Int :=
  if s.1 = xBlock i then SparseTensor.entry (xFactor i s.2 m) (SparseTensor.coordinateNumber a)
  else 0

private def yEntry (j : Fin 54) (s : SquareSummand) (m : Mode) (a : SparseTensor.Coordinate) : Int :=
  if s.2 = yBlock j then SparseTensor.entry (yFactor j s.1 m) (SparseTensor.coordinateNumber a)
  else 0

def xDirection (i : Fin 54) : Decomposition Int SquareVertex SquareSummand :=
  ⟨fun s => xEntry i s .u, fun s => xEntry i s .v, fun s => xEntry i s .w⟩

def yDirection (j : Fin 54) : Decomposition Int SquareVertex SquareSummand :=
  ⟨fun s => yEntry j s .u, fun s => yEntry j s .v, fun s => yEntry j s .w⟩

private def combineDirections (x y : Decomposition Int SquareVertex SquareSummand) :
    Decomposition Int SquareVertex SquareSummand where
  u s a := x.u s a + y.u s a
  v s b := x.v s b + y.v s b
  w s c := x.w s c + y.w s c

private def mixedSummand (x y : Decomposition Int SquareVertex SquareSummand)
    (s : SquareSummand) (e : EquationIndex SquareVertex) : Int :=
  let p := strassenSquareInt
  let a := e.1
  let b := e.2.1
  let c := e.2.2
  x.u s a * y.v s b * p.w s c + y.u s a * x.v s b * p.w s c +
    x.u s a * p.v s b * y.w s c + y.u s a * p.v s b * x.w s c +
    p.u s a * x.v s b * y.w s c + p.u s a * y.v s b * x.w s c

/-- The actual polar quadratic coefficient on the two selected directions. -/
def mixedEntry (i j : Fin 54) (e : EquationIndex SquareVertex) : Int :=
  let p := strassenSquareInt
  let x := xDirection i
  let y := yDirection j
  p.quadraticEntry (combineDirections x y) e.1 e.2.1 e.2.2 -
    p.quadraticEntry x e.1 e.2.1 e.2.2 - p.quadraticEntry y e.1 e.2.1 e.2.2

private theorem mixedEntry_sum (i j : Fin 54) (e : EquationIndex SquareVertex) :
    mixedEntry i j e = ∑ s, mixedSummand (xDirection i) (yDirection j) s e := by
  simp only [mixedEntry, Decomposition.quadraticEntry]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mixedSummand, combineDirections]
  ring

/-- Reconstruct a mixed quadratic column from the common summand. -/
def mixedColumn (i j : Fin 54) : SparseRow.Row :=
  let s := (xBlock i, yBlock j)
  let x := xFactor i s.2
  let y := yFactor j s.1
  let p := strassenSquareInt
  let u := SparseTensor.ofFunction (p.u s)
  let v := SparseTensor.ofFunction (p.v s)
  let w := SparseTensor.ofFunction (p.w s)
  SparseTensor.tensor (x .u) (y .v) w ++
    SparseTensor.tensor (y .u) (x .v) w ++
    SparseTensor.tensor (x .u) v (y .w) ++
    SparseTensor.tensor (y .u) v (x .w) ++
    SparseTensor.tensor u (x .v) (y .w) ++
    SparseTensor.tensor u (y .v) (x .w)

private theorem mixedColumn_fits (i j : Fin 54) :
    ∀ x ∈ mixedColumn i j, x.1 < 4096 := by
  intro x hx
  simp only [mixedColumn, List.mem_append, or_assoc] at hx
  rcases hx with h | h | h | h | h | h <;> exact SparseTensor.tensor_fits _ _ _ _ h

/-- The reconstructed sparse column gives the signed quadratic entry at every coordinate. -/
theorem coefficient_mixedColumn (i j : Fin 54) (e : EquationIndex SquareVertex) :
    SparseRow.coefficient (squareEquationNumber e).val (mixedColumn i j) = mixedEntry i j e := by
  rw [mixedEntry_sum, Finset.sum_eq_single (xBlock i, yBlock j)]
  · simp only [mixedColumn, SparseRow.coefficient_append, SparseTensor.coefficient_tensor,
      SparseTensor.entry_ofFunction, Equiv.symm_apply_apply, mixedSummand, xDirection,
      yDirection, xEntry, yEntry, if_true]
  · rintro ⟨a, b⟩ _ hab
    by_cases ha : a = xBlock i
    · have hb : b ≠ yBlock j := by
        intro hb
        exact hab (Prod.ext ha hb)
      simp [mixedSummand, xDirection, yDirection, xEntry, yEntry, ha, hb]
    · simp [mixedSummand, xDirection, yDirection, xEntry, yEntry, ha]
  · simp

private def mixedIndex (i j : Fin 54) : Nat := 54 * i.val + j.val

def literalMixed (i j : Fin 54) : SparseRow.Row :=
  unpack 54 (pick mixedExpectedData (mixedIndex i j))

private def mixedQuotient (i j : Fin 54) : SparseRow.Row :=
  unpack 54 (pick mixedQuotientData (mixedIndex i j))

def checkMixed (i j : Fin 54) : Bool :=
  SparseRow.checkMod 54 16 3 (SparseRow.contract coefficients (mixedColumn i j))
    (literalMixed i j) (mixedQuotient i j) &&
    (literalMixed i j).all (fun x => decide (mixedIndex (Fin.ofNat 54 x.1)
      (quadraticMatching (Fin.ofNat 54 x.1)) ≤ mixedIndex i j))

/-- Checked coefficients are the actual modulo-three covector projections of the polar quadratics. -/
theorem mixed_coefficient (i j ell : Fin 54) (h : checkMixed i j = true) :
    ∑ e : EquationIndex SquareVertex,
      (mixedEntry i j e : K) * functionalEntry ell (squareEquationNumber e) =
        (SparseRow.coefficient ell.val (literalMixed i j) : K) := by
  have h₁ : SparseRow.checkMod 54 16 3 (SparseRow.contract coefficients (mixedColumn i j))
      (literalMixed i j) (mixedQuotient i j) = true := by
    simp only [checkMixed, Bool.and_eq_true] at h
    exact h.1
  have hcheck := SparseRow.checked_mod 54 16 (SparseRow.contract coefficients (mixedColumn i j))
    (literalMixed i j) (mixedQuotient i j) h₁ ell
  rw [SparseRow.coefficient_contract_dense _ _ 4096 _ (mixedColumn_fits _ _)] at hcheck
  let f (e : Fin 4096) : K :=
    (SparseRow.coefficient e.val (mixedColumn i j) : K) * functionalEntry ell e
  have he : (∑ e : Fin 4096, f e) = (SparseRow.coefficient ell.val (literalMixed i j) : K) := by
    simpa only [Int.cast_sum, Int.cast_mul, f, functionalEntry] using hcheck
  refine Eq.trans (Finset.sum_congr rfl (fun e _ => ?_)) ((squareEquationNumber.sum_comp f).trans he)
  simp only [f, coefficient_mixedColumn]

private theorem coefficient_zero_before (r : SparseRow.Row) (ell : Fin 54)
    (predicate : (Nat × Int) → Prop)
    (hs : ∀ x ∈ r, predicate x) (hn : ∀ x, predicate (ell.val, x) → False) :
    SparseRow.coefficient ell.val r = 0 := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i, v⟩ := x
    have hm := hs _ (List.mem_cons_self ..)
    have hne : i ≠ ell.val := by
      rintro rfl
      exact hn v hm
    simp [SparseRow.coefficient, hne, ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

/-- Every coefficient before the prescribed leading position is zero. -/
theorem mixed_zero_before (i j ell : Fin 54) (h : checkMixed i j = true)
    (before : 54 * i.val + j.val < 54 * ell.val + (quadraticMatching ell).val) :
    ∑ e : EquationIndex SquareVertex,
      (mixedEntry i j e : K) * functionalEntry ell (squareEquationNumber e) = 0 := by
  rw [mixed_coefficient _ _ _ h]
  have hs := h
  simp only [checkMixed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
  have hn (a : Int) : mixedIndex (Fin.ofNat 54 ell.val)
      (quadraticMatching (Fin.ofNat 54 ell.val)) ≤ mixedIndex i j → False := by
    have he : Fin.ofNat 54 ell.val = ell := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt ell.isLt
    rw [he]
    exact not_le_of_gt before
  have zero := coefficient_zero_before (literalMixed i j) ell _ hs.2 hn
  simp [zero]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem literal_pivot_one :
    ∀ ell : Fin 54, SparseRow.coefficient ell.val (literalMixed ell (quadraticMatching ell)) = 1 := by
  decide +kernel

/-- Each prescribed leading coefficient is one. -/
theorem mixed_pivot_one (ell : Fin 54) (h : checkMixed ell (quadraticMatching ell) = true) :
    ∑ e : EquationIndex SquareVertex,
      (mixedEntry ell (quadraticMatching ell) e : K) *
        functionalEntry ell (squareEquationNumber e) = 1 := by
  simp only [mixed_coefficient _ _ _ h, literal_pivot_one, Int.cast_one]

def checkMixedNumber (n : Fin 2916) : Bool :=
  let i := (finProdFinEquiv (m := 54) (n := 54)).symm n
  checkMixed i.1 i.2

end Brent.QuadraticData
