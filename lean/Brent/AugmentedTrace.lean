import Brent.Generated.RankChecks
import Brent.QuadraticMixed
import Brent.Generated.AugmentedData

namespace Brent.AugmentedTrace

private def pick {α : Type*} [Inhabited α] (data : Array (Array α)) (i : Nat) : α :=
  (data[i / 48]!)[i % 48]!

private def unpack : Nat → Nat → SparseRow.Row
  | 0, _ => []
  | fuel + 1, packed => if packed = 0 then [] else
    let word := packed % 131072
    let magnitude : ℤ := (word % 16) / 2
    (word / 16, if word % 2 = 0 then magnitude else -magnitude) ::
      unpack fuel (packed / 131072)

private def first (i : Fin 2352) : Fin 5268 := i.castAdd 2916
private def last (i : Fin 2916) : Fin 5268 := i.natAdd 2352
private def pair (i : Fin 2916) : Fin 54 × Fin 54 := finProdFinEquiv.symm i

def original (i : Fin 5268) : SparseRow.Row :=
  @Fin.addCases 2352 2916 (fun _ => SparseRow.Row) JacobianTrace.original
    (fun i => QuadraticData.mixedColumn (pair i).1 (pair i).2) i

def reduced (i : Fin 5268) : SparseRow.Row :=
  @Fin.addCases 2352 2916 (fun _ => SparseRow.Row) JacobianTrace.reduced
    (fun i => unpack 193 (pick mixedReducedData i.val)) i

def operations (i : Fin 5268) : List (Fin 5268 × ℤ) :=
  @Fin.addCases 2352 2916 (fun _ => List (Fin 5268 × ℤ))
    (fun i => (JacobianTrace.operations i).map fun (j, a) => (first j, a))
    (fun i => (unpack 267 (pick mixedOperationsData i.val)).map fun (j, a) => (Fin.ofNat 5268 j, a)) i

def select (i : Fin 2749) : Fin 5268 := pick selectData i.val
def pivot (i : Fin 2749) : Fin 4096 := pick pivotData i.val
def cover (i : Fin 5268) : Option (Fin 2749) := pick coverData i.val

def checkMixedStep (i : Fin 2916) : Bool :=
  SparseRow.checkRadixStep 4096 14 original reduced operations (last i)

def checkMixedMerge (i : Fin 2916) : Bool :=
  -- Sorting is for speed only. Sparse semantics allow repeated coordinates.
  let row := (original (last i)).mergeSort fun a b => a.1 ≤ b.1
  decide (SparseRow.reduce reduced row (operations (last i)) = reduced (last i))

def checkPivotAt (i : Fin 2749) : Bool :=
  SparseRow.checkPivot (reduced (select i)) (pivot i).val

def checkCoverAt (i : Fin 5268) : Bool :=
  SparseRow.checkCover reduced select cover i

def checkOrderAt (i : Fin 2748) : Bool :=
  decide (pivot i.castSucc < pivot i.succ)

private theorem check_first (i : Fin 2352) :
    (∀ x ∈ operations (first i), x.1 < first i) ∧ ∀ k : Fin 4096,
    SparseRow.coefficient k.val (reduced (first i)) =
      SparseRow.coefficient k.val (original (first i)) -
        ((operations (first i)).map fun x => x.2 * SparseRow.coefficient k.val (reduced x.1)).sum := by
  have h := SparseRow.checked_radix_step 4096 12 _ _ _ i (JacobianTrace.checkedSteps i)
  simp only [operations, reduced, original, first, Fin.addCases_left, List.map_map, Function.comp_def] at *
  constructor
  · rintro x hx
    obtain ⟨⟨j, a⟩, ha, rfl⟩ := List.mem_map.mp hx
    exact h.1 (j, a) ha
  · exact h.2

private theorem check_last (i : Fin 2916) (h : checkMixedStep i = true) :
    (∀ x ∈ operations (last i), x.1 < last i) ∧ ∀ k : Fin 4096,
    SparseRow.coefficient k.val (reduced (last i)) =
      SparseRow.coefficient k.val (original (last i)) -
        ((operations (last i)).map fun x => x.2 * SparseRow.coefficient k.val (reduced x.1)).sum :=
  SparseRow.checked_radix_step 4096 14 original reduced operations (last i) h

/-- The signed replay certifies the same augmented rank over every coefficient field. -/
theorem rank_of_checks (k : Type) [Field k]
    (steps : ∀ i, checkMixedStep i = true)
    (pivots : ∀ i, checkPivotAt i = true)
    (coverage : ∀ i, checkCoverAt i = true)
    (order : ∀ i, checkOrderAt i = true) :
    Module.finrank k (Submodule.span k (Set.range (fun i =>
      SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (original i)))) = 2749 := by
  have h (i : Fin 5268) :
      (∀ x ∈ operations i, x.1 < i) ∧ ∀ e : Fin 4096,
      SparseRow.coefficient e.val (reduced i) =
        SparseRow.coefficient e.val (original i) -
          ((operations i).map fun x => x.2 * SparseRow.coefficient e.val (reduced x.1)).sum :=
    @Fin.addCases 2352 2916 (fun i : Fin (2352 + 2916) =>
      (∀ x ∈ operations i, x.1 < i) ∧ ∀ e : Fin 4096,
      SparseRow.coefficient e.val (reduced i) =
        SparseRow.coefficient e.val (original i) -
          ((operations i).map fun x => x.2 * SparseRow.coefficient e.val (reduced x.1)).sum)
      check_first (fun j => check_last j (steps j)) i
  have hp : StrictMono (Fin.val ∘ pivot) :=
    Fin.strictMono_iff_lt_succ.mpr fun i => of_decide_eq_true (order i)
  exact SparseRow.rank_of_elimination_certificate (Fin.val : Fin 4096 → Nat)
    original reduced operations select pivot cover hp (fun i => (h i).1)
    (fun i => (h i).2) pivots coverage

end Brent.AugmentedTrace
