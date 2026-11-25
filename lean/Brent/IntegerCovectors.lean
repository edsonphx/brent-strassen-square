import Brent.QuadraticAnnihilator
import Brent.Generated.LiftData

/-!
# Integer covectors lifting the 54 certified covectors

The 54 covectors `λ` are certified in the left kernel of the Jacobian modulo three, with the
integer quotients `⟨λ, R_i⟩ / 3` on the 2101 unit-pivot rows `R_i` of the elimination trace.
Since those rows are in echelon form with unit pivots, a triangular solve gives integer
corrections `T`, supported on the pivot coordinates, with `⟨λ + 3T, R_i⟩ = 0` exactly.
The checks below certify this in the kernel. Hence `μ = λ + 3T` lies in the left kernel of
the Jacobian over every commutative ring, and `μ ≡ λ` modulo three.
-/

open scoped BigOperators

set_option maxRecDepth 8192

namespace Brent.QuadraticData

private def unpackLift (fuel packed : Nat) : SparseRow.Row :=
  match fuel with
  | 0 => []
  | n + 1 => if packed = 0 then [] else
    let word := packed % 65536
    let magnitude : Int := (word % 256) / 2
    (word / 256, if word % 2 = 0 then magnitude else -magnitude) ::
      unpackLift n (packed / 65536)

/-- The correction rows, stored by equation coordinate. -/
def liftCoefficients (e : Nat) : SparseRow.Row := unpackLift 54 ((liftData[e / 48]!)[e % 48]!)

/-- Check `⟨T, R_i⟩ = -⟨λ, R_i⟩ / 3` on the `i`-th pivot row. -/
def checkLiftPivot (i : Fin 2101) : Bool :=
  SparseRow.checkMod 54 16 (-1)
    (SparseRow.contract liftCoefficients (JacobianTrace.reduced (JacobianTrace.select i))) []
    (annihilatorQuotient i)

/-- The exact integer covectors. -/
def integerEntry (i : Fin 54) (e : Fin 4096) : ℤ :=
  SparseRow.coefficient i.val (coefficients e.val) +
    3 * SparseRow.coefficient i.val (liftCoefficients e.val)

theorem integerEntry_cast (i : Fin 54) (e : Fin 4096) :
    ((integerEntry i e : ℤ) : ZMod 3) = functionalEntry i e := by
  rw [integerEntry, Int.cast_add, Int.cast_mul]
  have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
  rw [h3, zero_mul, add_zero]
  rfl

private def decodeZ (r : SparseRow.Row) (e : Fin 4096) : ℤ := SparseRow.coefficient e.val r

/-- The integer functional of the `i`-th lifted covector. -/
noncomputable def intFunctional (i : Fin 54) : (Fin 4096 → ℤ) →ₗ[ℤ] ℤ where
  toFun f := ∑ e, f e * integerEntry i e
  map_add' f g := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a f := by simp [mul_assoc, Finset.mul_sum]

private theorem eval_list_sum' (l : List (Fin 4096 → ℤ)) (e : Fin 4096) :
    l.sum e = (l.map fun f => f e).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem reduced_fits' (i : Fin 2352) :
    ∀ a ∈ JacobianTrace.reduced i, a.1 < 4096 := by
  have h := JacobianTrace.checkedSteps i
  simp only [SparseRow.checkRadixStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- The integer identity behind a `checkMod` certificate: `actual = p * quotient`. -/
private theorem checkMod_int (width bits : Nat) (p : Int) (actual quotient : SparseRow.Row)
    (h : SparseRow.checkMod width bits p actual [] quotient = true) (j : Fin width) :
    SparseRow.coefficient j.val actual = p * SparseRow.coefficient j.val quotient := by
  have he := (SparseRow.checked_radix_step width bits (fun _ : Fin 2 => actual)
    (fun i => if i = 0 then quotient else []) (fun _ => [(0, p)]) 1 h).2 j
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, if_true, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero] at he
  simp only [SparseRow.coefficient] at he
  linarith

private theorem pivot_int (annChecks : ∀ j, checkAnnihilatorPivot j = true)
    (checks : ∀ j, checkLiftPivot j = true) (i : Fin 54) (j : Fin 2101) :
    intFunctional i (decodeZ (JacobianTrace.reduced (JacobianTrace.select j))) = 0 := by
  have hA := checkMod_int 54 16 3 _ _ (annChecks j) i
  have hT := checkMod_int 54 16 (-1) _ _ (checks j) i
  rw [SparseRow.coefficient_contract_dense _ _ 4096 _ (reduced_fits' _)] at hA hT
  change ∑ e, decodeZ _ e * integerEntry i e = 0
  simp only [decodeZ, integerEntry, mul_add, Finset.sum_add_distrib]
  have e2 : ∑ x : Fin 4096, SparseRow.coefficient x.val
      (JacobianTrace.reduced (JacobianTrace.select j)) *
        (3 * SparseRow.coefficient i.val (liftCoefficients x.val)) =
      3 * ∑ x : Fin 4096, SparseRow.coefficient x.val
        (JacobianTrace.reduced (JacobianTrace.select j)) *
          SparseRow.coefficient i.val (liftCoefficients x.val) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e2, hA, hT]
  ring

private theorem reduced_int (annChecks : ∀ j, checkAnnihilatorPivot j = true)
    (checks : ∀ j, checkLiftPivot j = true) (i : Fin 54)
    (j : Fin 2352) :
    intFunctional i (decodeZ (JacobianTrace.reduced j)) = 0 := by
  have h := JacobianTrace.coverage_of_auxiliary JacobianTrace.checkedAuxiliary j
  cases hj : JacobianTrace.cover j with
  | none =>
    simp [SparseRow.checkCover, hj] at h
    rw [h]
    simp [intFunctional, decodeZ, SparseRow.coefficient]
  | some k =>
    simp [SparseRow.checkCover, hj] at h
    rw [← h]
    exact pivot_int annChecks checks i k

private theorem original_int (annChecks : ∀ j, checkAnnihilatorPivot j = true)
    (checks : ∀ j, checkLiftPivot j = true) (i : Fin 54)
    (j : Fin 2352) :
    intFunctional i (decodeZ (JacobianTrace.original j)) = 0 := by
  have h := (SparseRow.checked_radix_step 4096 12 JacobianTrace.original JacobianTrace.reduced
    JacobianTrace.operations j (JacobianTrace.checkedSteps j)).2
  let vector (s : Fin 2352 × Int) : Fin 4096 → ℤ :=
    s.2 • decodeZ (JacobianTrace.reduced s.1)
  have eq : (decodeZ (JacobianTrace.original j) : Fin 4096 → ℤ) =
      decodeZ (JacobianTrace.reduced j) +
      ((JacobianTrace.operations j).map vector).sum := by
    funext e
    have hj := h e
    simp only [Pi.add_apply, eval_list_sum', List.map_map, Function.comp_def, vector,
      Pi.smul_apply, smul_eq_mul, decodeZ]
    linarith
  rw [eq, map_add, map_list_sum, reduced_int annChecks checks i j, zero_add]
  simp only [List.map_map, Function.comp_def, vector, map_smul, reduced_int annChecks checks i,
    smul_zero, List.map_const', List.sum_replicate]

/-- The lifted integer covectors annihilate the Jacobian over every commutative ring. -/
theorem integer_annihilates (annChecks : ∀ j, checkAnnihilatorPivot j = true)
    (checks : ∀ j, checkLiftPivot j = true) (R : Type*) [CommRing R]
    (i : Fin 54) (x : Variable SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex,
      (strassenSquare R).jacobianColumn x e.1 e.2.1 e.2.2 *
        (integerEntry i (squareEquationNumber e) : R) = 0 := by
  let f (e : Fin 4096) : ℤ :=
    SparseRow.coefficient e.val (squareJacobianColumn x) * integerEntry i e
  have h : ∑ e : Fin 4096, f e = 0 := by
    simpa only [f, intFunctional, LinearMap.coe_mk, AddHom.coe_mk, decodeZ,
      JacobianTrace.original, Equiv.symm_apply_apply]
      using original_int annChecks checks i (squareVariableNumber x)
  have hsum : ∑ e : EquationIndex SquareVertex, f (squareEquationNumber e) = 0 :=
    (squareEquationNumber.sum_comp f).trans h
  have hcast := congrArg (Int.castRingHom R) hsum
  rw [map_sum, map_zero] at hcast
  refine Eq.trans (Finset.sum_congr rfl (fun e _ => ?_)) hcast
  dsimp only [f]
  rw [map_mul, squareJacobianColumn_correct]
  congr 1
  obtain ⟨s, m, a⟩ := x
  obtain ⟨b, c, d⟩ := e
  cases m <;>
    simp only [Decomposition.jacobianColumn_eq, strassenSquare, Decomposition.map] <;>
      split_ifs <;> simp

end Brent.QuadraticData
