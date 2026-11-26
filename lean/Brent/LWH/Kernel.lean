import Brent.LWH.Trace
import Brent.SparseContraction
import Brent.Formal.SmoothLeftPoint

/-!
# Jacobian rank 2155 and tangent dimension 197 at the Li–Wang–Hu point

The 197 variables outside the pivot columns of `Brent.LWH.Trace` are free. For each free
variable there is an integer kernel vector of the Jacobian equal to `1` on it and `0` on the
other free variables (the unit solutions are integral). The kernel identity `J v = 0` is checked
over `ℤ` by the bounded-radix replay, in kernel batches (`Brent.Generated.LWHKernelChecks`).
The 2155 × 2155 minor of the trace gives the rank lower bound; the 197 kernel vectors give the
nullity lower bound; rank–nullity closes both.
-/

open scoped BigOperators Matrix

namespace Brent.LWH

open SparseRow
open Brent.Formal.SmoothLeftPoint (differentialAt jacobianSpan range_differentialAt rank_add_nullity)

/-! ### Free variables -/

/-- The free variables. -/
def freeVar (i : Fin 197) : Variable SquareVertex SquareSummand := squareVariableNumber.symm (freeNum i)

set_option maxRecDepth 100000 in
theorem freeNum_injective : Function.Injective freeNum := by
  have h : ∀ i j : Fin 197, freeNum i = freeNum j → i = j := by decide +kernel
  exact fun i j => h i j

theorem freeVar_injective : Function.Injective freeVar :=
  fun i j h => freeNum_injective (squareVariableNumber.symm.injective h)

/-- Pivot column numbers, extended strictly monotonically past the end. -/
def colNumN (i : ℕ) : ℕ := if h : i < 2155 then (squareVariableNumber (col ⟨i, h⟩)).val else 2352 + i

set_option maxRecDepth 100000 in
theorem colNumN_succ_check : ∀ i : Fin 2155, colNumN i.val < colNumN (i.val + 1) := by
  decide +kernel

theorem colNumN_strictMono : StrictMono colNumN := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  by_cases h : i < 2155
  · exact colNumN_succ_check ⟨i, h⟩
  · have h' : ¬ i + 1 < 2155 := by omega
    simp only [colNumN, dif_neg h, dif_neg h']
    omega

set_option maxRecDepth 100000 in
theorem pos_check : ∀ f : Fin 197,
    (pos f = 0 ∨ colNumN (pos f - 1) < (freeNum f).val) ∧ (freeNum f).val < colNumN (pos f) := by
  decide +kernel

theorem freeVar_not_col (f : Fin 197) : freeVar f ∉ Set.range col := by
  rintro ⟨i, hi⟩
  have hnum : colNumN i.val = (freeNum f).val := by
    simp only [colNumN, dif_pos i.isLt, hi, freeVar, Equiv.apply_symm_apply]
  obtain ⟨hlo, hhi⟩ := pos_check f
  by_cases hp : pos f ≤ i.val
  · have := colNumN_strictMono.monotone hp
    omega
  · have hp' : i.val ≤ pos f - 1 := by omega
    have := colNumN_strictMono.monotone hp'
    rcases hlo with h0 | hlo
    · omega
    · omega

theorem col_injective : Function.Injective col := by
  intro i j h
  apply Fin.ext
  apply colNumN_strictMono.injective
  simp only [colNumN, dif_pos i.isLt, dif_pos j.isLt, h]

/-! ### Kernel vectors over `ℤ` -/

/-- The pivot part of kernel vector `i`: pairs (pivot row, value). -/
def kerPiv (i : Fin 197) : Row := SmoothL.unpack 1024 (pick kernelData i.val)

/-- Kernel vector `i` as a sparse row over variable numbers. -/
def kerRow (i : Fin 197) : Row :=
  ((freeNum i).val, 1) ::
    (kerPiv i).map fun x => ((squareVariableNumber (col (Fin.ofNat 2155 x.1))).val, x.2)

/-- The sparse Jacobian column of variable number `n`. -/
def columnN (n : Nat) : Row :=
  if h : n < 2352 then SmoothL.column pointDec (squareVariableNumber.symm ⟨n, h⟩) else []

/-- `J v = 0` for kernel vector `i`, as a bounded-radix identity. -/
def kerCheck (i : Fin 197) : Bool :=
  checkRadixStep 4096 kernelBits (fun j : Fin 197 => contract columnN (kerRow j))
    (fun _ => []) (fun _ => []) i

def kerCheckAt (i : Fin 200) : Bool := if h : i.val < 197 then kerCheck ⟨i.val, h⟩ else true

theorem kerRow_fits (i : Fin 197) : ∀ x ∈ kerRow i, x.1 < 2352 := by
  intro x hx
  simp only [kerRow, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨y, _, rfl⟩
  · exact (freeNum i).isLt
  · exact (squareVariableNumber _).isLt

/-- The kernel vectors over `ℤ`, as functions of the variables. -/
def kvec (i : Fin 197) (x : Variable SquareVertex SquareSummand) : ℤ :=
  coefficient (squareVariableNumber x).val (kerRow i)

theorem kvec_kernel (h : ∀ i, kerCheckAt i = true) (i : Fin 197) (e : EquationIndex SquareVertex) :
    ∑ x, pointDec.jacobianColumn x e.1 e.2.1 e.2.2 * kvec i x = 0 := by
  have hc : kerCheck i = true := by
    have := h ⟨i.val, by omega⟩
    simpa [kerCheckAt, i.isLt] using this
  have h0 := (checked_radix_step 4096 kernelBits _ _ _ i hc).2 (squareEquationNumber e)
  have h1 : coefficient (squareEquationNumber e).val (contract columnN (kerRow i)) = 0 := by
    simp only [coefficient, List.map_nil, List.sum_nil, sub_zero] at h0
    omega
  rw [coefficient_contract_dense columnN (kerRow i) 2352 _ (kerRow_fits i)] at h1
  rw [← h1, ← Equiv.sum_comp squareVariableNumber]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [columnN, dif_pos (squareVariableNumber x).isLt, Fin.eta, Equiv.symm_apply_apply,
    SmoothL.column_correct, kvec]
  ring

theorem kvec_free (i j : Fin 197) : kvec i (freeVar j) = if i = j then 1 else 0 := by
  have hz : coefficient (freeNum j).val ((kerPiv i).map fun x =>
      ((squareVariableNumber (col (Fin.ofNat 2155 x.1))).val, x.2)) = 0 := by
    rw [coefficient_indexedMap]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    dsimp only
    rw [if_neg]
    intro hx
    exact freeVar_not_col j ⟨Fin.ofNat 2155 x.1, (Equiv.eq_symm_apply _).mpr (Fin.ext hx)⟩
  simp only [kvec, freeVar, Equiv.apply_symm_apply, kerRow, coefficient, hz, add_zero]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (fun h => hij (freeNum_injective (Fin.ext h))), if_neg hij]

/-! ### Over a field -/

variable (K : Type) [Field K]

/-- The Li–Wang–Hu point over `K`. -/
noncomputable abbrev pointK : Decomposition K SquareVertex SquareSummand :=
  pointDec.map (Int.castRingHom K)

/-- The Jacobian matrix at the point over `K`: rows are equations, columns are variables. -/
noncomputable def jacK :
    Matrix (EquationIndex SquareVertex) (Variable SquareVertex SquareSummand) K :=
  Matrix.of fun e x => (pointK K).jacobianColumn x e.1 e.2.1 e.2.2

theorem jacobianColumn_pointK (x : Variable SquareVertex SquareSummand)
    (e : EquationIndex SquareVertex) :
    (pointK K).jacobianColumn x e.1 e.2.1 e.2.2 = (pointDec.jacobianColumn x e.1 e.2.1 e.2.2 : K) :=
  Decomposition.jacobianColumn_map (Int.castRingHom K) pointDec x e.1 e.2.1 e.2.2

theorem jacK_apply (e : EquationIndex SquareVertex) (x : Variable SquareVertex SquareSummand) :
    jacK K e x = (pointDec.jacobianColumn x e.1 e.2.1 e.2.2 : K) := by
  rw [jacK, Matrix.of_apply, jacobianColumn_pointK]

theorem jacK_mulVecLin : (jacK K).mulVecLin = differentialAt K (pointK K) := rfl

/-- The kernel vectors over `K`. -/
noncomputable def kvecK (i : Fin 197) : Variable SquareVertex SquareSummand → K :=
  fun x => (kvec i x : K)

theorem kvecK_mem (h : ∀ i, kerCheckAt i = true) (i : Fin 197) : jacK K *ᵥ kvecK K i = 0 := by
  funext e
  have h0 := congrArg (fun z : ℤ => (z : K)) (kvec_kernel h i e)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at h0
  simpa only [Matrix.mulVec, dotProduct, jacK_apply, kvecK, Pi.zero_apply] using h0

theorem kvecK_independent : LinearIndependent K (kvecK K) := by
  apply LinearIndependent.of_comp (LinearMap.funLeft K K freeVar)
  have hcomp : (LinearMap.funLeft K K freeVar) ∘ kvecK K = fun i => Pi.single i (1 : K) := by
    funext i j
    simp only [Function.comp_apply, LinearMap.funLeft_apply, kvecK, kvec_free]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hcomp]
  exact Pi.linearIndependent_single_one (Fin 197) K

theorem nullity_ge (h : ∀ i, kerCheckAt i = true) :
    197 ≤ Module.finrank K (LinearMap.ker (differentialAt K (pointK K))) := by
  have hc := finrank_span_eq_card (kvecK_independent K)
  rw [Fintype.card_fin] at hc
  rw [← hc]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, ← jacK_mulVecLin, Matrix.mulVecLin_apply]
  exact kvecK_mem K h i

variable {K}

theorem rank_ge (hdet : (minorInt.map (Int.castRingHom K)).det ≠ 0) :
    2155 ≤ Module.finrank K (jacobianSpan K (pointK K)) := by
  let colVec : Fin 2155 → EquationIndex SquareVertex → K := fun i e =>
    (pointK K).jacobianColumn (col i) e.1 e.2.1 e.2.2
  have hli : LinearIndependent K colVec := by
    have hu : IsUnit (minorInt.map (Int.castRingHom K)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hrow : LinearIndependent K (minorInt.map (Int.castRingHom K)).row :=
      Matrix.linearIndependent_rows_of_isUnit hu
    apply LinearIndependent.of_comp (LinearMap.funLeft K K eqn)
    convert hrow using 1
    funext i j
    simp only [colVec, Function.comp_apply, LinearMap.funLeft_apply, jacobianColumn_pointK,
      Matrix.row, Matrix.map_apply, minorInt, Matrix.of_apply]
    rfl
  have hc := finrank_span_eq_card hli
  rw [Fintype.card_fin] at hc
  rw [← hc]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨col i, rfl⟩

/-- **Jacobian rank 2155**, given the two kernel-checked certificates. -/
theorem jacK_rank (hchk : ∀ i, kerCheckAt i = true)
    (hdet : (minorInt.map (Int.castRingHom K)).det ≠ 0) : (jacK K).rank = 2155 := by
  have h1 := rank_add_nullity K (pointK K)
  have h2 := nullity_ge K hchk
  have h3 := rank_ge hdet
  have hr : (jacK K).rank = Module.finrank K (jacobianSpan K (pointK K)) := by
    rw [Matrix.rank, jacK_mulVecLin, range_differentialAt]
  omega

/-- **Tangent dimension 197.** -/
theorem jacK_nullity (hchk : ∀ i, kerCheckAt i = true)
    (hdet : (minorInt.map (Int.castRingHom K)).det ≠ 0) :
    Module.finrank K (LinearMap.ker (jacK K).mulVecLin) = 197 := by
  have hr : (jacK K).rank = 2155 := jacK_rank hchk hdet
  rw [Matrix.rank, jacK_mulVecLin, range_differentialAt] at hr
  have h := rank_add_nullity K (pointK K)
  rw [hr] at h
  rw [jacK_mulVecLin]
  exact Nat.add_left_cancel (show 2155 + _ = 2155 + 197 from h)

end Brent.LWH
