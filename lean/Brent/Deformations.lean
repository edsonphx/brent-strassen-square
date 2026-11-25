import Brent.StrassenSquare
import Mathlib.Data.Matrix.Basic

open scoped BigOperators

namespace Brent.Decomposition

variable {R α ι : Type*} [CommRing R] [DecidableEq α] [Fintype α] [Fintype ι]

private def pairing (f : α × α → R) (X : Matrix α α R) : R :=
  ∑ a, f a * X a.1 a.2

private def asMatrix (f : α × α → R) : Matrix α α R := fun i j => f (i, j)

private def entries (X : Matrix α α R) : α × α → R := fun a => X a.1 a.2

private def evaluate (d : Decomposition R α ι) (X Y : Matrix α α R) : Matrix α α R :=
  ∑ s, (pairing (d.u s) X * pairing (d.v s) Y) • asMatrix (d.w s)

omit [DecidableEq α] in
private lemma evaluate_apply (d : Decomposition R α ι) (X Y : Matrix α α R) (i j : α) :
    evaluate d X Y i j = ∑ a : α × α, ∑ b : α × α, d.entry a b (i, j) * X a.1 a.2 * Y b.1 b.2 := by
  simp only [evaluate, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pairing, asMatrix, entry]
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ s : ι, ∑ a : α × α, ∑ b : α × α,
        d.u s a * X a.1 a.2 * (d.v s b * Y b.1 b.2) * d.w s (i, j) := by
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  ring

private def matrixUnit (a : α × α) : Matrix α α R :=
  fun i j => if (i, j) = a then 1 else 0

private lemma solves_iff_evaluate (d : Decomposition R α ι) :
    d.Solves ↔ ∀ X Y, evaluate d X Y = X * Y := by
  constructor
  · intro hd X Y
    ext i j
    rw [evaluate_apply, Matrix.mul_apply]
    have he : ∀ a b, d.entry a b (i, j) = matrixMultiplicationEntry R a b (i, j) :=
      fun a b => hd a b (i, j)
    simp_rw [he, matrixMultiplicationEntry, Fintype.sum_prod_type]
    simp only [ite_and, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  · intro h a b c
    have h' := congrFun (congrFun (h (matrixUnit a) (matrixUnit b)) c.1) c.2
    rw [evaluate_apply, Matrix.mul_apply] at h'
    simp only [matrixUnit, mul_ite, mul_zero, mul_one, Prod.ext_iff] at h'
    -- The standard matrix units pick the two prescribed input coordinates.
    have h'' : d.entry a b c =
        (if c.2 = b.2 then if c.1 = a.1 then if b.1 = a.2 then 1 else 0 else 0 else 0) := by
      simpa [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] using h'
    rw [h'', matrixMultiplicationEntry]
    simp only [eq_comm (a := a.2) (b := b.1), eq_comm (a := a.1) (b := c.1),
      eq_comm (a := b.2) (b := c.2)]
    split_ifs <;> simp_all

omit [DecidableEq α] in
private lemma pairing_transport (f : α × α → R) (P Q X : Matrix α α R) :
    pairing (entries (P.transpose * asMatrix f * Q.transpose)) X =
      pairing f (P * X * Q) := by
  classical
  simp only [pairing, entries, asMatrix, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  let term (a b : α × α) := P a.1 b.1 * f a * Q b.2 a.2 * X b.1 b.2
  calc
    (∑ i : α, ∑ j : α, ∑ l : α, ∑ k : α,
      P k i * f (k, l) * Q j l * X i j) =
        ∑ b : α × α, ∑ a : α × α, term a b := by
      simp only [Fintype.sum_prod_type, term]
      congr! 2 with i j
      rw [Finset.sum_comm]
    _ = ∑ a : α × α, ∑ b : α × α, term a b := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, term]
      congr! 2 with k l
      rw [Finset.sum_comm]
      congr! 2
      ring

/-- The three vertex changes of basis, with the output in the paper's convention. -/
def changeBasis (d : Decomposition R α ι) (P Q T : (Matrix α α R)ˣ) :
    Decomposition R α ι where
  u s := entries (P.val.transpose * asMatrix (d.u s) * Q.inv.transpose)
  v s := entries (Q.val.transpose * asMatrix (d.v s) * T.inv.transpose)
  w s := entries (P.inv * asMatrix (d.w s) * T.val)

omit [Fintype ι] in
@[simp]
theorem changeBasis_identity (d : Decomposition R α ι) :
    d.changeBasis 1 1 1 = d := by
  cases d
  simp [changeBasis, Matrix.transpose_one]
  exact ⟨rfl, rfl, rfl⟩

private lemma evaluate_changeBasis (d : Decomposition R α ι) (P Q T : (Matrix α α R)ˣ)
    (X Y : Matrix α α R) :
    evaluate (d.changeBasis P Q T) X Y =
      P.inv * evaluate d (P.val * X * Q.inv) (Q.val * Y * T.inv) * T.val := by
  simp only [evaluate, changeBasis, pairing_transport]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- An exact Brent solution is preserved by vertex changes. -/
theorem solves_changeBasis {d : Decomposition R α ι} (hd : d.Solves)
    (P Q T : (Matrix α α R)ˣ) : (d.changeBasis P Q T).Solves := by
  rw [solves_iff_evaluate]
  intro X Y
  rw [evaluate_changeBasis, (solves_iff_evaluate d).mp hd]
  calc
    _ = (P.inv * P.val) * X * (Q.inv * Q.val) * Y * (T.inv * T.val) := by
      simp only [mul_assoc]
    _ = X * Y := by simp

/-- Independent rescalings of each summand with product one. -/
def rescale (d : Decomposition R α ι) (l m : ι → Rˣ) : Decomposition R α ι where
  u s a := (l s).val * d.u s a
  v s a := (m s).val * d.v s a
  w s a := ↑((l s)⁻¹) * ↑((m s)⁻¹) * d.w s a

omit [Fintype α] in
theorem solves_rescale {d : Decomposition R α ι} (hd : d.Solves) (l m : ι → Rˣ) :
    (d.rescale l m).Solves := by
  intro a b c
  rw [← hd a b c]
  apply Finset.sum_congr rfl
  intro s _
  change ((l s).val * d.u s a) * ((m s).val * d.v s b) *
    (↑((l s)⁻¹) * ↑((m s)⁻¹) * d.w s c) = _
  calc
    _ = ((l s).val * ↑((l s)⁻¹)) * ((m s).val * ↑((m s)⁻¹)) *
        (d.u s a * d.v s b * d.w s c) := by ring
    _ = _ := by simp

end Brent.Decomposition

namespace Brent

private def baseStrassen (R : Type*) [CommRing R] : Decomposition R (Fin 2) (Fin 7) :=
  strassen.map (Int.castRingHom R)

private theorem baseStrassen_solves (R : Type*) [CommRing R] : (baseStrassen R).Solves :=
  Decomposition.solves_map _ strassen_solves

/-- The independent inner block changes in the first recursive family. -/
def leftFamily {R : Type*} [CommRing R] (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    Decomposition R SquareVertex SquareSummand :=
  (baseStrassen R).recursiveLeft (fun i => (baseStrassen R).changeBasis (P i) (Q i) (T i))

theorem leftFamily_solves {R : Type*} [CommRing R]
    (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) : (leftFamily P Q T).Solves :=
  Decomposition.solves_recursiveLeft (baseStrassen_solves R)
    (fun i => Decomposition.solves_changeBasis (baseStrassen_solves R) (P i) (Q i) (T i))

/-- The independent outer block changes in the second recursive family. -/
def rightFamily {R : Type*} [CommRing R] (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    Decomposition R SquareVertex SquareSummand :=
  Decomposition.recursiveRight
    (fun j => (baseStrassen R).changeBasis (P j) (Q j) (T j)) (baseStrassen R)

theorem rightFamily_solves {R : Type*} [CommRing R]
    (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) : (rightFamily P Q T).Solves :=
  Decomposition.solves_recursiveRight
    (fun j => Decomposition.solves_changeBasis (baseStrassen_solves R) (P j) (Q j) (T j)) (baseStrassen_solves R)

private theorem left_recursive_base (R : Type*) [CommRing R] :
    (baseStrassen R).recursiveLeft (fun _ => baseStrassen R) = strassenSquare R := by
  simp [baseStrassen, strassenSquare, strassenSquareInt, Decomposition.recursiveLeft,
    Decomposition.map, map_mul]

/-- The common identity parameter values of both algebraic families are the marked point. -/
theorem leftFamily_at_identity (R : Type*) [CommRing R] :
    leftFamily (R := R) (fun _ => 1) (fun _ => 1) (fun _ => 1) = strassenSquare R := by
  simp only [leftFamily, Decomposition.changeBasis_identity, left_recursive_base]

theorem rightFamily_at_identity (R : Type*) [CommRing R] :
    rightFamily (R := R) (fun _ => 1) (fun _ => 1) (fun _ => 1) = strassenSquare R := by
  simp only [rightFamily, Decomposition.changeBasis_identity]
  exact left_recursive_base R

end Brent
