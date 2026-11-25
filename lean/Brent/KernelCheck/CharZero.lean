import Brent.KernelCheck.UpperBound
import Brent.GradedTransfer
import Brent.Generated.AnnihilatorChecks
import Brent.Generated.LiftChecks
import Mathlib.Algebra.Field.ZMod

/-!
# The upper bound in characteristic zero

The 54 certified covectors lift to exact integer covectors `μ` in the left kernel of the
Jacobian (`Brent.QuadraticData.integer_annihilates`). Over a field of characteristic zero they
give 54 quadratic relations among the tangent coordinates, with integer coefficient tables
`B`, whose reductions modulo three are the certified characteristic-three tables. The graded
transfer theorem `Brent.Transfer.charZero_dim_le` then gives `dim ≤ 197`.
-/

open MvPolynomial IsLocalRing
open scoped BigOperators

namespace Brent.CharZeroBound

instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

open TangentData QuadraticData CharThree UpperBound

/-- The integer bilinear tables of the lifted covectors on the tangent frame. -/
def B (ell : Fin 54) (i j : Fin 251) : ℤ :=
  ∑ e : EquationIndex SquareVertex,
    (strassenSquare ℤ).bilinearEntry (frameDirection ℤ i) (frameDirection ℤ j) e.1 e.2.1 e.2.2 *
      integerEntry ell (squareEquationNumber e)

theorem strassenSquare_int_map (R : Type) [CommRing R] :
    (strassenSquare ℤ).map (Int.castRingHom R) = strassenSquare R := by
  rw [strassenSquare, strassenSquare, Decomposition.map_map']
  congr 1

theorem frameDirection_int_map (R : Type) [CommRing R] (i : Fin 251) :
    (frameDirection ℤ i).map (Int.castRingHom R) = frameDirection R i := by
  apply Decomposition.eq_of_components <;> funext s a <;>
    simp [frameDirection, Decomposition.map]

theorem B_cast (R : Type) [CommRing R] (ell : Fin 54) (i j : Fin 251) :
    ((B ell i j : ℤ) : R) = ∑ e : EquationIndex SquareVertex,
      (strassenSquare R).bilinearEntry (frameDirection R i) (frameDirection R j) e.1 e.2.1 e.2.2 *
        (integerEntry ell (squareEquationNumber e) : R) := by
  rw [B, Int.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Int.cast_mul, ← strassenSquare_int_map R, ← frameDirection_int_map R i,
    ← frameDirection_int_map R j, Decomposition.bilinearEntry_map, eq_intCast]

/-- The lifted covectors over `k`. -/
noncomputable def mu (k : Type) [Field k] (ell : Fin 54) (e : EquationIndex SquareVertex) : k :=
  (integerEntry ell (squareEquationNumber e) : k)

theorem mu_annihilate (k : Type) [Field k] (ell : Fin 54) (x : Variable SquareVertex SquareSummand) :
    ∑ e : EquationIndex SquareVertex, J k x e * mu k ell e = 0 :=
  integer_annihilates checkedAnnihilator checkedLift k ell x

theorem β_mu (k : Type) [Field k] (ell : Fin 54) (i j : Fin 251) :
    UpperBound.β k (mu k ell) i j = ((B ell i j : ℤ) : k) := by
  rw [B_cast]; rfl

theorem castK_self (x : ZMod 3) : castK (ZMod 3) x = x := by
  simp [castK]

theorem mu_mod_three (ell : Fin 54) : mu (ZMod 3) ell = lam (ZMod 3) ell := by
  funext e
  rw [mu, lam, castK_self, integerEntry_cast]

theorem B_mod_three (ell : Fin 54) (i j : Fin 251) :
    ((B ell i j : ℤ) : ZMod 3) = UpperBound.β (ZMod 3) (lam (ZMod 3) ell) i j := by
  rw [← β_mu, mu_mod_three]

theorem B_diag (ell : Fin 54) (i : Fin 251) : ((B ell i i : ℤ) : ZMod 3) = 0 := by
  rw [B_mod_three, β_diag]

theorem B_polar (ell : Fin 54) (i j : Fin 251) :
    ((B ell i j + B ell j i : ℤ) : ZMod 3) = projectedPolar ell i j := by
  rw [Int.cast_add, B_mod_three, B_mod_three, β_polar, castK_self]

theorem B_nonmixed (ell : Fin 54) (i j : Fin 251) (hij : i < j)
    (h : ¬ (143 ≤ i.val ∧ i.val < 197 ∧ 197 ≤ j.val)) : projectedPolar ell i j = 0 := by
  apply archived_nonmixed_zero
  rintro (h' | h')
  · exact h h'
  · have : i.val < j.val := hij
    omega

variable (k : Type) [Field k]

theorem rel_B (ell : Fin 54) :
    ∑ i, ∑ j, z k i * z k j * ((B ell i j : ℤ) : A k) ∈ maximalIdeal (A k) ^ 3 := by
  have h := quad_rel_Z k (mu k ell) (mu_annihilate k ell)
  rw [expand] at h
  have e : ∀ i j, ((B ell i j : ℤ) : A k) = algebraMap k (A k) (UpperBound.β k (mu k ell) i j) := by
    intro i j
    rw [β_mu, map_intCast]
  simp only [e]
  exact h

theorem gen_z : maximalIdeal (A k) ≤ Ideal.span (Set.range (z k)) ⊔ maximalIdeal (A k) ^ 2 := by
  refine (gen k).trans (sup_le_sup_right (sup_le (sup_le ?_ ?_) ?_) _) <;>
    rw [Ideal.span_le] <;> rintro _ ⟨a, rfl⟩ <;> exact Ideal.subset_span ⟨_, rfl⟩

theorem unit_of_charZero [CharZero k] (t : ℤ) (ht : t ≠ 0) : IsUnit (t : A k) := by
  have e : algebraMap k (A k) (t : k) = (t : A k) :=
    eq_intCast ((algebraMap k (A k)).comp (Int.castRingHom k)) t
  rw [← e]
  exact (IsUnit.mk0 _ (Int.cast_ne_zero.mpr ht)).map _

theorem ringKrullDim_le [CharZero k] : ringKrullDim (A k) ≤ ((143 + 54 : ℕ) : WithBot ℕ∞) :=
  Transfer.charZero_dim_le (unit_of_charZero k) (z k) (z_mem k) (gen_z k) B (rel_B k)
    projectedPolar B_diag B_polar B_nonmixed quadraticMatching quadraticMatching_bijective.2
    (fun ell => (archived_polar_leading ell).1) (fun ell => (archived_polar_leading ell).2)

/-- **Upper bound.** Over a field of characteristic zero, `dim_p V(4,4,4 | 49) ≤ 197`. -/
theorem squareLocalDimension_le_197 [CharZero k] : squareLocalDimension k ≤ 197 := by
  have h := ringKrullDim_le k
  exact h

end Brent.CharZeroBound
