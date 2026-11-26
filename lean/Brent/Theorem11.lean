import Brent.KernelCheck.MainTheorem
import Brent.KernelCheck.SquareJacobianRank
import Brent.KernelCheck.HilbertValues
import Brent.Formal.Completion
import Brent.Formal.Branches
import Brent.Formal.OrbitClosure
import Brent.LocalDimension

/-!
# Theorem 1.1, bundled (F20)

`Brent.main_theorem` states Theorem 1.1 of the paper clause by clause, over every field `k : Type`
of characteristic three or zero. The paper states it for `k = 𝔽̄₃` or `char k = 0`; the Lean
statement covers every field of characteristic three, which includes `𝔽̄₃`.

Clause map (paper → Lean):

1. `rk DΦ_p = 2101` → `square_jacobian_rank` (holds over every field).
2. `dim T_p Br_k = 251` → `square_jacobian_nullity` (kernel of the differential, every field) and
   `HilbertInitial.hilbertValue_one` (`dim 𝔪/𝔪²` of the scheme local ring, every field).
3. `dim_p V_k(4,4,4|49) = 197` → `squareLocalDimension_eq_197` (the scheme local ring) and
   `reduced_localDimension_eq_197` (its reduction; nilpotents do not change Krull dimension).
4. Orbit dimension 143 → `Formal.finrank_range_dOrbit` (rank of the differential of the
   146-parameter isotropy and term-rescaling orbit map at `p`, every field), and
   `Formal.OrbitClosure.orbitRing_dimension_eq_143` and
   `Formal.OrbitClosure.orbitClosure_dimension_eq_143` (geometric orbit closure over infinite fields).
5. Two distinct smooth 197-dimensional formal branches → `Formal.sqBranchPrime_ne`,
   `sqBranchPrime_minimal` (minimal primes of the `𝔪`-adic completion `SquareCompletion k` of the
   scheme local ring), `Formal.sqBranchQuotEquiv` (each quotient is a power series ring) and
   `Formal.card_branchVar` (in 197 variables).
6. Scheme-theoretic formal intersection of dimension 143 → `Formal.ringKrullDim_sqIntersection`
   and `Formal.sqIntersectionEquiv`: `SquareCompletion k ⧸ (𝔭_L + 𝔭_R)` is a power series ring in
   143 variables (`Formal.card_orbitVar`).
7. Hilbert function starts `(1, 251, 30978)` → `hilbert_initial_values`, for the scheme local ring
   `UpperBound.A k`, which is `SquareLocalRing k` by definition (`A_eq_squareLocalRing`).
-/

namespace Brent

/-- The ring of the Hilbert function statements is the scheme local ring at `p`. -/
theorem A_eq_squareLocalRing (k : Type) [Field k] : UpperBound.A k = SquareLocalRing k := rfl

/-- `dim_p` of the Brent scheme, in characteristic three or zero. -/
theorem squareLocalDimension_eq_197 (k : Type) [Field k] (hk : CharP k 3 ∨ CharZero k) :
    squareLocalDimension k = 197 := by
  rcases hk with hk | hk
  · exact squareLocalDimension_eq_197_of_charThree k
  · exact squareLocalDimension_eq_197_of_charZero k

/-- `dim_p` of the reduced Brent variety: the reduction of the local ring has the same dimension. -/
theorem reduced_localDimension_eq_197 (k : Type) [Field k] (hk : CharP k 3 ∨ CharZero k) :
    ringKrullDim (SquareLocalRing k ⧸ nilradical (SquareLocalRing k)) = 197 := by
  rw [quotient_dimension_of_le_nilradical _ le_rfl]
  exact squareLocalDimension_eq_197 k hk

/-- Both branch primes are minimal primes of the completion. -/
theorem sqBranchPrime_minimal (k : Type) [Field k] (hk : CharP k 3 ∨ CharZero k) (left : Bool) :
    Formal.sqBranchPrime k left ∈ minimalPrimes (SquareCompletion k) := by
  rcases hk with hk | hk
  · exact Formal.sqBranchPrime_minimal_charThree k left
  · exact Formal.sqBranchPrime_minimal_charZero k left

/-- The initial local Hilbert values of the scheme local ring. -/
theorem hilbert_initial_values (k : Type) [Field k] (hk : CharP k 3 ∨ CharZero k) :
    hilbertValue k (UpperBound.A k) 0 = 1 ∧ hilbertValue k (UpperBound.A k) 1 = 251 ∧
      hilbertValue k (UpperBound.A k) 2 = 30978 := by
  rcases hk with hk | hk
  · exact HilbertValues.hilbert_initial_charP_three k
  · exact HilbertValues.hilbert_initial_charZero k

/-- **Theorem 1.1.** Over every field of characteristic three or zero, at the recursive point `p`:
the Jacobian has rank 2101 and the tangent space dimension 251; the local dimension is 197 (for
the scheme and for its reduction); the isotropy and term-rescaling orbit has dimension 143; the
completion has two distinct minimal primes whose quotients are power series rings in 197
variables, and their sum cuts out a power series ring in 143 variables, of dimension 143; the
local Hilbert function starts `(1, 251, 30978)`. -/
theorem main_theorem (k : Type) [Field k] (hk : CharP k 3 ∨ CharZero k) :
    Module.finrank k (Submodule.span k (Set.range (fun x : Variable SquareVertex SquareSummand =>
      fun e : EquationIndex SquareVertex =>
        (strassenSquare k).jacobianColumn x e.1 e.2.1 e.2.2))) = 2101 ∧
    Module.finrank k (LinearMap.ker (squareDifferential k)) = 251 ∧
    hilbertValue k (UpperBound.A k) 1 = 251 ∧
    squareLocalDimension k = 197 ∧
    ringKrullDim (SquareLocalRing k ⧸ nilradical (SquareLocalRing k)) = 197 ∧
    Module.finrank k (LinearMap.range (Formal.dOrbit k)) = 143 ∧
    ringKrullDim (Formal.OrbitClosure.OrbitRing k) = 143 ∧
    (Infinite k → ringKrullDim (MvPolynomial Formal.Var k ⧸
      Formal.Component.vanishingIdeal k (Formal.OrbitClosure.orbitClosure k)) = 143) ∧
    Formal.sqBranchPrime k true ≠ Formal.sqBranchPrime k false ∧
    (∀ left : Bool, Formal.sqBranchPrime k left ∈ minimalPrimes (SquareCompletion k) ∧
      Nonempty ((SquareCompletion k ⧸ Formal.sqBranchPrime k left) ≃+*
        MvPowerSeries (Formal.BranchVar k left) k) ∧
      Fintype.card (Formal.BranchVar k left) = 197) ∧
    ringKrullDim (SquareCompletion k ⧸
      (Formal.sqBranchPrime k true ⊔ Formal.sqBranchPrime k false)) = 143 ∧
    Nonempty ((SquareCompletion k ⧸ (Formal.sqBranchPrime k true ⊔ Formal.sqBranchPrime k false))
      ≃+* MvPowerSeries (Formal.OrbitVar k) k) ∧
    Fintype.card (Formal.OrbitVar k) = 143 ∧
    (hilbertValue k (UpperBound.A k) 0 = 1 ∧ hilbertValue k (UpperBound.A k) 1 = 251 ∧
      hilbertValue k (UpperBound.A k) 2 = 30978) :=
  ⟨square_jacobian_rank k, square_jacobian_nullity k, HilbertInitial.hilbertValue_one k,
    squareLocalDimension_eq_197 k hk, reduced_localDimension_eq_197 k hk,
    Formal.finrank_range_dOrbit k, Formal.OrbitClosure.orbitRing_dimension_eq_143 k,
    (fun hi => by letI := hi; exact Formal.OrbitClosure.orbitClosure_dimension_eq_143 k),
    Formal.sqBranchPrime_ne k,
    fun left => ⟨sqBranchPrime_minimal k hk left, ⟨Formal.sqBranchQuotEquiv k left⟩,
      Formal.card_branchVar k left⟩,
    Formal.ringKrullDim_sqIntersection k, ⟨Formal.sqIntersectionEquiv k⟩, Formal.card_orbitVar k,
    hilbert_initial_values k hk⟩

end Brent
