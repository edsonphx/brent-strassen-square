import Brent.CM.LiftInstance
import Brent.KernelCheck.QuadraticCertificates

/-!
# The lifted quadrics `q̃ᵢ` over `ℤ₍₃₎` (paper lines 508–520)

DRAFT, NOT YET COMPILED.

Paper: *Lift the 54 rows `λᵢ` into the left kernel over `R₀`. … The lifted residual equations
again have quadratic initial parts `q̃ᵢ` because the lifted rows kill all linear terms. Their
reductions are the certified `qᵢ`.*

The quadratic part of the residual equation of a row `λ` is `Σ_{i,j} (Σ_e M_{ij}(e) λ(e)) xᵢ yⱼ`,
with the integer mixed second derivatives `M_{ij}(e) = mixedEntry i j e` of the Brent equations
(over `𝔽₃` this is `projectedMixed`, the coefficients of `qᵢ`). So for rows `λ̃ℓ` over `R₀`:

* `qtOf λ̃ ℓ`: the lifted quadric `q̃ℓ` built from `λ̃ℓ`;
* `map_qtOf`: **if `λ̃ℓ` reduces to `λℓ` modulo 3, then `q̃ℓ` reduces to `qℓ`**, because
  reduction is a ring map and `M_{ij}(e)` is integral;
* `qtOf_regular`: hence (`lifted_quadrics_regular`) the `q̃ℓ` are a regular sequence on
  `ℤ₍₃₎[x, y]_(3,x,y)` and on every flat module over it;
* `lamCanon`, `map_lamCanon`: a lift of the rows always exists (lift each coefficient through
  `ℕ`); the paper's `λ̃ℓ` lie in the left kernel over `R₀` in addition, which is only used for
  "the lifted rows kill all linear terms" and not for the regularity.
-/

open scoped BigOperators

namespace Brent.CM.LiftedQuadrics

open Brent Brent.QuadraticData Brent.Groebner.Paper Brent.Z3 Brent.CM.LiftInstance

/-- **The lifted quadric** attached to rows `λ̃ : Fin 54 → Fin 4096 → R₀`:
`q̃ℓ = Σ_{i,j} (Σ_e M_{ij}(e) λ̃ℓ(e)) xᵢ yⱼ`. -/
noncomputable def qtOf (lam : Fin 54 → Fin 4096 → R0) (ell : Fin 54) :
    MvPolynomial (Fin 54 ⊕ Fin 54) R0 :=
  ∑ i, ∑ j, MvPolynomial.monomial (e i j)
    (∑ x : EquationIndex SquareVertex, (mixedEntry i j x : R0) * lam ell (squareEquationNumber x))

/-- **Reduction of the lifted quadrics.** If the rows reduce to the certified covectors, the
lifted quadrics reduce to the certified `qℓ`. -/
theorem map_qtOf {lam : Fin 54 → Fin 4096 → R0}
    (hlam : ∀ ell x, rho3 (lam ell x) = functionalEntry ell x) (ell : Fin 54) :
    MvPolynomial.map rho3 (qtOf lam ell) = q ell := by
  rw [q_eq, qtOf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.map_monomial, projectedMixed, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_intCast, hlam]

/-- **Step E for the lifted quadrics.** -/
theorem qtOf_regular {lam : Fin 54 → Fin 4096 → R0}
    (hlam : ∀ ell x, rho3 (lam ell x) = functionalEntry ell x)
    (M₂ : Type*) [AddCommGroup M₂] [Module (Loc rho3 (σ := Fin 54 ⊕ Fin 54)) M₂]
    [Module.Flat (Loc rho3 (σ := Fin 54 ⊕ Fin 54)) M₂] :
    IsWeaklyRegular M₂ ((List.ofFn (qtOf lam)).map
      (algebraMap (P R0 (Fin 54 ⊕ Fin 54)) (Loc rho3 (σ := Fin 54 ⊕ Fin 54)))) :=
  lifted_quadrics_regular (qtOf lam) (map_qtOf hlam) M₂

/-- A lift of the 54 rows: each coefficient in `𝔽₃` lifted through `ℕ`. -/
noncomputable def lamCanon (ell : Fin 54) (x : Fin 4096) : R0 :=
  ((functionalEntry ell x).val : R0)

theorem map_lamCanon (ell : Fin 54) (x : Fin 4096) :
    rho3 (lamCanon ell x) = functionalEntry ell x := by
  rw [lamCanon, map_natCast, ZMod.natCast_zmod_val]

/-- The quadrics lifted along `lamCanon` are a regular sequence over `ℤ₍₃₎`. -/
theorem qtCanon_regular (M₂ : Type*) [AddCommGroup M₂]
    [Module (Loc rho3 (σ := Fin 54 ⊕ Fin 54)) M₂]
    [Module.Flat (Loc rho3 (σ := Fin 54 ⊕ Fin 54)) M₂] :
    IsWeaklyRegular M₂ ((List.ofFn (qtOf lamCanon)).map
      (algebraMap (P R0 (Fin 54 ⊕ Fin 54)) (Loc rho3 (σ := Fin 54 ⊕ Fin 54)))) :=
  qtOf_regular map_lamCanon M₂

end Brent.CM.LiftedQuadrics
