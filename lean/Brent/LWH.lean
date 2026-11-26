import Brent.LWH.Orbit
import Brent.Generated.LWHChecks
import Brent.Generated.LWHKernelChecks
import Brent.Generated.LWHSolves

/-!
# §7: the Li–Wang–Hu comparison point (paper lines 652–656)

The point is the AlphaTensor rank-49 decomposition selected in Section 5.2.2 of
X. Li, Y. Wang, S. Hu, *Substitution and quotient of the isotropy group action*
(arXiv:2607.15069v2; `s526.ipynb` in their repository), which is entry 1403 of DeepMind's
catalogue of 14,236 factorizations. (Their Section 5.3 uses a different, singular point with
Jacobian nullity 198.) Over every field of characteristic three or zero:

* the integer Brent identity holds (`solves`);
* the Jacobian has rank 2155 (`jacobian_rank`), so the tangent space has dimension 197
  (`tangent_dimension`);
* the 146 isotropy and term-scaling generators are tangent (`orbit_in_tangent`, over every field)
  and span 143 dimensions (`orbit_tangent_dimension`, in fact over every field).

The rank uses a mod-3 elimination trace for a `2155 × 2155` minor (`Brent/Generated/LWHBlocks`)
and 197 integer kernel vectors (`Brent/Generated/LWHKernelChecks`), both replayed by the kernel.
-/

open scoped Matrix

namespace Brent.LWH

/-- The Brent entries at the point. -/
def brentEntry (a b c : SquareVertex × SquareVertex) : ℤ := pointDec.entry a b c

/-- The matrix multiplication tensor. -/
def T (a b c : SquareVertex × SquareVertex) : ℤ := matrixMultiplicationEntry ℤ a b c

/-- The Jacobian of the Brent equations at the point over `K`. -/
noncomputable def jac (K : Type) [Field K] :
    Matrix (EquationIndex SquareVertex) (Variable SquareVertex SquareSummand) K := jacK K

theorem solves : ∀ a b c, brentEntry a b c = T a b c := pointDec_solves

theorem jacobian_rank (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) : (jac K).rank = 2155 :=
  jacK_rank kerChecked (det_minor_ne_zero checked K hK)

theorem tangent_dimension (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    Module.finrank K (LinearMap.ker (jac K).mulVecLin) = 197 :=
  jacK_nullity kerChecked (det_minor_ne_zero checked K hK)

theorem orbit_in_tangent (K : Type) [Field K] (i : Fin 146) : jac K *ᵥ orbitGens K i = 0 :=
  orbitGens_tangent K pointDec_solves i

/-- The hypothesis on the characteristic is not needed: the orbit minor has diagonal `±1`. -/
theorem orbit_tangent_dimension (K : Type) [Field K] (_hK : CharP K 3 ∨ CharZero K) :
    Module.finrank K (Submodule.span K (Set.range (orbitGens K))) = 143 :=
  orbit_finrank K

/-- **§7, Li–Wang–Hu point, all clauses.** -/
theorem lwh_point (K : Type) [Field K] (hK : CharP K 3 ∨ CharZero K) :
    (∀ a b c, brentEntry a b c = T a b c) ∧ (jac K).rank = 2155 ∧
    Module.finrank K (LinearMap.ker (jac K).mulVecLin) = 197 ∧
    (∀ i, jac K *ᵥ orbitGens K i = 0) ∧
    Module.finrank K (Submodule.span K (Set.range (orbitGens K))) = 143 :=
  ⟨solves, jacobian_rank K hK, tangent_dimension K hK, orbit_in_tangent K,
    orbit_tangent_dimension K hK⟩

end Brent.LWH
