import Brent.Formal.SmoothFamily
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The Zariski closures of the two family images (§7, lines 610–620)

The family image of orientation `left` is the set of coordinate vectors
`(pq.value left).coordinates` for all parameters `pq`: three global `GL₄` changes, 21 block
`GL₂` changes and 98 term scalings. A generic parameter lives over
`R = k[Y] [1/D]`, where `Y` are the 230 entries and `D` is the product of all determinants and
scalings. The family comorphism `ψ : k[x] → R` sends a coordinate to its value at the generic
parameter. Over an infinite field a polynomial vanishes on the image iff it lies in `ker ψ`.
Since `R` is a domain, `ker ψ` is prime, which makes the Zariski closure irreducible.
-/

open MvPolynomial
open scoped BigOperators

namespace Brent.Formal.FamilyClosure

open Brent Brent.Formal

set_option linter.unusedSectionVars false

instance : DecidableEq GrpIdx := instDecidableEqSum

variable (k : Type) [Field k]

/-- Polynomials in the 230 parameter entries. -/
abbrev P := MvPolynomial GrpIdx k

noncomputable def gMat (g : Fin 3) : Matrix SquareVertex SquareVertex (P k) :=
  Matrix.of fun a b => X (.inl (.inl (g, a, b)))

noncomputable def bMat (l : Fin 7) (g : Fin 3) : Matrix (Fin 2) (Fin 2) (P k) :=
  Matrix.of fun i j => X (.inr (l, g, i, j))

noncomputable def sVar (s : SquareSummand) (c : Fin 2) : P k := X (.inl (.inr (s, c)))

/-- The product of all determinants and scalings. -/
noncomputable def D : P k :=
  (∏ g, (gMat k g).det) * (∏ l, ∏ g, (bMat k l g).det) * ∏ s, ∏ c, sVar k s c

/-- The coordinate ring of the parameter group. -/
abbrev R := Localization.Away (D k)

theorem isUnit_of_dvd_D {f : P k} (h : f ∣ D k) : IsUnit (algebraMap (P k) (R k) f) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit (D k))

theorem gMat_dvd (g : Fin 3) : (gMat k g).det ∣ D k :=
  Dvd.dvd.mul_right (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ g)) _) _

theorem bMat_dvd (l : Fin 7) (g : Fin 3) : (bMat k l g).det ∣ D k :=
  Dvd.dvd.mul_right (Dvd.dvd.mul_left
    ((Finset.dvd_prod_of_mem (fun g => (bMat k l g).det) (Finset.mem_univ g)).trans
    (Finset.dvd_prod_of_mem (fun l => ∏ g, (bMat k l g).det) (Finset.mem_univ l))) _) _

theorem sVar_dvd (s : SquareSummand) (c : Fin 2) : sVar k s c ∣ D k :=
  Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem (fun c => sVar k s c) (Finset.mem_univ c)).trans
    (Finset.dvd_prod_of_mem (fun s => ∏ c, sVar k s c) (Finset.mem_univ s))) _

theorem isUnit_map_matrix {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (P k))
    (h : M.det ∣ D k) : IsUnit (M.map (algebraMap (P k) (R k))) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isUnit_of_dvd_D k h

/-- The generic parameter. -/
noncomputable def generic : FamilyParameters (R k) :=
  ⟨fun g => (isUnit_map_matrix k (gMat k g) (gMat_dvd k g)).unit,
   fun l g => (isUnit_map_matrix k (bMat k l g) (bMat_dvd k l g)).unit,
   fun s c => (isUnit_of_dvd_D k (sVar_dvd k s c)).unit⟩

/-- The family comorphism. -/
noncomputable def psi (left : Bool) : MvPolynomial Var k →ₐ[k] R k :=
  aeval ((generic k).value left).coordinates

/-- Evaluation of the generic parameter at a point of the group. -/
noncomputable def evAt (a : GrpIdx → k) (ha : eval a (D k) ≠ 0) : R k →+* k :=
  IsLocalization.Away.lift (D k) (g := eval a) (isUnit_iff_ne_zero.mpr ha)

theorem evAt_algebraMap (a : GrpIdx → k) (ha : eval a (D k) ≠ 0) (f : P k) :
    evAt k a ha (algebraMap _ _ f) = eval a f :=
  IsLocalization.lift_eq _ _

theorem evAt_psi (left : Bool) (a : GrpIdx → k) (ha : eval a (D k) ≠ 0)
    (f : MvPolynomial Var k) :
    evAt k a ha (psi k left f) =
      eval (((generic k).map (evAt k a ha)).value left).coordinates f := by
  rw [psi, ← FamilyParameters.value_map]
  have : ∀ x, (((generic k).value left).map (evAt k a ha)).coordinates x =
      evAt k a ha (((generic k).value left).coordinates x) := LowerBound.coordinates_map _ _
  rw [show (((generic k).value left).map (evAt k a ha)).coordinates =
    fun x => evAt k a ha (((generic k).value left).coordinates x) from funext this]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, eval_C]
    rw [IsScalarTower.algebraMap_apply k (P k) (R k), evAt_algebraMap, MvPolynomial.algebraMap_eq,
      eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf => simp only [map_mul, hf, aeval_X, eval_X]

/-- The entries of a parameter. -/
def entries (pq : FamilyParameters k) : GrpIdx → k
  | .inl (.inl (g, a, b)) => (pq.global g : Matrix SquareVertex SquareVertex k) a b
  | .inl (.inr (s, c)) => (pq.scale s c : k)
  | .inr (l, g, i, j) => (pq.block l g : Matrix (Fin 2) (Fin 2) k) i j

theorem eval_D_entries (pq : FamilyParameters k) : eval (entries k pq) (D k) ≠ 0 := by
  have hg : ∀ g, eval (entries k pq) (gMat k g).det = (pq.global g : Matrix SquareVertex SquareVertex k).det := by
    intro g
    rw [RingHom.map_det]
    congr 1; ext a b; simp [gMat, entries]
  have hb : ∀ l g, eval (entries k pq) (bMat k l g).det = (pq.block l g : Matrix (Fin 2) (Fin 2) k).det := by
    intro l g
    rw [RingHom.map_det]
    congr 1; ext i j; simp [bMat, entries]
  simp only [D, map_mul, map_prod, hg, hb, sVar, eval_X, entries]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact Finset.prod_ne_zero_iff.mpr fun g _ =>
      ((Matrix.isUnit_iff_isUnit_det _).mp (pq.global g).isUnit).ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun l _ => Finset.prod_ne_zero_iff.mpr fun g _ =>
      ((Matrix.isUnit_iff_isUnit_det _).mp (pq.block l g).isUnit).ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun s _ => Finset.prod_ne_zero_iff.mpr fun c _ =>
      (pq.scale s c).ne_zero

/-- Every parameter is a specialization of the generic one. -/
theorem generic_map_entries (pq : FamilyParameters k) :
    (generic k).map (evAt k (entries k pq) (eval_D_entries k pq)) = pq := by
  obtain ⟨G, B, S⟩ := pq
  simp only [generic, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; ext a b
    simp [RingHom.mapMatrix_apply, evAt_algebraMap, gMat, entries]
  · funext l g; apply Units.ext; ext i j
    simp [RingHom.mapMatrix_apply, evAt_algebraMap, bMat, entries]
  · funext s c; apply Units.ext
    simp [evAt_algebraMap, sVar, entries]

/-- The image of the family of orientation `left`. -/
def image (left : Bool) : Set (Var → k) :=
  Set.range fun pq : FamilyParameters k => (pq.value left).coordinates

theorem D_ne_zero : D k ≠ 0 := by
  intro h
  have := eval_D_entries k (FamilyParameters.one k)
  rw [h, map_zero] at this
  exact this rfl

/-- **Vanishing on the image is the kernel of the comorphism** (over an infinite field). -/
theorem vanishes_iff [Infinite k] (left : Bool) (f : MvPolynomial Var k) :
    (∀ v ∈ image k left, eval v f = 0) ↔ psi k left f = 0 := by
  constructor
  · intro h
    obtain ⟨⟨g, ⟨_, n, rfl⟩⟩, hg⟩ := IsLocalization.surj (Submonoid.powers (D k)) (psi k left f)
    simp only at hg
    -- `g` vanishes wherever `D` does not.
    have hzero : ∀ a : GrpIdx → k, eval a (D k) ≠ 0 → eval a g = 0 := by
      intro a ha
      have h1 := congrArg (evAt k a ha) hg
      rw [map_mul, evAt_psi, evAt_algebraMap, evAt_algebraMap,
        h _ ⟨_, rfl⟩, zero_mul] at h1
      exact h1.symm
    have hDg : D k * g = 0 := by
      apply MvPolynomial.funext
      intro a
      rw [map_mul, map_zero]
      by_cases ha : eval a (D k) = 0
      · rw [ha, zero_mul]
      · rw [hzero a ha, mul_zero]
    have hg0 : g = 0 := (mul_eq_zero.mp hDg).resolve_left (D_ne_zero k)
    rw [hg0, map_zero] at hg
    have hu : IsUnit (algebraMap (P k) (R k) (D k ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (D k)).pow n
    exact (hu.mul_left_eq_zero).mp hg
  · rintro h _ ⟨pq, rfl⟩
    have := evAt_psi k left (entries k pq) (eval_D_entries k pq) f
    rw [h, map_zero, generic_map_entries] at this
    exact this.symm

/-! ### The Zariski topology on `k^2352` -/

/-- Affine space `k^2352`, with the Zariski topology. -/
def Affine (k : Type) := Var → k

/-- The zero locus of a set of polynomials. -/
def zeroLocus (J : Set (MvPolynomial Var k)) : Set (Affine k) := {v | ∀ f ∈ J, eval v f = 0}

/-- The polynomials vanishing on a set. -/
def vanishing (S : Set (Affine k)) : Set (MvPolynomial Var k) := {f | ∀ v ∈ S, eval v f = 0}

theorem zeroLocus_vanishing {S : Set (Affine k)} (h : ∃ J, S = zeroLocus k J) :
    S = zeroLocus k (vanishing k S) := by
  obtain ⟨J, rfl⟩ := h
  ext v
  constructor
  · intro hv f hf; exact hf v hv
  · intro hv f hf; exact hv f fun w hw => hw f hf

theorem zeroLocus_union (J₁ J₂ : Set (MvPolynomial Var k)) :
    zeroLocus k J₁ ∪ zeroLocus k J₂ = zeroLocus k {f | ∃ f₁ ∈ J₁, ∃ f₂ ∈ J₂, f = f₁ * f₂} := by
  ext v
  constructor
  · rintro (h | h) _ ⟨f₁, h₁, f₂, h₂, rfl⟩
    · rw [map_mul, h f₁ h₁, zero_mul]
    · rw [map_mul, h f₂ h₂, mul_zero]
  · intro h
    by_contra hv
    simp only [Set.mem_union, zeroLocus, Set.mem_setOf_eq, not_or, not_forall] at hv
    obtain ⟨⟨f₁, h₁, e₁⟩, ⟨f₂, h₂, e₂⟩⟩ := hv
    have := h _ ⟨f₁, h₁, f₂, h₂, rfl⟩
    rw [map_mul] at this
    exact (mul_ne_zero e₁ e₂) this

instance : TopologicalSpace (Affine k) :=
  TopologicalSpace.ofClosed {S | ∃ J, S = zeroLocus k J}
    ⟨{1}, by ext v; simp [zeroLocus]⟩
    (fun A hA => ⟨⋃ S ∈ A, vanishing k S, by
      ext v
      simp only [Set.mem_sInter, zeroLocus, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro hv f ⟨S, hS, hf⟩
        exact hf v (hv S hS)
      · intro hv S hS
        rw [zeroLocus_vanishing k (hA hS)]
        exact fun f hf => hv f ⟨S, hS, hf⟩⟩)
    (fun A hA B hB => by
      obtain ⟨J₁, rfl⟩ := hA
      obtain ⟨J₂, rfl⟩ := hB
      exact ⟨_, zeroLocus_union k J₁ J₂⟩)

theorem isClosed_iff (S : Set (Affine k)) : IsClosed S ↔ ∃ J, S = zeroLocus k J := by
  rw [← isOpen_compl_iff]
  have : IsOpen Sᶜ ↔ Sᶜᶜ ∈ {S : Set (Affine k) | ∃ J, S = zeroLocus k J} := Iff.rfl
  rw [this, compl_compl]
  rfl

theorem isClosed_zeroLocus (J : Set (MvPolynomial Var k)) : IsClosed (zeroLocus k J) :=
  (isClosed_iff k _).mpr ⟨J, rfl⟩

/-- The Zariski closure is the zero locus of the vanishing ideal. -/
theorem closure_eq (S : Set (Affine k)) : closure S = zeroLocus k (vanishing k S) := by
  apply le_antisymm
  · exact closure_minimal (fun v hv f hf => hf v hv) (isClosed_zeroLocus k _)
  · obtain ⟨J, hJ⟩ := (isClosed_iff k _).mp (isClosed_closure (s := S))
    rw [hJ]
    intro v hv f hf
    exact hv f fun w hw => by
      have : w ∈ closure S := subset_closure hw
      rw [hJ] at this
      exact this f hf

/-! ### The family closures -/

/-- The image of the family in affine space. -/
def imageA (left : Bool) : Set (Affine k) := image k left

/-- The Brent variety `V(4,4,4|49)`. -/
def brentVariety : Set (Affine k) := zeroLocus k (Set.range fun abc : EquationIndex SquareVertex =>
  equation k SquareVertex SquareSummand abc.1 abc.2.1 abc.2.2)

/-- The family closure of orientation `left`. -/
def familyClosure (left : Bool) : Set (Affine k) := closure (imageA k left)

theorem vanishing_eq_ker [Infinite k] (left : Bool) :
    vanishing k (imageA k left) = RingHom.ker (psi k left) := by
  ext f
  exact vanishes_iff k left f

instance isDomain_R : IsDomain (R k) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (D_ne_zero k))

/-- The recursive point. -/
def pointP : Affine k := (strassenSquare k).coordinates

theorem pointP_mem_image (left : Bool) : pointP k ∈ imageA k left :=
  ⟨FamilyParameters.one k, by
    show ((FamilyParameters.one k).value left).coordinates = _
    rw [FamilyParameters.value_one]; rfl⟩

/-- **The family closure contains `p`.** -/
theorem pointP_mem (left : Bool) : pointP k ∈ familyClosure k left :=
  subset_closure (pointP_mem_image k left)

/-- **The family closure is irreducible** (over an infinite field). -/
theorem isIrreducible_familyClosure [Infinite k] (left : Bool) :
    IsIrreducible (familyClosure k left) := by
  rw [familyClosure, isIrreducible_iff_closure]
  refine ⟨⟨_, pointP_mem_image k left⟩, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro Z₁ Z₂ h₁ h₂ hsub
  obtain ⟨J₁, rfl⟩ := (isClosed_iff k _).mp h₁
  obtain ⟨J₂, rfl⟩ := (isClosed_iff k _).mp h₂
  by_contra hne
  simp only [not_or, Set.not_subset] at hne
  obtain ⟨⟨v₁, hv₁, hn₁⟩, ⟨v₂, hv₂, hn₂⟩⟩ := hne
  simp only [zeroLocus, Set.mem_setOf_eq, not_forall] at hn₁ hn₂
  obtain ⟨f₁, hf₁, e₁⟩ := hn₁
  obtain ⟨f₂, hf₂, e₂⟩ := hn₂
  have hprod : psi k left (f₁ * f₂) = 0 := by
    rw [← vanishes_iff]
    intro v hv
    rcases hsub hv with h | h
    · rw [map_mul, h f₁ hf₁, zero_mul]
    · rw [map_mul, h f₂ hf₂, mul_zero]
  rw [map_mul] at hprod
  rcases mul_eq_zero.mp hprod with h | h
  · exact e₁ (((vanishes_iff k left f₁).mpr h) v₁ hv₁)
  · exact e₂ (((vanishes_iff k left f₂).mpr h) v₂ hv₂)

theorem image_subset_brentVariety (left : Bool) : imageA k left ⊆ brentVariety k := by
  rintro _ ⟨pq, rfl⟩ _ ⟨abc, rfl⟩
  rw [eval_equation, FamilyParameters.value_solves left pq, sub_self]

theorem familyClosure_subset (left : Bool) : familyClosure k left ⊆ brentVariety k :=
  closure_minimal (image_subset_brentVariety k left) (isClosed_zeroLocus k _)

end Brent.Formal.FamilyClosure
