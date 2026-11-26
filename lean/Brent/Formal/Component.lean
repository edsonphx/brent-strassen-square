import Brent.Formal.FamilyClosure
import Brent.Formal.GermQuotLower
import Brent.KernelCheck.LowerBound
import Brent.KernelCheck.MainTheorem
import Brent.Equidim.Equidim
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# §7: each family closure is an irreducible component (F17, lines 610–620)

Write `𝔮 = ker ψ` for the kernel of the family comorphism of orientation `left`. Over an infinite
field it is the vanishing ideal of the family image (`FamilyClosure.vanishing_eq_ker`), so the
family closure is its zero locus, and it is prime.

*Generic part* (`Generic`). For ideals `J ≤ J'` of `k[x]` inside the maximal ideal of a point
`q`, the local rings of `k[x] ⧸ J` and `k[x] ⧸ J'` at `q` are related by a surjection
(`locMap`), so `dim (k[x]⧸J')_q ≤ dim (k[x]⧸J)_q`. If `J` is prime and `J < J'`, an element of
`J' \ J` is a nonzero element of the kernel of that surjection, in a domain, so the inequality is
strict by one (`ringKrullDim_locQ_succ_le`).

*Specialization* (`Specialize`). Every parameter over a `k`-algebra `S` is a specialization of the
generic parameter (`generic_map_evS`), so every family over `S` kills `𝔮` (`family_kills`).

*Germ families* (`GermFamily`). For each orientation, the 197 chart directions of
`chart_independent_derivatives k left` give an exact family over the germ `k[t₁,…,t₁₉₇]_(t)`
through `p`, with independent derivatives. This is `LowerBound.multi` with the direction map
`dirOf left` in place of `LowerBound.dir`; `dirOf true = LowerBound.dir`.

*Brent part* (`Closure`). `Brent ideal ≤ 𝔮 ≤ 𝔪_p`. The local ring of the closure at `p` has
dimension at most `dim_p V = 197` (a quotient of the Brent local ring) and at least 197 (the germ
family kills `𝔮`, `GermQuotLower.le_ringKrullDim_locQ`). If a prime `𝔭` with
`Brent ideal ≤ 𝔭 < 𝔮` existed, the local ring of `k[x] ⧸ 𝔭` at `p` would have dimension at
least 198, but it is a quotient of the Brent local ring. So no irreducible closed subset of the
Brent variety strictly contains the closure: it is an irreducible component
(`familyClosure_isComponent`), and `𝔮` is a minimal prime of the Brent ideal
(`ker_mem_minimalPrimes`). The closure has dimension 197 (`ringKrullDim_closure`, via
`Equidim.ringKrullDim_localization_eq'`, valid over any field).

Field hypotheses: `[Infinite k]` (closure = zero locus of `𝔮`) and `CharP k 3 ∨ CharZero k`
(the upper bound `dim_p V = 197` of `KernelCheck.MainTheorem`). No algebraic closedness is
needed.
-/

open MvPolynomial
open scoped BigOperators nonZeroDivisors

namespace Brent.Formal.Component

open Brent Brent.GermQuotLower

/-! ### Generic lemmas -/

section Generic

variable {k : Type} [Field k] {σ : Type} [Fintype σ] [DecidableEq σ] (q : σ → k)
  {J J' : Ideal (MvPolynomial σ k)} (hJJ' : J ≤ J') (hJq : J ≤ RingHom.ker (eval q))
  (hJ'q : J' ≤ RingHom.ker (eval q))

theorem evQ_factor (x : MvPolynomial σ k ⧸ J) :
    evQ J' q hJ'q (Ideal.Quotient.factor hJJ' x) = evQ J q hJq x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [evQ, Ideal.Quotient.factor_mk]

theorem mQ_eq_comap : mQ J q hJq = (mQ J' q hJ'q).comap (Ideal.Quotient.factor hJJ') := by
  ext x
  simp only [mQ, Ideal.mem_comap, RingHom.mem_ker, evQ_factor q hJJ' hJq hJ'q]

/-- The surjection `(k[x] ⧸ J)_q → (k[x] ⧸ J')_q`. -/
noncomputable def locMap : LocQ J q hJq →+* LocQ J' q hJ'q :=
  Localization.localRingHom (mQ J q hJq) (mQ J' q hJ'q) (Ideal.Quotient.factor hJJ')
    (mQ_eq_comap q hJJ' hJq hJ'q)

theorem locMap_surjective : Function.Surjective (locMap q hJJ' hJq hJ'q) := by
  intro z
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (mQ J' q hJ'q).primeCompl z
  obtain ⟨a0, rfl⟩ := Ideal.Quotient.factor_surjective hJJ' a
  obtain ⟨t0, ht⟩ := Ideal.Quotient.factor_surjective hJJ' t.1
  have ht0 : t0 ∈ (mQ J q hJq).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    intro h
    rw [mQ_eq_comap q hJJ' hJq hJ'q, Ideal.mem_comap, ht] at h
    exact Ideal.mem_primeCompl_iff.mp t.2 h
  refine ⟨IsLocalization.mk' (LocQ J q hJq) a0 ⟨t0, ht0⟩, ?_⟩
  rw [locMap, Localization.localRingHom_mk']
  congr 1
  exact Subtype.ext ht

/-- Enlarging the ideal does not increase the local dimension at `q`. -/
theorem ringKrullDim_locQ_le : ringKrullDim (LocQ J' q hJ'q) ≤ ringKrullDim (LocQ J q hJq) :=
  ringKrullDim_le_of_surjective _ (locMap_surjective q hJJ' hJq hJ'q)

/-- A strictly larger ideal over a prime lowers the local dimension at `q` by at least one. -/
theorem ringKrullDim_locQ_succ_le [J.IsPrime] {x : MvPolynomial σ k} (hxJ' : x ∈ J')
    (hxJ : x ∉ J) : ringKrullDim (LocQ J' q hJ'q) + 1 ≤ ringKrullDim (LocQ J q hJq) := by
  have hle : (mQ J q hJq).primeCompl ≤ nonZeroDivisors (MvPolynomial σ k ⧸ J) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  haveI : IsDomain (LocQ J q hJq) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hr0 : algebraMap (MvPolynomial σ k ⧸ J) (LocQ J q hJq) (Ideal.Quotient.mk J x) ≠ 0 := by
    intro h
    have h' := IsLocalization.injective (M := (mQ J q hJq).primeCompl) (LocQ J q hJq) hle
      (h.trans (map_zero _).symm)
    exact hxJ (Ideal.Quotient.eq_zero_iff_mem.mp h')
  refine ringKrullDim_succ_le_of_surjective (locMap q hJJ' hJq hJ'q)
    (locMap_surjective q hJJ' hJq hJ'q) (mem_nonZeroDivisors_of_ne_zero hr0) ?_
  rw [locMap, Localization.localRingHom_to_map, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hxJ', map_zero]

end Generic

/-- `197 ≤ a`, `a + 1 ≤ b`, `b ≤ 197` is impossible in `WithBot ℕ∞`. -/
theorem not_le_succ_le {a b : WithBot ℕ∞} (ha : 197 ≤ a) (hab : a + 1 ≤ b) (hb : b ≤ 197) :
    False := by
  have h1 : (((197 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((197 : ℕ) : ℕ∞) : WithBot ℕ∞) :=
    (add_le_add ha (le_refl 1)).trans (hab.trans hb)
  have h2 := ENat.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)
  omega

/-! ### Specializing the generic parameter over any `k`-algebra -/

section Specialize

open Brent.Formal.FamilyClosure

variable (k : Type) [Field k] {S : Type} [CommRing S] [Algebra k S]

/-- The entries of a parameter over `S` (`FamilyClosure.entries` is the case `S = k`). -/
def entriesS (pq : FamilyParameters S) : GrpIdx → S
  | .inl (.inl (g, a, b)) => (pq.global g : Matrix SquareVertex SquareVertex S) a b
  | .inl (.inr (s, c)) => (pq.scale s c : S)
  | .inr (l, g, i, j) => (pq.block l g : Matrix (Fin 2) (Fin 2) S) i j

theorem aeval_det_gMat (pq : FamilyParameters S) (g : Fin 3) :
    aeval (entriesS pq) (gMat k g).det =
      (pq.global g : Matrix SquareVertex SquareVertex S).det := by
  rw [AlgHom.map_det]
  congr 1
  ext a b
  simp [gMat, entriesS]

theorem aeval_det_bMat (pq : FamilyParameters S) (l : Fin 7) (g : Fin 3) :
    aeval (entriesS pq) (bMat k l g).det = (pq.block l g : Matrix (Fin 2) (Fin 2) S).det := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [bMat, entriesS]

theorem isUnit_aeval_D (pq : FamilyParameters S) : IsUnit (aeval (entriesS pq) (D k)) := by
  simp only [D, map_mul, map_prod]
  refine IsUnit.mul (IsUnit.mul ?_ ?_) ?_
  · refine IsUnit.prod_univ_iff.mpr fun g => ?_
    rw [aeval_det_gMat]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (pq.global g).isUnit
  · refine IsUnit.prod_univ_iff.mpr fun l => IsUnit.prod_univ_iff.mpr fun g => ?_
    rw [aeval_det_bMat]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (pq.block l g).isUnit
  · refine IsUnit.prod_univ_iff.mpr fun s => IsUnit.prod_univ_iff.mpr fun c => ?_
    rw [sVar, aeval_X]
    exact (pq.scale s c).isUnit

/-- Evaluation of the generic parameter at a parameter over `S`. -/
noncomputable def evS (pq : FamilyParameters S) : R k →+* S :=
  IsLocalization.Away.lift (D k) (g := (aeval (entriesS pq)).toRingHom) (isUnit_aeval_D k pq)

theorem evS_algebraMap (pq : FamilyParameters S) (f : P k) :
    evS k pq (algebraMap (P k) (R k) f) = aeval (entriesS pq) f :=
  IsLocalization.lift_eq _ _

theorem evS_algebraMap_k (pq : FamilyParameters S) (c : k) :
    evS k pq (algebraMap k (R k) c) = algebraMap k S c := by
  rw [IsScalarTower.algebraMap_apply k (P k) (R k), evS_algebraMap, MvPolynomial.algebraMap_eq,
    aeval_C]

/-- Every parameter over `S` is a specialization of the generic one. -/
theorem generic_map_evS (pq : FamilyParameters S) : (generic k).map (evS k pq) = pq := by
  obtain ⟨G, B, Sc⟩ := pq
  simp only [generic, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; ext a b
    simp [RingHom.mapMatrix_apply, evS_algebraMap, gMat, entriesS]
  · funext l g; apply Units.ext; ext i j
    simp [RingHom.mapMatrix_apply, evS_algebraMap, bMat, entriesS]
  · funext s c; apply Units.ext
    simp [evS_algebraMap, sVar, entriesS]

theorem evS_psi (left : Bool) (pq : FamilyParameters S) (f : MvPolynomial Var k) :
    evS k pq (psi k left f) = aeval (pq.value left).coordinates f := by
  have hc : (pq.value left).coordinates =
      fun x => evS k pq (((generic k).value left).coordinates x) := by
    funext x
    rw [← LowerBound.coordinates_map (evS k pq) ((generic k).value left) x,
      FamilyParameters.value_map, generic_map_evS]
  rw [hc, psi]
  induction f using MvPolynomial.induction_on with
  | C c => rw [aeval_C, aeval_C, evS_algebraMap_k]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf => simp only [map_mul, hf, aeval_X]

/-- **Every family over a `k`-algebra kills the kernel of the comorphism.** -/
theorem family_kills (left : Bool) (pq : FamilyParameters S) {f : MvPolynomial Var k}
    (hf : f ∈ RingHom.ker (psi k left)) : aeval (pq.value left).coordinates f = 0 := by
  rw [← evS_psi, RingHom.mem_ker.mp hf, map_zero]

end Specialize

/-! ### Exact germ families through `p`, for both orientations -/

section GermFamily

open LowerBound

variable (k : Type) [Field k]

/-- The chart directions (`FamilyQuadratics.chartIndex`, which is private, restated). -/
def dirOf (left : Bool) (i : Fin 197) : Fin 251 :=
  ⟨if left || i.val < 143 then i.val else i.val + 54, by have := i.isLt; split <;> omega⟩

theorem dirOf_true : dirOf true = LowerBound.dir := rfl

noncomputable def tGlobal (left : Bool) (g : Fin 3) (i : Fin 197) :
    Matrix SquareVertex SquareVertex k :=
  fun a b => (((castOrigin k (dirOf left i)).global g).val a b).snd

noncomputable def tBlock (left : Bool) (s : Fin 7) (g : Fin 3) (i : Fin 197) :
    Matrix (Fin 2) (Fin 2) k :=
  fun a b => (((castOrigin k (dirOf left i)).block s g).val a b).snd

noncomputable def tScale (left : Bool) (s : SquareSummand) (c : Fin 2) (i : Fin 197) : k :=
  (((castOrigin k (dirOf left i)).scale s c).val).snd

/-- The exact 197-parameter family of orientation `left` over the parameter germ. -/
noncomputable def multiD (left : Bool) : FamilyParameters (LowerBound.Germ k) :=
  ⟨fun g => (isUnit_germMatrix k (tGlobal k left g)).unit,
   fun s g => (isUnit_germMatrix k (tBlock k left s g)).unit,
   fun s c => (isUnit_germScalar k (tScale k left s c)).unit⟩

theorem multiD_residue (left : Bool) :
    (multiD k left).map (LowerBound.residue k) = FamilyParameters.one k := by
  simp only [multiD, FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext
    exact map_residue_germMatrix k _
  · funext s g; apply Units.ext
    exact map_residue_germMatrix k _
  · funext s c; apply Units.ext
    exact residue_germScalar k _

theorem multiD_germJet (left : Bool) (j : Fin 197) :
    (multiD k left).map (germJet k 197 j) = castOrigin k (dirOf left j) := by
  have hb := castOrigin_base' k (dirOf left j)
  simp only [FamilyParameters.map, FamilyParameters.one, FamilyParameters.mk.injEq] at hb
  change _ = FamilyParameters.mk (castOrigin k (dirOf left j)).global
    (castOrigin k (dirOf left j)).block (castOrigin k (dirOf left j)).scale
  simp only [multiD, FamilyParameters.map, FamilyParameters.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((castOrigin k (dirOf left j)).global g).val a b).fst =
        (1 : Matrix SquareVertex SquareVertex k) a b :=
      congrArg (fun u : (Matrix SquareVertex SquareVertex k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun hb.1 g)
    change germJet k 197 j (germMatrix k (tGlobal k left g) a b) = _
    rw [germJet_germMatrix]
    exact TrivSqZeroExt.ext h1.symm rfl
  · funext s g; apply Units.ext; refine Matrix.ext fun a b => ?_
    have h1 : (((castOrigin k (dirOf left j)).block s g).val a b).fst =
        (1 : Matrix (Fin 2) (Fin 2) k) a b :=
      congrArg (fun u : (Matrix (Fin 2) (Fin 2) k)ˣ => (u : Matrix _ _ k) a b)
        (congrFun (congrFun hb.2.1 s) g)
    change germJet k 197 j (germMatrix k (tBlock k left s g) a b) = _
    rw [germJet_germMatrix]
    exact TrivSqZeroExt.ext h1.symm rfl
  · funext s c; apply Units.ext
    have h1 : (((castOrigin k (dirOf left j)).scale s c).val).fst = 1 :=
      congrArg (fun u : kˣ => (u : k)) (congrFun (congrFun hb.2.2 s) c)
    change germJet k 197 j (germScalar k (tScale k left s c)) = _
    rw [germJet_germScalar]
    exact TrivSqZeroExt.ext h1.symm rfl

/-- The germ family of orientation `left`. -/
noncomputable def famD (left : Bool) : Decomposition (LowerBound.Germ k) SquareVertex SquareSummand :=
  (multiD k left).value left

theorem famD_residue (left : Bool) (x : Var) :
    LowerBound.residue k ((famD k left).coordinates x) = (strassenSquare k).coordinates x := by
  rw [← LowerBound.coordinates_map, famD, FamilyParameters.value_map, multiD_residue,
    FamilyParameters.value_one]

theorem famD_germJet (left : Bool) (j : Fin 197) (x : Var) :
    (germJet k 197 j ((famD k left).coordinates x)).snd =
      ((castOrigin k (dirOf left j)).value left).tangentPart.coordinates x := by
  rw [← LowerBound.coordinates_map, famD, FamilyParameters.value_map, multiD_germJet]
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

/-- The 197 derivatives of the germ family, indexed by the variables. -/
noncomputable def derivD (left : Bool) : Matrix (Fin 197) Var k := fun j x =>
  ((castOrigin k (dirOf left j)).value left).tangentPart.coordinates x

theorem derivD_independent (left : Bool) : LinearIndependent k (derivD k left).row := by
  have h := (chart_independent_derivatives k left).map'
    (LinearEquiv.funCongrLeft k k squareVariableNumber).toLinearMap (LinearEquiv.ker _)
  convert h using 1
  funext i x
  have e := Equiv.symm_apply_apply squareVariableNumber x
  show _ = ((castOrigin k (dirOf left i)).value left).tangentPart.coordinates
    (squareVariableNumber.symm (squareVariableNumber x))
  exact congrArg (fun y => ((castOrigin k (dirOf left i)).value left).tangentPart.coordinates y)
    e.symm

/-- The two germ residue maps agree (same definition, stated in two files). -/
theorem residue_eq : GermLower.residue k 197 = LowerBound.residue k := rfl

end GermFamily

/-! ### The family closures -/

section Closure

open Brent.Formal.FamilyClosure

variable (k : Type) [Field k] [Infinite k]

theorem brentIdeal_le_ker (left : Bool) :
    brentIdeal k SquareVertex SquareSummand ≤ RingHom.ker (psi k left) := by
  rw [brentIdeal, Ideal.span_le]
  rintro _ ⟨abc, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, ← vanishes_iff]
  intro v hv
  exact image_subset_brentVariety k left hv _ ⟨abc, rfl⟩

theorem ker_le_point (left : Bool) :
    RingHom.ker (psi k left) ≤ RingHom.ker (eval (pointP k)) := fun f hf => by
  rw [RingHom.mem_ker]
  exact (vanishes_iff k left f).mpr (RingHom.mem_ker.mp hf) (pointP k) (pointP_mem_image k left)

theorem brentIdeal_le_point :
    brentIdeal k SquareVertex SquareSummand ≤ RingHom.ker (eval (pointP k)) :=
  (brentIdeal_le_ker k true).trans (ker_le_point k true)

instance ker_isPrime (left : Bool) : (RingHom.ker (psi k left)).IsPrime := RingHom.ker_isPrime _

/-- The Brent local ring at `p`, in the `LocQ` form, is `SquareLocalRing`. -/
theorem locQ_brent_eq :
    ringKrullDim (LocQ (brentIdeal k SquareVertex SquareSummand) (pointP k)
      (brentIdeal_le_point k)) = squareLocalDimension k := rfl

/-- Every quotient of the Brent ring through `p` has local dimension at most 197. -/
theorem localDim_le_197 (hk : CharP k 3 ∨ CharZero k) {I : Ideal (MvPolynomial Var k)}
    (hBI : brentIdeal k SquareVertex SquareSummand ≤ I)
    (hIp : I ≤ RingHom.ker (eval (pointP k))) : ringKrullDim (LocQ I (pointP k) hIp) ≤ 197 := by
  have h := ringKrullDim_locQ_le (pointP k) hBI (brentIdeal_le_point k) hIp
  rw [locQ_brent_eq] at h
  rcases hk with hk | hk
  · rwa [squareLocalDimension_eq_197_of_charThree k] at h
  · rwa [squareLocalDimension_eq_197_of_charZero k] at h

/-- The germ family of orientation `left` kills `𝔮`. -/
theorem famD_kills (left : Bool) :
    RingHom.ker (psi k left) ≤ RingHom.ker (eval₂Hom (algebraMap k (GermLower.Germ k 197))
      fun x => (famD k left).coordinates x) := by
  intro f hf
  rw [RingHom.mem_ker, coe_eval₂Hom, ← aeval_def]
  exact family_kills k left (multiD k left) hf

/-- **The local dimension of the family closure at `p` is at least 197.** -/
theorem localDim_closure_ge (left : Bool) :
    (197 : WithBot ℕ∞) ≤
      ringKrullDim (LocQ (RingHom.ker (psi k left)) (pointP k) (ker_le_point k left)) := by
  have h := le_ringKrullDim_locQ 197 (RingHom.ker (psi k left)) (pointP k) (ker_le_point k left)
    (fun x => (famD k left).coordinates x) (famD_kills k left)
    (fun x => by rw [residue_eq]; exact famD_residue k left x) (derivD k left)
    (derivD_independent k left) (fun j x => famD_germJet k left j x)
  exact_mod_cast h

/-- **The local dimension of the family closure at `p` is 197.** -/
theorem localDim_closure (left : Bool) (hk : CharP k 3 ∨ CharZero k) :
    ringKrullDim (LocQ (RingHom.ker (psi k left)) (pointP k) (ker_le_point k left)) = 197 :=
  le_antisymm (localDim_le_197 k hk (brentIdeal_le_ker k left) (ker_le_point k left))
    (localDim_closure_ge k left)

/-- **No prime strictly between the Brent ideal and `𝔮`.** -/
theorem prime_eq_ker (left : Bool) (hk : CharP k 3 ∨ CharZero k)
    {I : Ideal (MvPolynomial Var k)} [I.IsPrime]
    (hBI : brentIdeal k SquareVertex SquareSummand ≤ I) (hIq : I ≤ RingHom.ker (psi k left)) :
    I = RingHom.ker (psi k left) := by
  by_contra hne
  obtain ⟨x, hxq, hxI⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hIq hne)
  have hIp : I ≤ RingHom.ker (eval (pointP k)) := hIq.trans (ker_le_point k left)
  have hstrict := ringKrullDim_locQ_succ_le (pointP k) hIq hIp (ker_le_point k left) hxq hxI
  exact not_le_succ_le (localDim_closure_ge k left) hstrict (localDim_le_197 k hk hBI hIp)

/-! ### The component statement in `k^2352` -/

/-- The vanishing ideal of a set of points. -/
def vanishingIdeal (Z : Set (Affine k)) : Ideal (MvPolynomial Var k) where
  carrier := vanishing k Z
  add_mem' := fun {a b} ha hb v hv => by rw [map_add, ha v hv, hb v hv, add_zero]
  zero_mem' := fun v _ => map_zero _
  smul_mem' := fun c {x} hx v hv => by rw [smul_eq_mul, map_mul, hx v hv, mul_zero]

theorem mem_vanishingIdeal {Z : Set (Affine k)} {f : MvPolynomial Var k} :
    f ∈ vanishingIdeal k Z ↔ ∀ v ∈ Z, eval v f = 0 := Iff.rfl

theorem vanishingIdeal_isPrime {Z : Set (Affine k)} (hZ : IsIrreducible Z) :
    (vanishingIdeal k Z).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr fun h1 => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hZ.nonempty
    have h2 := (mem_vanishingIdeal k).mp h1 v hv
    rw [map_one] at h2
    exact one_ne_zero h2
  · intro f g hfg
    have hfg' := (mem_vanishingIdeal k).mp hfg
    have hcover : Z ⊆ zeroLocus k {f} ∪ zeroLocus k {g} := by
      intro v hv
      rw [Set.mem_union]
      by_cases hf : eval v f = 0
      · exact Or.inl fun f' hf' => by rw [Set.mem_singleton_iff.mp hf']; exact hf
      · refine Or.inr fun g' hg' => ?_
        rw [Set.mem_singleton_iff.mp hg']
        have h := hfg' v hv
        rw [map_mul] at h
        exact (mul_eq_zero.mp h).resolve_left hf
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hZ.isPreirreducible) _ _
        (isClosed_zeroLocus k _) (isClosed_zeroLocus k _) hcover with h | h
    · exact Or.inl ((mem_vanishingIdeal k).mpr fun v hv => h hv f rfl)
    · exact Or.inr ((mem_vanishingIdeal k).mpr fun v hv => h hv g rfl)

/-- **Maximality.** An irreducible closed subset of the Brent variety containing the family
closure is the family closure. -/
theorem familyClosure_maximal (left : Bool) (hk : CharP k 3 ∨ CharZero k)
    (Z : Set (Affine k)) (hZc : IsClosed Z) (hZi : IsIrreducible Z)
    (hsub : familyClosure k left ⊆ Z) (hZB : Z ⊆ brentVariety k) : Z = familyClosure k left := by
  have hZ : Z = zeroLocus k (vanishing k Z) := zeroLocus_vanishing k ((isClosed_iff k Z).mp hZc)
  have h2 : vanishingIdeal k Z ≤ RingHom.ker (psi k left) := by
    intro f hf
    rw [RingHom.mem_ker, ← vanishes_iff]
    intro v hv
    exact (mem_vanishingIdeal k).mp hf v (hsub (subset_closure hv))
  have h1 : brentIdeal k SquareVertex SquareSummand ≤ vanishingIdeal k Z := by
    rw [brentIdeal, Ideal.span_le]
    rintro _ ⟨abc, rfl⟩
    exact (mem_vanishingIdeal k).mpr fun v hv => hZB hv _ ⟨abc, rfl⟩
  haveI := vanishingIdeal_isPrime k hZi
  have heq := prime_eq_ker k left hk h1 h2
  have hset : vanishing k Z = (RingHom.ker (psi k left) : Set (MvPolynomial Var k)) :=
    congrArg (fun I : Ideal (MvPolynomial Var k) => (I : Set (MvPolynomial Var k))) heq
  rw [familyClosure, closure_eq, vanishing_eq_ker, ← hset]
  exact hZ

/-- **Each family closure is an irreducible component of the Brent variety**: it contains `p`,
is irreducible, lies in the Brent variety, and no irreducible closed subset of the variety
strictly contains it. -/
theorem familyClosure_isComponent (left : Bool) (hk : CharP k 3 ∨ CharZero k) :
    pointP k ∈ familyClosure k left ∧ IsIrreducible (familyClosure k left) ∧
      familyClosure k left ⊆ brentVariety k ∧
      ∀ Z : Set (Affine k), IsClosed Z → IsIrreducible Z → familyClosure k left ⊆ Z →
        Z ⊆ brentVariety k → Z = familyClosure k left :=
  ⟨pointP_mem k left, isIrreducible_familyClosure k left, familyClosure_subset k left,
    familyClosure_maximal k left hk⟩

/-- The same statement for the ideal: `𝔮` is a minimal prime over the Brent ideal. -/
theorem ker_mem_minimalPrimes (left : Bool) (hk : CharP k 3 ∨ CharZero k) :
    RingHom.ker (psi k left) ∈ (brentIdeal k SquareVertex SquareSummand).minimalPrimes :=
  ⟨⟨inferInstance, brentIdeal_le_ker k left⟩, fun I hI hIq =>
    (haveI := hI.1; prime_eq_ker k left hk hI.2 hIq).ge⟩

/-- **Each family closure has dimension 197.** A finitely generated domain over a field has the
same dimension at every maximal ideal (`Equidim.ringKrullDim_localization_eq'`, any field). -/
theorem ringKrullDim_closure (left : Bool) (hk : CharP k 3 ∨ CharZero k) :
    ringKrullDim (MvPolynomial Var k ⧸ RingHom.ker (psi k left)) = 197 := by
  rw [← Equidim.ringKrullDim_localization_eq' (k := k)
    (mQ (RingHom.ker (psi k left)) (pointP k) (ker_le_point k left))]
  exact localDim_closure k left hk

end Closure

end Brent.Formal.Component
