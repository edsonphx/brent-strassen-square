import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Initial relations for a principal ideal

Draft for Lemma 4.1 (rows 13–14). For the filtration by powers of an ideal `m`,
`InitialRegular m f d` states that multiplication by the degree-`d` class
of `f` is injective on each graded piece, using representatives throughout.
-/

namespace Brent.InitialForms

variable {R : Type*} [CommRing R]

/-- Injectivity of multiplication by the initial form, expressed on representatives. -/
def InitialRegular (m : Ideal R) (f : R) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (a : R), a ∈ m ^ n → a * f ∈ m ^ (n + d + 1) → a ∈ m ^ (n + 1)

/-- Multiplication by `f` cannot raise filtration order beyond the shift `d`. -/
theorem mem_pow_of_mul_mem (m : Ideal R) (f : R) (d : ℕ)
    (hreg : InitialRegular m f d) (a : R) (n : ℕ)
    (h : a * f ∈ m ^ (n + d)) : a ∈ m ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      trivial
  | succ n ih =>
      have hnext : a * f ∈ m ^ (n + d + 1) := by
        simpa [Nat.succ_add, add_assoc] using h
      have hprev : a * f ∈ m ^ (n + d) :=
        Ideal.pow_le_pow_right (Nat.le_succ _) hnext
      exact hreg n a (ih hprev) hnext

/-- The principal ideal meets the filtration in exactly the expected multiples. -/
theorem principal_inf_pow (m : Ideal R) (f : R) (d n : ℕ)
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) :
    Ideal.span ({f} : Set R) ⊓ m ^ (n + d) =
      Ideal.span ({f} : Set R) * m ^ n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx.1
    have ha := mem_pow_of_mul_mem m f d hreg a n hx.2
    rw [mul_comm a f]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) ha
  · refine le_inf ?_ ?_
    · exact Ideal.mul_le_right
    · have hspan : Ideal.span ({f} : Set R) ≤ m ^ d := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hf
      rw [add_comm n d, pow_add]
      exact Ideal.mul_mono hspan le_rfl

/-- In degree `n+d`, each class killed by the quotient by `f` is represented
by an expected multiple of `f` with multiplier in filtration degree `n`. -/
theorem principal_relation_of_mem_sup (m : Ideal R) (f : R) (d n : ℕ)
    (hreg : InitialRegular m f d) {x : R} (hx : x ∈ m ^ (n + d))
    (h : x ∈ Ideal.span ({f} : Set R) ⊔ m ^ (n + d + 1)) :
    ∃ a ∈ m ^ n, x - a * f ∈ m ^ (n + d + 1) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hz' : z ∈ m ^ (n + d) := Ideal.pow_le_pow_right (Nat.le_succ _) hz
  have ha' : a * f ∈ m ^ (n + d) := by
    have hsub := Ideal.sub_mem (m ^ (n + d)) hx hz'
    simpa [add_sub_cancel_right] using hsub
  exact ⟨a, mem_pow_of_mul_mem m f d hreg a n ha', by simpa using hz⟩

/-- Below the order of `f`, quotienting by `f` creates no initial relations. -/
theorem principal_no_relation_below (m : Ideal R) (f : R) {d j : ℕ}
    (hf : f ∈ m ^ d) (hj : j < d) :
    Ideal.span ({f} : Set R) ⊔ m ^ (j + 1) = m ^ (j + 1) := by
  apply sup_eq_right.mpr
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hj) hf

/-- The degreewise initial ideal of `(f)`, pulled back to the filtered ring.
Intersecting with `m^j` gives representatives for the kernel in degree `j`. -/
theorem principal_initial_preimage (m : Ideal R) (f : R) {d j : ℕ}
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) :
    (Ideal.span ({f} : Set R) ⊔ m ^ (j + 1)) ⊓ m ^ j =
      if j < d then m ^ (j + 1)
      else Ideal.span ({f} : Set R) * m ^ (j - d) ⊔ m ^ (j + 1) := by
  by_cases hj : j < d
  · rw [if_pos hj, principal_no_relation_below m f hf hj]
    exact inf_eq_left.mpr (Ideal.pow_le_pow_right (Nat.le_succ j))
  · rw [if_neg hj]
    have hdegree : j - d + d = j := Nat.sub_add_cancel (Nat.le_of_not_gt hj)
    apply le_antisymm
    · intro x hx
      have hxj : x ∈ m ^ (j - d + d) := by simpa [hdegree] using hx.2
      have hxq : x ∈ Ideal.span ({f} : Set R) ⊔ m ^ (j - d + d + 1) := by
        simpa [hdegree, add_assoc] using hx.1
      obtain ⟨a, ha, hrem⟩ := principal_relation_of_mem_sup m f d (j - d) hreg hxj hxq
      have hrem' : x - a * f ∈ m ^ (j + 1) := by
        simpa [hdegree, add_assoc] using hrem
      have hprod : a * f ∈ Ideal.span ({f} : Set R) * m ^ (j - d) := by
        rw [mul_comm a f]
        exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) ha
      apply Submodule.mem_sup.mpr
      refine ⟨a * f, hprod, x - a * f, hrem', ?_⟩
      abel
    · have hprod := principal_inf_pow m f d (j - d) hf hreg
      rw [hdegree] at hprod
      rw [← hprod]
      exact sup_le
        (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right (Ideal.pow_le_pow_right (Nat.le_succ j)))

/-- For a quotient map with kernel `(f)`, the kernel on degree-`j`
representatives is the same ideal as in `principal_initial_preimage`. -/
theorem principal_initial_preimage_of_surjective {S : Type*} [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π)
    (m : Ideal R) (f : R) {d j : ℕ}
    (hker : RingHom.ker π = Ideal.span ({f} : Set R))
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) :
    ((m.map π) ^ (j + 1)).comap π ⊓ m ^ j =
      if j < d then m ^ (j + 1)
      else Ideal.span ({f} : Set R) * m ^ (j - d) ⊔ m ^ (j + 1) := by
  rw [← Ideal.map_pow, Ideal.comap_map_of_surjective π hπ]
  change (m ^ (j + 1) ⊔ RingHom.ker π) ⊓ m ^ j = _
  rw [hker, sup_comm]
  exact principal_initial_preimage m f hf hreg

/-! ### Graded pieces as module quotients -/

abbrev nextStep (m : Ideal R) (j : ℕ) : Submodule R (m ^ j : Ideal R) :=
  Submodule.comap (m ^ j : Ideal R).subtype (m ^ (j + 1) : Ideal R)

abbrev PowerPiece (m : Ideal R) (j : ℕ) :=
  (m ^ j : Ideal R) ⧸ nextStep m j

def principalPieceMap (m : Ideal R) (f : R) (j : ℕ) :=
  (nextStep m j).liftQ
    (((Ideal.span ({f} : Set R) ⊔ m ^ (j + 1) : Ideal R).mkQ).comp
      (m ^ j : Ideal R).subtype)
    (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact le_sup_right hx)

theorem mkQ_mem_ker_principalPieceMap (m : Ideal R) (f : R) (j : ℕ)
    (x : (m ^ j : Ideal R)) :
    (nextStep m j).mkQ x ∈ LinearMap.ker (principalPieceMap m f j) ↔
      (x : R) ∈ (Ideal.span ({f} : Set R) ⊔ m ^ (j + 1) : Ideal R) ⊓ m ^ j := by
  rw [LinearMap.mem_ker]
  change (nextStep m j).liftQ _ _ (Submodule.Quotient.mk x) = 0 ↔ _
  rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨fun h => ⟨h, x.property⟩, fun h => h.1⟩

theorem principalPieceMap_kernel_formula (m : Ideal R) (f : R) {d j : ℕ}
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) (x : (m ^ j : Ideal R)) :
    (nextStep m j).mkQ x ∈ LinearMap.ker (principalPieceMap m f j) ↔
      (x : R) ∈ (if j < d then m ^ (j + 1)
        else Ideal.span ({f} : Set R) * m ^ (j - d) ⊔ m ^ (j + 1)) := by
  rw [mkQ_mem_ker_principalPieceMap, principal_initial_preimage m f hf hreg]

def mulFiltered (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d) (n : ℕ) :
    (m ^ n : Ideal R) →ₗ[R] (m ^ (n + d) : Ideal R) where
  toFun a := ⟨a.val * f, by
    rw [pow_add]
    exact Ideal.mul_mem_mul a.property hf⟩
  map_add' a b := Subtype.ext (add_mul a.val b.val f)
  map_smul' r a := Subtype.ext (mul_assoc r a.val f)

def mulPowerPiece (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d) (n : ℕ) :
    PowerPiece m n →ₗ[R] PowerPiece m (n + d) :=
  (nextStep m n).liftQ ((nextStep m (n + d)).mkQ.comp (mulFiltered m f hf n)) (by
    intro a ha
    apply LinearMap.mem_ker.mpr
    change Submodule.Quotient.mk (mulFiltered m f hf n a) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change a.val * f ∈ m ^ (n + d + 1)
    have hpow : m ^ (n + d + 1) = m ^ (n + 1) * m ^ d := by
      rw [show n + d + 1 = (n + 1) + d by omega, pow_add]
    rw [hpow]
    exact Ideal.mul_mem_mul (show a.val ∈ m ^ (n + 1) from ha) hf)

@[simp] theorem mulPowerPiece_mkQ (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d)
    (n : ℕ) (a : (m ^ n : Ideal R)) :
    mulPowerPiece m f hf n ((nextStep m n).mkQ a) =
      (nextStep m (n + d)).mkQ (mulFiltered m f hf n a) := by
  simp only [mulPowerPiece, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply]

theorem ker_principalPieceMap_eq_range (m : Ideal R) (f : R) {d : ℕ}
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) (n : ℕ) :
    LinearMap.ker (principalPieceMap m f (n + d)) =
      LinearMap.range (mulPowerPiece m f hf n) := by
  ext u
  obtain ⟨x, rfl⟩ := (nextStep m (n + d)).mkQ_surjective u
  constructor
  · intro hx
    have hsup := ((mkQ_mem_ker_principalPieceMap m f (n + d) x).mp hx).1
    obtain ⟨a, ha, hdiff⟩ :=
      principal_relation_of_mem_sup m f d n hreg x.property hsup
    refine ⟨(nextStep m n).mkQ ⟨a, ha⟩, ?_⟩
    rw [mulPowerPiece_mkQ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change a * f - x.val ∈ m ^ (n + d + 1)
    rw [← neg_sub]
    exact (m ^ (n + d + 1) : Ideal R).neg_mem hdiff
  · rintro ⟨v, hv⟩
    obtain ⟨a, rfl⟩ := (nextStep m n).mkQ_surjective v
    rw [mulPowerPiece_mkQ] at hv
    rw [← hv]
    apply (mkQ_mem_ker_principalPieceMap m f (n + d) _).mpr
    refine ⟨Ideal.mem_sup_left ?_, (mulFiltered m f hf n a).property⟩
    exact Ideal.mem_span_singleton'.mpr ⟨a.val, rfl⟩

abbrev PrincipalQuotPiece (m : Ideal R) (f : R) (j : ℕ) :=
  LinearMap.range (principalPieceMap m f j)

noncomputable def principalPieceEquiv (m : Ideal R) (f : R) {d : ℕ}
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) (n : ℕ) :
    (PowerPiece m (n + d) ⧸ LinearMap.range (mulPowerPiece m f hf n)) ≃ₗ[R]
      PrincipalQuotPiece m f (n + d) := by
  rw [← ker_principalPieceMap_eq_range m f hf hreg n]
  exact (principalPieceMap m f (n + d)).quotKerEquivRange

theorem ker_principalPieceMap_eq_bot_of_lt (m : Ideal R) (f : R) {d j : ℕ}
    (hf : f ∈ m ^ d) (hj : j < d) :
    LinearMap.ker (principalPieceMap m f j) = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  obtain ⟨x, rfl⟩ := (nextStep m j).mkQ_surjective u
  have hx := ((mkQ_mem_ker_principalPieceMap m f j x).mp hu).1
  rw [principal_no_relation_below m f hf hj] at hx
  change (nextStep m j).mkQ x = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hx

noncomputable def principalPieceEquivBelow (m : Ideal R) (f : R) {d j : ℕ}
    (hf : f ∈ m ^ d) (hj : j < d) :
    PowerPiece m j ≃ₗ[R] PrincipalQuotPiece m f j :=
  LinearEquiv.ofInjective (principalPieceMap m f j)
    (LinearMap.ker_eq_bot.mp (ker_principalPieceMap_eq_bot_of_lt m f hf hj))

/-! ### The initial form as a nonzerodivisor on the graded pieces -/

/-- `InitialRegular` makes multiplication by the initial form injective in every degree. -/
theorem mulPowerPiece_injective (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d)
    (hreg : InitialRegular m f d) (n : ℕ) : Function.Injective (mulPowerPiece m f hf n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  obtain ⟨a, rfl⟩ := (nextStep m n).mkQ_surjective u
  rw [mulPowerPiece_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hreg n a.val a.property hu

/-- **`InitialRegular` is exactly regularity of the initial form**: multiplication by the
degree-`d` class of `f` is injective on every graded piece of the `m`-adic filtration. -/
theorem initialRegular_iff (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d) :
    InitialRegular m f d ↔ ∀ n, Function.Injective (mulPowerPiece m f hf n) := by
  refine ⟨fun h n => mulPowerPiece_injective m f hf h n, fun h n a ha hmul => ?_⟩
  have h0 : mulPowerPiece m f hf n ((nextStep m n).mkQ ⟨a, ha⟩) = 0 := by
    rw [mulPowerPiece_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmul
  have h1 := h n (h0.trans (map_zero (mulPowerPiece m f hf n)).symm)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

/-- **Exactness in degree `n + d`**: `0 → grₙ → gr_{n+d} → (degree `n + d` piece of the
quotient by `f`) → 0`, with the first map multiplication by the initial form. -/
theorem principal_exact (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d)
    (hreg : InitialRegular m f d) (n : ℕ) :
    Function.Injective (mulPowerPiece m f hf n) ∧
      LinearMap.range (mulPowerPiece m f hf n) =
        LinearMap.ker (principalPieceMap m f (n + d)) :=
  ⟨mulPowerPiece_injective m f hf hreg n, (ker_principalPieceMap_eq_range m f hf hreg n).symm⟩

/-! ### Multiplication of homogeneous classes -/

def productRepresentative (m : Ideal R) (i j : ℕ) :
    (m ^ i : Ideal R) →ₗ[R] (m ^ j : Ideal R) →ₗ[R] PowerPiece m (i + j) where
  toFun a := (nextStep m (i + j)).mkQ.comp
    { toFun := fun b => ⟨a.val * b.val, by
        rw [pow_add]
        exact Ideal.mul_mem_mul a.property b.property⟩
      map_add' := fun b c => Subtype.ext (mul_add a.val b.val c.val)
      map_smul' := fun r b => Subtype.ext (by simp [smul_eq_mul, mul_left_comm]) }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro y
    change (nextStep m (i + j)).mkQ ⟨(a.val + b.val) * y.val, _⟩ =
      (nextStep m (i + j)).mkQ ⟨a.val * y.val, _⟩ +
        (nextStep m (i + j)).mkQ ⟨b.val * y.val, _⟩
    rw [← map_add]
    exact congrArg ((nextStep m (i + j)).mkQ) (Subtype.ext (add_mul _ _ _))
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro y
    change (nextStep m (i + j)).mkQ ⟨(r * a.val) * y.val, _⟩ =
      r • (nextStep m (i + j)).mkQ ⟨a.val * y.val, _⟩
    rw [← map_smul]
    exact congrArg ((nextStep m (i + j)).mkQ) (Subtype.ext (mul_assoc _ _ _))

theorem productRepresentative_apply (m : Ideal R) (i j : ℕ)
    (a : (m ^ i : Ideal R)) (b : (m ^ j : Ideal R)) :
    productRepresentative m i j a b =
      (nextStep m (i + j)).mkQ ⟨a.val * b.val, by
        rw [pow_add]
        exact Ideal.mul_mem_mul a.property b.property⟩ := rfl

def productPiece (m : Ideal R) (i j : ℕ) :
    PowerPiece m i →ₗ[R] PowerPiece m j →ₗ[R] PowerPiece m (i + j) :=
  (productRepresentative m i j).liftQ₂ (nextStep m i) (nextStep m j)
    (by
      intro a ha
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro b
      rw [LinearMap.zero_apply, productRepresentative_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change a.val * b.val ∈ m ^ (i + j + 1)
      have hpow : m ^ (i + j + 1) = m ^ (i + 1) * m ^ j := by
        rw [show i + j + 1 = (i + 1) + j by omega, pow_add]
      rw [hpow]
      exact Ideal.mul_mem_mul (show a.val ∈ m ^ (i + 1) from ha) b.property)
    (by
      intro b hb
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro a
      rw [LinearMap.zero_apply, LinearMap.flip_apply, productRepresentative_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change a.val * b.val ∈ m ^ (i + j + 1)
      have hpow : m ^ (i + j + 1) = m ^ i * m ^ (j + 1) := by
        rw [show i + j + 1 = i + (j + 1) by omega, pow_add]
      rw [hpow]
      exact Ideal.mul_mem_mul a.property (show b.val ∈ m ^ (j + 1) from hb))

@[simp] theorem productPiece_mkQ (m : Ideal R) (i j : ℕ)
    (a : (m ^ i : Ideal R)) (b : (m ^ j : Ideal R)) :
    productPiece m i j ((nextStep m i).mkQ a) ((nextStep m j).mkQ b) =
      productRepresentative m i j a b := by
  simp only [productPiece, Submodule.mkQ_apply, LinearMap.liftQ₂_mk]

theorem productPiece_initial (m : Ideal R) (f : R) {d : ℕ} (hf : f ∈ m ^ d)
    (n : ℕ) (a : PowerPiece m n) :
    productPiece m n d a ((nextStep m d).mkQ ⟨f, hf⟩) = mulPowerPiece m f hf n a := by
  obtain ⟨x, rfl⟩ := (nextStep m n).mkQ_surjective a
  rw [productPiece_mkQ, productRepresentative_apply, mulPowerPiece_mkQ]
  rfl

theorem mem_principalPieceMap_ker_iff_product (m : Ideal R) (f : R) {d : ℕ}
    (hf : f ∈ m ^ d) (hreg : InitialRegular m f d) (n : ℕ) (u : PowerPiece m (n + d)) :
    u ∈ LinearMap.ker (principalPieceMap m f (n + d)) ↔
      ∃ a : PowerPiece m n, productPiece m n d a ((nextStep m d).mkQ ⟨f, hf⟩) = u := by
  rw [ker_principalPieceMap_eq_range m f hf hreg n]
  simp only [productPiece_initial, LinearMap.mem_range]

/-! ### Functoriality for quotient filtrations -/

section Map

variable {S : Type*} [CommRing S]

/-- The map of powers induced by a ring homomorphism. -/
def mapPower (π : R →+* S) (m : Ideal R) (j : ℕ) :
    (m ^ j : Ideal R) →ₛₗ[π] ((m.map π) ^ j : Ideal S) where
  toFun a := ⟨π a.val, by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem π a.property⟩
  map_add' a b := Subtype.ext (map_add π a.val b.val)
  map_smul' r a := Subtype.ext (map_mul π r a.val)

/-- The degreewise map to the filtration induced on the target ring. -/
def mapPowerPiece (π : R →+* S) (m : Ideal R) (j : ℕ) :
    PowerPiece m j →ₛₗ[π] PowerPiece (m.map π) j :=
  (nextStep m j).mapQ (nextStep (m.map π) j) (mapPower π m j) (by
    intro a ha
    change π a.val ∈ (m.map π) ^ (j + 1)
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem π (show a.val ∈ m ^ (j + 1) from ha))

@[simp] theorem mapPowerPiece_mkQ (π : R →+* S) (m : Ideal R) (j : ℕ)
    (a : (m ^ j : Ideal R)) :
    mapPowerPiece π m j ((nextStep m j).mkQ a) =
      (nextStep (m.map π) j).mkQ (mapPower π m j a) := rfl

theorem mapPowerPiece_surjective (π : R →+* S) (hπ : Function.Surjective π)
    (m : Ideal R) (j : ℕ) : Function.Surjective (mapPowerPiece π m j) := by
  intro u
  obtain ⟨b, rfl⟩ := (nextStep (m.map π) j).mkQ_surjective u
  have hb : b.val ∈ (m ^ j).map π := by rw [Ideal.map_pow]; exact b.property
  obtain ⟨a, ha, hab⟩ := Ideal.mem_image_of_mem_map_of_surjective π hπ hb
  refine ⟨(nextStep m j).mkQ ⟨a, ha⟩, ?_⟩
  rw [mapPowerPiece_mkQ]
  exact congrArg ((nextStep (m.map π) j).mkQ) (Subtype.ext hab)

theorem mapPowerPiece_product (π : R →+* S) (m : Ideal R) (i j : ℕ)
    (u : PowerPiece m i) (v : PowerPiece m j) :
    mapPowerPiece π m (i + j) (productPiece m i j u v) =
      productPiece (m.map π) i j (mapPowerPiece π m i u) (mapPowerPiece π m j v) := by
  obtain ⟨a, rfl⟩ := (nextStep m i).mkQ_surjective u
  obtain ⟨b, rfl⟩ := (nextStep m j).mkQ_surjective v
  simp only [mapPowerPiece_mkQ, productPiece_mkQ, productRepresentative_apply]
  exact congrArg ((nextStep (m.map π) (i + j)).mkQ)
    (Subtype.ext (map_mul π a.val b.val))

/-- Compatibility with the earlier principal kernel calculation. -/
theorem mapPowerPiece_mkQ_eq_zero_iff (π : R →+* S) (hπ : Function.Surjective π)
    (m : Ideal R) (f : R) (hker : RingHom.ker π = Ideal.span ({f} : Set R))
    (j : ℕ) (a : (m ^ j : Ideal R)) :
    mapPowerPiece π m j ((nextStep m j).mkQ a) = 0 ↔
      (nextStep m j).mkQ a ∈ LinearMap.ker (principalPieceMap m f j) := by
  rw [mapPowerPiece_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [mkQ_mem_ker_principalPieceMap]
  change a.val ∈ ((m.map π) ^ (j + 1)).comap π ↔ _
  rw [← Ideal.map_pow, Ideal.comap_map_of_surjective π hπ]
  change a.val ∈ m ^ (j + 1) ⊔ RingHom.ker π ↔ _
  rw [hker, sup_comm (m ^ (j + 1))]
  exact ⟨fun h => ⟨h, a.property⟩, fun h => h.1⟩

end Map

end Brent.InitialForms
