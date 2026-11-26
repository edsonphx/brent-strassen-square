import Brent.CM.GradedPresentation
import Mathlib.Algebra.DirectSum.Ring

/-! DRAFT, NOT YET COMPILED.
Assemble the degreewise presentation into a commutative ring on the actual
external direct sum. Multiplication on both sides is multiplication of
representatives in A, not a structure transported across the equivalence.
The source is the direct sum of the explicit homogeneous relation quotients;
the target is the direct sum of the filtration quotients of A / (f_i).
-/
namespace Brent.CM.GradedRingAssembly

open IsLocalRing InitialForms DirectSum
open scoped DirectSum

variable {A : Type*} [CommRing A]

/-- Data for a homogeneous quotient of a multiplicative filtration. -/
structure Presentation (A : Type*) [CommRing A] where
  term : ℕ → Ideal A
  rel : ℕ → Ideal A
  zero_eq_top : term 0 = ⊤
  term_mul : ∀ {i j : ℕ} {a b : A}, a ∈ term i → b ∈ term j → a * b ∈ term (i+j)
  rel_mul : ∀ {i j : ℕ} {a b : A}, a ∈ rel i → b ∈ term j → a * b ∈ rel (i+j)

variable (P : Presentation A)

abbrev relation (i : ℕ) : Submodule A (P.term i) :=
  (P.rel i).comap (P.term i).subtype

/-- A component of the homogeneous quotient. Keep the presentation parameter
visible to typeclass inference. -/
def Piece (i : ℕ) : Type _ := P.term i ⧸ relation P i

instance (i : ℕ) : AddCommGroup (Piece P i) :=
  inferInstanceAs (AddCommGroup (P.term i ⧸ relation P i))

instance (i : ℕ) : Module A (Piece P i) :=
  inferInstanceAs (Module A (P.term i ⧸ relation P i))

noncomputable def mk (i : ℕ) (a : P.term i) : Piece P i := Submodule.Quotient.mk a

noncomputable def representative (i j : ℕ) :
    P.term i →ₗ[A] P.term j →ₗ[A] Piece P (i+j) where
  toFun a := (relation P (i+j)).mkQ.comp
    { toFun := fun b => ⟨a.val*b.val, P.term_mul a.property b.property⟩
      map_add' := fun b c => Subtype.ext (mul_add a.val b.val c.val)
      map_smul' := fun r b => Subtype.ext (by simp [smul_eq_mul, mul_left_comm]) }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    change (relation P (i+j)).mkQ ⟨(a.val+b.val)*c.val, _⟩ =
      (relation P (i+j)).mkQ ⟨a.val*c.val, _⟩ +
      (relation P (i+j)).mkQ ⟨b.val*c.val, _⟩
    rw [← map_add]
    exact congrArg ((relation P (i+j)).mkQ) (Subtype.ext (add_mul _ _ _))
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    change (relation P (i+j)).mkQ ⟨(r*a.val)*b.val, _⟩ =
      r • (relation P (i+j)).mkQ ⟨a.val*b.val, _⟩
    rw [← map_smul]
    exact congrArg ((relation P (i+j)).mkQ) (Subtype.ext (mul_assoc _ _ _))

theorem representative_apply (i j : ℕ) (a : P.term i) (b : P.term j) :
    representative P i j a b = mk P (i+j) ⟨a.val*b.val, P.term_mul a.property b.property⟩ := rfl

/-- Multiplication descends in both arguments by the stated relation ideal
compatibility. No choice of representatives enters the result. -/
noncomputable def product (i j : ℕ) :
    Piece P i →ₗ[A] Piece P j →ₗ[A] Piece P (i+j) :=
  (representative P i j).liftQ₂ (relation P i) (relation P j)
    (by
      intro a ha
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro b
      rw [LinearMap.zero_apply, representative_apply, mk, Submodule.Quotient.mk_eq_zero]
      exact P.rel_mul (show a.val ∈ P.rel i from ha) b.property)
    (by
      intro b hb
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro a
      rw [LinearMap.zero_apply, LinearMap.flip_apply, representative_apply, mk,
        Submodule.Quotient.mk_eq_zero]
      change a.val*b.val ∈ P.rel (i+j)
      simpa only [mul_comm a.val b.val, Nat.add_comm i j] using
        P.rel_mul (show b.val ∈ P.rel j from hb) a.property)

@[simp] theorem product_mk (i j : ℕ) (a : P.term i) (b : P.term j) :
    product P i j (mk P i a) (mk P j b) =
      mk P (i+j) ⟨a.val*b.val, P.term_mul a.property b.property⟩ := by
  simp only [product, mk, LinearMap.liftQ₂_mk, ← Submodule.mkQ_apply] <;> rfl

/-- Induction on actual homogeneous classes. -/
@[elab_as_elim] theorem piece_induction {i : ℕ} {C : Piece P i → Prop}
    (x : Piece P i) (h : ∀ a : P.term i, C (mk P i a)) : C x :=
  Submodule.Quotient.induction_on x h

noncomputable def constRep (a : A) : P.term 0 := ⟨a, by rw [P.zero_eq_top]; trivial⟩
noncomputable def constant (a : A) : Piece P 0 := mk P 0 (constRep P a)

/-- A helper for degree transport in the sigma-type associativity laws. -/
theorem sigma_mk_eq {i j : ℕ} (h : i = j) (a : P.term i) (b : P.term j)
    (hab : a.val = b.val) :
    GradedMonoid.mk i (mk P i a) = GradedMonoid.mk j (mk P j b) := by
  subst j
  rw [show a = b from Subtype.ext hab]

/-- The graded commutative ring laws follow directly from the ring laws in A. -/
noncomputable instance : DirectSum.GCommRing (Piece P) where
  mul := fun {i j} => product P i j
  one := constant P 1
  mul_zero := fun a => map_zero (product P _ _ a)
  zero_mul := fun b => by rw [map_zero] <;> rfl
  mul_add := fun a b c => map_add (product P _ _ a) b c
  add_mul := fun a b c => by rw [map_add] <;> rfl
  one_mul := by
    rintro ⟨i,a⟩
    induction a using piece_induction P with
    | h a =>
      change GradedMonoid.mk (0+i) (product P 0 i (mk P 0 (constRep P 1)) (mk P i a)) =
        GradedMonoid.mk i (mk P i a)
      rw [product_mk]
      apply sigma_mk_eq P (Nat.zero_add i)
      exact one_mul a.val
  mul_one := by
    rintro ⟨i,a⟩
    induction a using piece_induction P with
    | h a =>
      change GradedMonoid.mk (i+0) (product P i 0 (mk P i a) (mk P 0 (constRep P 1))) =
        GradedMonoid.mk i (mk P i a)
      rw [product_mk]
      apply sigma_mk_eq P (Nat.add_zero i)
      exact mul_one a.val
  mul_assoc := by
    rintro ⟨i,a⟩ ⟨j,b⟩ ⟨l,c⟩
    induction a using piece_induction P with
    | h a =>
      induction b using piece_induction P with
      | h b =>
        induction c using piece_induction P with
        | h c =>
          change GradedMonoid.mk (i+j+l)
            (product P (i+j) l (product P i j (mk P i a) (mk P j b)) (mk P l c)) =
            GradedMonoid.mk (i+(j+l))
            (product P i (j+l) (mk P i a) (product P j l (mk P j b) (mk P l c)))
          simp only [product_mk]
          apply sigma_mk_eq P (Nat.add_assoc i j l)
          exact mul_assoc a.val b.val c.val
  mul_comm := by
    rintro ⟨i,a⟩ ⟨j,b⟩
    induction a using piece_induction P with
    | h a =>
      induction b using piece_induction P with
      | h b =>
        change GradedMonoid.mk (i+j) (product P i j (mk P i a) (mk P j b)) =
          GradedMonoid.mk (j+i) (product P j i (mk P j b) (mk P i a))
        simp only [product_mk]
        apply sigma_mk_eq P (Nat.add_comm i j)
        exact mul_comm a.val b.val
  natCast := fun n => constant P (n : A)
  natCast_zero := by
    change (relation P 0).mkQ (constRep P ((0 : ℕ) : A)) = 0
    rw [Nat.cast_zero, show constRep P 0 = 0 from Subtype.ext rfl, map_zero]
  natCast_succ := by
    intro n
    change (relation P 0).mkQ (constRep P ((n+1 : ℕ) : A)) =
      (relation P 0).mkQ (constRep P (n : A)) + (relation P 0).mkQ (constRep P 1)
    rw [← map_add]
    exact congrArg ((relation P 0).mkQ) (Subtype.ext (Nat.cast_succ n))
  intCast := fun z => constant P (z : A)
  intCast_ofNat := by intro n; rfl
  intCast_negSucc_ofNat := by
    intro n
    change (relation P 0).mkQ (constRep P (Int.negSucc n : A)) =
      -(relation P 0).mkQ (constRep P ((n+1 : ℕ) : A))
    rw [← map_neg]
    exact congrArg ((relation P 0).mkQ) (Subtype.ext (Int.cast_negSucc n))

section Lemma41

variable [IsNoetherianRing A] [IsLocalRing A]
local notation "𝔪" => maximalIdeal A

/-- Source presentation from Lemma 4.1. -/
noncomputable def source (f : ℕ → A) (d : ℕ → ℕ) (s : ℕ) : Presentation A where
  term := fun n => 𝔪 ^ n
  rel := relI f d s
  zero_eq_top := by simp
  term_mul := by
    intro i j a b ha hb
    rw [pow_add]
    exact Ideal.mul_mem_mul ha hb
  rel_mul := by
    intro i j a b ha hb
    exact relI_mul_pow f d s i j ha hb

theorem filt_mul_mem (J : Ideal A) {i j : ℕ} {a b : A}
    (ha : a ∈ filt J i) (hb : b ∈ filt J j) : a*b ∈ filt J (i+j) := by
  obtain ⟨x,hx,p,hp,rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨y,hy,q,hq,rfl⟩ := Submodule.mem_sup.mp hb
  have h₁ : (x+p)*y + x*q ∈ J := Ideal.add_mem _
    (Ideal.mul_mem_left _ _ hy) (by rw [mul_comm]; exact Ideal.mul_mem_left _ _ hx)
  have h₂ : p*q ∈ 𝔪 ^ (i+j) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hp hq
  convert Ideal.add_mem (filt J (i+j)) (Ideal.mem_sup_left h₁) (Ideal.mem_sup_right h₂) using 1 <;> ring

/-- Target: the actual filtration quotients F_n/F_(n+1), where F_n = J + m^n. -/
noncomputable def target (J : Ideal A) : Presentation A where
  term := filt J
  rel := fun n => filt J (n+1)
  zero_eq_top := by simp [filt]
  term_mul := filt_mul_mem J
  rel_mul := by
    intro i j a b ha hb
    have h := filt_mul_mem J ha hb
    rwa [show i+1+j = i+j+1 by omega] at h

variable (f : ℕ → A) (d : ℕ → ℕ) (hf : ∀ i, f i ∈ 𝔪 ^ d i)
  (hreg : ∀ i, InitialRegularRel 𝔪 (firstIdeal f i) (f i) (d i)) (s : ℕ)

noncomputable def pieceEquiv (n : ℕ) :
    Piece (source f d s) n ≃ₗ[A] Piece (target (firstIdeal f s)) n :=
  lemma41_gradedPieceEquiv f d hf hreg s n

theorem pieceEquiv_mk (n : ℕ) (a : (source f d s).term n) :
    pieceEquiv f d hf hreg s n (mk (source f d s) n a) =
      mk (target (firstIdeal f s)) n ⟨a.val, Ideal.mem_sup_right a.property⟩ := rfl

/-- The canonical equivalence preserves multiplication of arbitrary classes. -/
theorem pieceEquiv_mul (i j : ℕ) (a : Piece (source f d s) i) (b : Piece (source f d s) j) :
    pieceEquiv f d hf hreg s (i+j) (product (source f d s) i j a b) =
      product (target (firstIdeal f s)) i j (pieceEquiv f d hf hreg s i a)
        (pieceEquiv f d hf hreg s j b) := by
  induction a using piece_induction (source f d s) with
  | h a =>
    induction b using piece_induction (source f d s) with
    | h b =>
      simp only [product_mk, pieceEquiv_mk] <;> rfl

noncomputable def forward :
    (⨁ n, Piece (source f d s) n) →+* (⨁ n, Piece (target (firstIdeal f s)) n) :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of _ n).comp (pieceEquiv f d hf hreg s n).toLinearMap.toAddMonoidHom)
    (by rfl)
    (by
      intro i j a b
      change DirectSum.of _ (i+j) (pieceEquiv f d hf hreg s (i+j)
        (product (source f d s) i j a b)) =
        DirectSum.of _ i (pieceEquiv f d hf hreg s i a) *
          DirectSum.of _ j (pieceEquiv f d hf hreg s j b)
      rw [DirectSum.of_mul_of]
      change DirectSum.of _ (i+j) (pieceEquiv f d hf hreg s (i+j)
        (product (source f d s) i j a b)) =
        DirectSum.of _ (i+j) (product (target (firstIdeal f s)) i j
          (pieceEquiv f d hf hreg s i a) (pieceEquiv f d hf hreg s j b))
      rw [pieceEquiv_mul])

noncomputable def backward :
    (⨁ n, Piece (target (firstIdeal f s)) n) →+* (⨁ n, Piece (source f d s) n) :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of _ n).comp (pieceEquiv f d hf hreg s n).symm.toLinearMap.toAddMonoidHom)
    (by
      change DirectSum.of _ 0 ((pieceEquiv f d hf hreg s 0).symm
        (constant (target (firstIdeal f s)) 1)) = DirectSum.of _ 0 (constant (source f d s) 1)
      congr 1
      apply (pieceEquiv f d hf hreg s 0).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl)
    (by
      intro i j a b
      rw [DirectSum.of_mul_of]
      change DirectSum.of _ (i+j) ((pieceEquiv f d hf hreg s (i+j)).symm
        (product (target (firstIdeal f s)) i j a b)) =
        DirectSum.of _ (i+j) (product (source f d s) i j
          ((pieceEquiv f d hf hreg s i).symm a) ((pieceEquiv f d hf hreg s j).symm b))
      congr 1
      apply (pieceEquiv f d hf hreg s (i+j)).injective
      rw [LinearEquiv.apply_symm_apply, pieceEquiv_mul, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])

@[simp] theorem forward_of (i : ℕ) (a : Piece (source f d s) i) :
    forward f d hf hreg s (DirectSum.of _ i a) = DirectSum.of _ i (pieceEquiv f d hf hreg s i a) :=
  DirectSum.toSemiring_of _ _ _ i a

@[simp] theorem backward_of (i : ℕ) (a : Piece (target (firstIdeal f s)) i) :
    backward f d hf hreg s (DirectSum.of _ i a) = DirectSum.of _ i ((pieceEquiv f d hf hreg s i).symm a) :=
  DirectSum.toSemiring_of _ _ _ i a

/-- The full direct-sum ring equivalence, not merely a sequence of linear
isomorphisms. Both ring multiplications were constructed independently from
representative products. -/
noncomputable def lemma41_ringEquiv :
    (⨁ n, Piece (source f d s) n) ≃+* (⨁ n, Piece (target (firstIdeal f s)) n) := by
  let F := forward f d hf hreg s
  let G := backward f d hf hreg s
  have hGF : G.comp F = RingHom.id _ := by
    apply DirectSum.ringHom_ext
    intro i a
    change backward f d hf hreg s (forward f d hf hreg s (DirectSum.of _ i a)) = _
    simp [forward_of, backward_of]
  have hFG : F.comp G = RingHom.id _ := by
    apply DirectSum.ringHom_ext
    intro i a
    change forward f d hf hreg s (backward f d hf hreg s (DirectSum.of _ i a)) = _
    simp [forward_of, backward_of]
  exact { toFun := F, invFun := G,
    left_inv := fun a => DFunLike.congr_fun hGF a,
    right_inv := fun a => DFunLike.congr_fun hFG a,
    map_mul' := F.map_mul, map_add' := F.map_add }

/-- The ring equivalence is graded: every homogeneous summand maps into the
same degree, by the canonical piece equivalence. -/
theorem lemma41_ringEquiv_of (i : ℕ) (a : Piece (source f d s) i) :
    lemma41_ringEquiv f d hf hreg s (DirectSum.of _ i a) =
      DirectSum.of _ i (pieceEquiv f d hf hreg s i a) :=
  forward_of f d hf hreg s i a

end Lemma41
end Brent.CM.GradedRingAssembly
