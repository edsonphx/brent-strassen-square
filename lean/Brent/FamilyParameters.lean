import Brent.DeformationJets

open TrivSqZeroExt

namespace Brent

/-- Parameters in either exact recursive chart, including changes of bases and term scalings. -/
structure FamilyParameters (R : Type*) [CommRing R] where
  global : Fin 3 → (Matrix SquareVertex SquareVertex R)ˣ
  block : Fin 7 → Fin 3 → (Matrix (Fin 2) (Fin 2) R)ˣ
  scale : SquareSummand → Fin 2 → Rˣ

namespace FamilyParameters

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

protected def one (R : Type*) [CommRing R] : FamilyParameters R :=
  ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1⟩

def map (f : R →+* S) (p : FamilyParameters R) : FamilyParameters S :=
  ⟨fun i => Units.map f.mapMatrix.toMonoidHom (p.global i),
   fun i j => Units.map f.mapMatrix.toMonoidHom (p.block i j),
   fun i j => Units.map f.toMonoidHom (p.scale i j)⟩

protected def mul (p q : FamilyParameters R) : FamilyParameters R :=
  ⟨fun i => p.global i * q.global i, fun i j => p.block i j * q.block i j,
   fun i j => p.scale i j * q.scale i j⟩

theorem map_one (f : R →+* S) : (FamilyParameters.one R).map f = FamilyParameters.one S := by
  simp [FamilyParameters.one, map]

theorem map_id (p : FamilyParameters R) : p.map (RingHom.id R) = p := by
  cases p
  simp [map]

theorem map_comp (g : S →+* T) (f : R →+* S) (p : FamilyParameters R) :
    (p.map f).map g = p.map (g.comp f) := by
  cases p
  simp only [map, FamilyParameters.mk.injEq]
  constructor
  · funext i
    apply Units.ext
    rfl
  constructor <;> (funext i j; apply Units.ext; rfl)

theorem map_mul (f : R →+* S) (p q : FamilyParameters R) :
    (p.mul q).map f = (p.map f).mul (q.map f) := by
  simp [FamilyParameters.mul, map, _root_.map_mul]

theorem one_mul (p : FamilyParameters R) : (FamilyParameters.one R).mul p = p := by
  cases p
  simp [FamilyParameters.mul, FamilyParameters.one]

theorem mul_one (p : FamilyParameters R) : p.mul (FamilyParameters.one R) = p := by
  cases p
  simp [FamilyParameters.mul, FamilyParameters.one]

def value (left : Bool) (p : FamilyParameters R) :
    Decomposition R SquareVertex SquareSummand :=
  let d := if left then leftFamily (fun i => p.block i 0) (fun i => p.block i 1) (fun i => p.block i 2)
    else rightFamily (fun i => p.block i 0) (fun i => p.block i 1) (fun i => p.block i 2)
  (d.changeBasis (p.global 0) (p.global 1) (p.global 2)).rescale
    (fun i => p.scale i 0) (fun i => p.scale i 1)

theorem value_solves (left : Bool) (p : FamilyParameters R) : (p.value left).Solves := by
  have hs : (if left then leftFamily (fun i => p.block i 0) (fun i => p.block i 1) (fun i => p.block i 2)
    else rightFamily (fun i => p.block i 0) (fun i => p.block i 1) (fun i => p.block i 2)).Solves := by
    cases left <;> simp [leftFamily_solves, rightFamily_solves]
  exact Decomposition.solves_rescale (Decomposition.solves_changeBasis hs _ _ _) _ _

theorem value_map (f : R →+* S) (left : Bool) (p : FamilyParameters R) :
    (p.value left).map f = (p.map f).value left := by
  cases left <;> simp [value, map, Decomposition.map_rescale, Decomposition.map_changeBasis,
    map_leftFamily, map_rightFamily]

theorem value_one (left : Bool) : (FamilyParameters.one R).value left = strassenSquare R := by
  have hs (d : Decomposition R SquareVertex SquareSummand) :
      d.rescale (fun _ => 1) (fun _ => 1) = d := by
    cases d; simp [Decomposition.rescale]
  cases left <;> simp [value, FamilyParameters.one, hs, leftFamily_at_identity, rightFamily_at_identity]

end FamilyParameters

namespace Jets

variable (R : Type*) [CommRing R]

def constant : R →+* DualNumber R where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

def forget : DualNumber R →+* R where
  toFun x := x.fst
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def map {S : Type*} [CommRing S] (f : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

abbrev Double := DualNumber (DualNumber R)

/-- Keep the inner parameter and set the outer parameter to zero. -/
abbrev innerSpecialization : Double R →+* DualNumber R := forget (DualNumber R)

/-- Keep the outer parameter and set the inner parameter to zero. -/
abbrev outerSpecialization : Double R →+* DualNumber R := map (DualNumber R) (forget R)

private abbrev innerEmbedding : DualNumber R →+* Double R := constant (DualNumber R)
private abbrev outerEmbedding : DualNumber R →+* Double R := map R (constant R)

theorem inner_specialization_inner :
    (innerSpecialization R).comp (innerEmbedding R) = RingHom.id _ := by
  ext x <;> rfl

theorem outer_specialization_outer :
    (outerSpecialization R).comp (outerEmbedding R) = RingHom.id _ := by
  ext x <;> rfl

theorem outer_specialization_inner :
    (outerSpecialization R).comp (innerEmbedding R) = (constant R).comp (forget R) := by
  ext x <;> rfl

theorem inner_specialization_outer :
    (innerSpecialization R).comp (outerEmbedding R) = (constant R).comp (forget R) := by
  ext x <;> rfl

def pairParameters (p q : FamilyParameters (DualNumber R)) : FamilyParameters (Double R) :=
  (p.map (innerEmbedding R)).mul (q.map (outerEmbedding R))

theorem pair_specializes_inner (p q : FamilyParameters (DualNumber R))
    (hq : q.map (forget R) = FamilyParameters.one R) :
    (pairParameters R p q).map (innerSpecialization R) = p := by
  rw [pairParameters, FamilyParameters.map_mul, FamilyParameters.map_comp, FamilyParameters.map_comp,
    inner_specialization_inner, inner_specialization_outer, FamilyParameters.map_id,
    ← FamilyParameters.map_comp, hq, FamilyParameters.map_one, FamilyParameters.mul_one]

theorem pair_specializes_outer (p q : FamilyParameters (DualNumber R))
    (hp : p.map (forget R) = FamilyParameters.one R) :
    (pairParameters R p q).map (outerSpecialization R) = q := by
  rw [pairParameters, FamilyParameters.map_mul, FamilyParameters.map_comp, FamilyParameters.map_comp,
    outer_specialization_inner, outer_specialization_outer, FamilyParameters.map_id,
    ← FamilyParameters.map_comp, hp, FamilyParameters.map_one, FamilyParameters.one_mul]

end Jets
end Brent
