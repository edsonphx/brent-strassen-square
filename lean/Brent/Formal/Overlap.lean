import Brent.FamilyParameters

/-!
# The two charts agree on the orbit

When every inner block parameter is the identity, the left and right recursive families give
the same decomposition: the recursive point moved by the global basis changes and term scalings.
This common restriction is the orbit map `γ(c)` shared by both formal branches.
-/

namespace Brent.Formal

open FamilyParameters

variable {R : Type*} [CommRing R]

/-- The block parameters are all trivial. -/
def BlockTrivial (p : FamilyParameters R) : Prop := ∀ i j, p.block i j = 1

/-- The orbit through the recursive point. -/
def orbitValue (p : FamilyParameters R) : Decomposition R SquareVertex SquareSummand :=
  ((strassenSquare R).changeBasis (p.global 0) (p.global 1) (p.global 2)).rescale
    (fun i => p.scale i 0) (fun i => p.scale i 1)

theorem value_of_blockTrivial (left : Bool) {p : FamilyParameters R} (hp : BlockTrivial p) :
    p.value left = orbitValue p := by
  have hb : ∀ j, (fun i => p.block i j) = fun _ => 1 := fun j => funext fun i => hp i j
  cases left <;>
    simp only [value, orbitValue, hb, leftFamily_at_identity, rightFamily_at_identity,
      Bool.false_eq_true, if_true, if_false]

/-- **Overlap.** On trivial blocks the two charts coincide. -/
theorem value_left_eq_right {p : FamilyParameters R} (hp : BlockTrivial p) :
    p.value true = p.value false := by
  rw [value_of_blockTrivial true hp, value_of_blockTrivial false hp]

end Brent.Formal
