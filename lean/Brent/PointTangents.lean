import Brent.BlockTangents

/-!
# Tangents of the recursive families at a general block point

The lemmas in `Brent.FamilyTangents` and `Brent.BlockTangents` compute first-order tangents of
`G.value left` at the identity parameters. Here we compute them at a base point `pq` whose global
changes of basis and term scalings are trivial, while the inner block changes are arbitrary.
The resulting closed forms are computable, and commute with ring homomorphisms.
-/

open TrivSqZeroExt

namespace Brent

namespace Decomposition

variable {R α ι : Type} [CommRing R] [Fintype α] [DecidableEq α]

/-- Changes of basis compose: first by `(P, Q, T)`, then by `(P', Q', T')`. -/
theorem changeBasis_mul (d : Decomposition R α ι) (P P' Q Q' T T' : (Matrix α α R)ˣ) :
    d.changeBasis (P * P') (Q * Q') (T * T') = (d.changeBasis P Q T).changeBasis P' Q' T' := by
  have hinv (X Y : (Matrix α α R)ˣ) : (X * Y).inv = Y.inv * X.inv := rfl
  apply eq_of_components <;> funext s a
  · change ((P * P').val.transpose * Matrix.of (fun i j => d.u s (i, j)) *
        (Q * Q').inv.transpose) a.1 a.2 =
      (P'.val.transpose * (P.val.transpose * Matrix.of (fun i j => d.u s (i, j)) *
        Q.inv.transpose) * Q'.inv.transpose) a.1 a.2
    rw [hinv, Units.val_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  · change ((Q * Q').val.transpose * Matrix.of (fun i j => d.v s (i, j)) *
        (T * T').inv.transpose) a.1 a.2 =
      (Q'.val.transpose * (Q.val.transpose * Matrix.of (fun i j => d.v s (i, j)) *
        T.inv.transpose) * T'.inv.transpose) a.1 a.2
    rw [hinv, Units.val_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  · change ((P * P').inv * Matrix.of (fun i j => d.w s (i, j)) * (T * T').val) a.1 a.2 =
      (P'.inv * (P.inv * Matrix.of (fun i j => d.w s (i, j)) * T.val) * T'.val) a.1 a.2
    rw [hinv, Units.val_mul]
    simp only [Matrix.mul_assoc]

omit [Fintype α] [DecidableEq α] in
theorem coordinates_map {S : Type} [CommRing S] (f : R →+* S) (d : Decomposition R α ι)
    (x : Variable α ι) : (d.map f).coordinates x = f (d.coordinates x) := by
  obtain ⟨s, m, a⟩ := x
  cases m <;> rfl

omit [Fintype α] in
theorem vertexUnitCoefficient_map {S : Type} [CommRing S] (f : R →+* S)
    (d : Decomposition R α ι) (g : Fin 3) (i j : α) (s : ι) (m : Mode) (a b : α) :
    (d.map f).vertexUnitCoefficient g i j s m a b = f (d.vertexUnitCoefficient g i j s m a b) := by
  cases m <;> simp [vertexUnitCoefficient, Decomposition.map, apply_ite f]

end Decomposition

namespace FamilyParameters

variable {R : Type} [CommRing R]

theorem termUnitCoefficient_map {S : Type} [CommRing S] (f : R →+* S)
    (d : Decomposition R SquareVertex SquareSummand) (k : SquareSummand) (second : Bool)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    termUnitCoefficient (d.map f) k second s m a b = f (termUnitCoefficient d k second s m a b) := by
  cases m <;> simp [termUnitCoefficient, Decomposition.map, apply_ite f]

/-- The base Strassen decomposition of one `2 × 2` block (a public copy). -/
def blockBase (R : Type) [CommRing R] : Decomposition R (Fin 2) (Fin 7) :=
  strassen.map (Int.castRingHom R)

theorem blockBase_map {S : Type} [CommRing S] (f : R →+* S) :
    (blockBase R).map f = blockBase S := by
  simp [blockBase, Decomposition.map]

theorem leftFamily_eq (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    leftFamily P Q T =
      (blockBase R).recursiveLeft (fun i => (blockBase R).changeBasis (P i) (Q i) (T i)) := rfl

theorem rightFamily_eq (P Q T : Fin 7 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    rightFamily P Q T =
      Decomposition.recursiveRight (fun j => (blockBase R).changeBasis (P j) (Q j) (T j))
        (blockBase R) := rfl

/-- The family determined by the block parameters alone. -/
def blockFamily (left : Bool) (B : Fin 7 → Fin 3 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    Decomposition R SquareVertex SquareSummand :=
  if left then leftFamily (fun i => B i 0) (fun i => B i 1) (fun i => B i 2)
  else rightFamily (fun i => B i 0) (fun i => B i 1) (fun i => B i 2)

theorem blockFamily_map {S : Type} [CommRing S] (f : R →+* S) (left : Bool)
    (B : Fin 7 → Fin 3 → (Matrix (Fin 2) (Fin 2) R)ˣ) :
    (blockFamily left B).map f =
      blockFamily left (fun l h => Units.map f.mapMatrix.toMonoidHom (B l h)) := by
  cases left <;> simp [blockFamily, map_leftFamily, map_rightFamily]

/-- With trivial global changes and scalings, the value is the bare block family. -/
theorem value_of_trivial (left : Bool) (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) :
    pq.value left = blockFamily left pq.block := by
  simp only [value, hg, hs, Decomposition.changeBasis_identity, rescale_identity]
  rfl

theorem value_left_of_trivial (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) :
    pq.value true = leftFamily (fun i => pq.block i 0) (fun i => pq.block i 1)
      (fun i => pq.block i 2) :=
  value_of_trivial true pq hg hs

theorem value_right_of_trivial (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) :
    pq.value false = rightFamily (fun i => pq.block i 0) (fun i => pq.block i 1)
      (fun i => pq.block i 2) :=
  value_of_trivial false pq hg hs

/-- The value of a perturbation `(pq.map f).mul G` of a point with trivial global part. -/
theorem mul_value_of_trivial {S : Type} [CommRing S] (f : R →+* S) (left : Bool)
    (pq : FamilyParameters R) (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1)
    (G : FamilyParameters S) :
    ((pq.map f).mul G).value left =
      ((blockFamily left
        (fun l h => Units.map f.mapMatrix.toMonoidHom (pq.block l h) * G.block l h)).changeBasis
        (G.global 0) (G.global 1) (G.global 2)).rescale
        (fun s => G.scale s 0) (fun s => G.scale s 1) := by
  have e : (pq.map f).mul G =
      ⟨G.global, fun l h => Units.map f.mapMatrix.toMonoidHom (pq.block l h) * G.block l h,
        G.scale⟩ := by
    obtain ⟨pg, pb, ps⟩ := pq
    obtain ⟨gg, gb, gs⟩ := G
    simp only at hg hs
    subst hg hs
    simp only [FamilyParameters.mul, map, _root_.map_one]
    congr 1
    · funext x
      exact _root_.one_mul _
    · funext x y
      exact _root_.one_mul _
  rw [e]
  rfl

/-! ### Global generators -/

theorem globalUnit_tangentAt (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) (left : Bool)
    (g : Fin 3) (i j : SquareVertex) (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    (((pq.map (Jets.constant R)).mul (globalUnit g i j)).value left).tangentPart.coordinates
        (s, m, (a, b)) =
      (pq.value left).vertexUnitCoefficient g i j s m a b := by
  rw [mul_value_of_trivial (Jets.constant R) left pq hg hs]
  have hb : (fun l h => Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l h) *
      (globalUnit (R := R) g i j).block l h) =
      fun l h => Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l h) := by
    funext l h
    exact _root_.mul_one _
  rw [hb, ← blockFamily_map, ← value_of_trivial left pq hg hs]
  simp only [globalUnit, FamilyParameters.one, rescale_identity,
    Decomposition.tangent_changeBasis, Decomposition.vertexVariation_unit]

/-! ### Term scalings -/

theorem termUnit_tangentAt (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) (left : Bool)
    (k : SquareSummand) (second : Bool) (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    (((pq.map (Jets.constant R)).mul (termUnit k second)).value left).tangentPart.coordinates
        (s, m, (a, b)) =
      termUnitCoefficient (pq.value left) k second s m a b := by
  rw [mul_value_of_trivial (Jets.constant R) left pq hg hs]
  have hb : (fun l h => Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l h) *
      (termUnit (R := R) k second).block l h) =
      fun l h => Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l h) := by
    funext l h
    exact _root_.mul_one _
  rw [hb, ← blockFamily_map, ← value_of_trivial left pq hg hs]
  simp only [termUnit, FamilyParameters.one, Decomposition.changeBasis_identity]
  cases second <;> cases m <;> by_cases hk : s = k <;>
    simp [termUnitCoefficient, Decomposition.coordinates, Decomposition.rescale,
      Decomposition.tangentPart, Jets.scalarJet, Decomposition.map, Jets.constant, hk]

/-! ### Block generators -/

/-- The inner decomposition of block `l` at the point `pq`. -/
def innerBlock (pq : FamilyParameters R) (l : Fin 7) : Decomposition R (Fin 2) (Fin 7) :=
  (blockBase R).changeBasis (pq.block l 0) (pq.block l 1) (pq.block l 2)

theorem innerBlock_map {S : Type} [CommRing S] (f : R →+* S) (pq : FamilyParameters R)
    (l : Fin 7) : (pq.map f).innerBlock l = (pq.innerBlock l).map f := by
  rw [innerBlock, innerBlock, Decomposition.map_changeBasis, blockBase_map]
  rfl

theorem blockUnit_block (k : Fin 7) (g : Fin 3) (i j : Fin 2) (l : Fin 7) (h : Fin 3) :
    (blockUnit (R := R) k g i j).block l h =
      if l = k then matrixJet (Decomposition.vertexUnit g h i j) else 1 := rfl

/-- The tangent of a block generator at the point `pq`, generalizing `blockUnitCoefficient`. -/
def blockUnitCoefficientAt (pq : FamilyParameters R) (left : Bool) (k : Fin 7) (g : Fin 3)
    (i j : Fin 2) (s : SquareSummand) (m : Mode) (a b : SquareVertex) : R :=
  if left then
    if s.1 = k then
      (blockBase R).coordinates (s.1, m, (a.1, b.1)) *
        (pq.innerBlock k).vertexUnitCoefficient g i j s.2 m a.2 b.2
    else 0
  else
    if s.2 = k then
      (pq.innerBlock k).vertexUnitCoefficient g i j s.1 m a.1 b.1 *
        (blockBase R).coordinates (s.2, m, (a.2, b.2))
    else 0

theorem blockUnitCoefficientAt_map {S : Type} [CommRing S] (f : R →+* S)
    (pq : FamilyParameters R) (left : Bool) (k : Fin 7) (g : Fin 3) (i j : Fin 2)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    blockUnitCoefficientAt (pq.map f) left k g i j s m a b =
      f (blockUnitCoefficientAt pq left k g i j s m a b) := by
  cases left <;>
    simp only [blockUnitCoefficientAt, innerBlock_map, Decomposition.vertexUnitCoefficient_map,
      ← blockBase_map f, Decomposition.coordinates_map, apply_ite f, _root_.map_mul, map_zero,
      Bool.false_eq_true, if_true, if_false]

theorem blockUnit_tangentAt (pq : FamilyParameters R)
    (hg : pq.global = fun _ => 1) (hs : pq.scale = fun _ _ => 1) (left : Bool)
    (k : Fin 7) (g : Fin 3) (i j : Fin 2) (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    (((pq.map (Jets.constant R)).mul (blockUnit k g i j)).value left).tangentPart.coordinates
        (s, m, (a, b)) =
      blockUnitCoefficientAt pq left k g i j s m a b := by
  rw [mul_value_of_trivial (Jets.constant R) left pq hg hs]
  simp only [blockUnit, FamilyParameters.one, Decomposition.changeBasis_identity,
    rescale_identity]
  let J (l : Fin 7) (h : Fin 3) : (Matrix (Fin 2) (Fin 2) (DualNumber R))ˣ :=
    (blockUnit (R := R) k g i j).block l h
  let ch (l : Fin 7) := (blockBase (DualNumber R)).changeBasis
    (Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l 0) * J l 0)
    (Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l 1) * J l 1)
    (Units.map (Jets.constant R).mapMatrix.toMonoidHom (pq.block l 2) * J l 2)
  have chEq (l : Fin 7) : ch l =
      ((pq.innerBlock l).map (Jets.constant R)).changeBasis (J l 0) (J l 1) (J l 2) := by
    simp only [ch, Decomposition.changeBasis_mul, innerBlock, Decomposition.map_changeBasis,
      blockBase_map]
  have slope (l s : Fin 7) (x y : Fin 2) :
      (ch l).tangentPart.coordinates (s, m, (x, y)) =
        if l = k then (pq.innerBlock l).vertexUnitCoefficient g i j s m x y else 0 := by
    rw [chEq]
    by_cases h : l = k
    · simp only [J, blockUnit_block, h, if_true, Decomposition.tangent_changeBasis,
        Decomposition.vertexVariation_unit]
    · simp only [J, blockUnit_block, h, if_false, Decomposition.changeBasis_identity]
      cases m <;> rfl
  have rhsL :
      (((blockBase (DualNumber R)).recursiveLeft ch).tangentPart.coordinates (s, m, (a, b))) =
       (blockBase R).coordinates (s.1, m, (a.1, b.1)) *
         (ch s.1).tangentPart.coordinates (s.2, m, (a.2, b.2)) := by
    rw [← blockBase_map (Jets.constant R)]
    cases m <;> simp [Decomposition.recursiveLeft, Decomposition.coordinates,
      Decomposition.tangentPart, Decomposition.outer, Decomposition.inner, Decomposition.map,
      Jets.constant]
  have rhsR :
      ((Decomposition.recursiveRight ch (blockBase (DualNumber R))).tangentPart.coordinates
        (s, m, (a, b))) =
       (ch s.2).tangentPart.coordinates (s.1, m, (a.1, b.1)) *
         (blockBase R).coordinates (s.2, m, (a.2, b.2)) := by
    rw [← blockBase_map (Jets.constant R)]
    cases m <;> simp [Decomposition.recursiveRight, Decomposition.coordinates,
      Decomposition.tangentPart, Decomposition.outer, Decomposition.inner, Decomposition.map,
      Jets.constant]
  cases left
  · change (Decomposition.recursiveRight ch (blockBase (DualNumber R))).tangentPart.coordinates
      _ = _
    rw [rhsR, slope]
    by_cases h : s.2 = k
    · subst h
      simp [blockUnitCoefficientAt]
    · simp [blockUnitCoefficientAt, h]
  · change ((blockBase (DualNumber R)).recursiveLeft ch).tangentPart.coordinates _ = _
    rw [rhsL, slope]
    by_cases h : s.1 = k
    · subst h
      simp [blockUnitCoefficientAt]
    · simp [blockUnitCoefficientAt, h]

/-! ### Transport of the closed forms along ring homomorphisms -/

theorem globalCoefficientAt_map {S : Type} [CommRing S] (f : R →+* S)
    (pq : FamilyParameters R) (left : Bool) (g : Fin 3) (i j : SquareVertex)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    ((pq.map f).value left).vertexUnitCoefficient g i j s m a b =
      f ((pq.value left).vertexUnitCoefficient g i j s m a b) := by
  rw [← value_map, Decomposition.vertexUnitCoefficient_map]

theorem termCoefficientAt_map {S : Type} [CommRing S] (f : R →+* S)
    (pq : FamilyParameters R) (left : Bool) (k : SquareSummand) (second : Bool)
    (s : SquareSummand) (m : Mode) (a b : SquareVertex) :
    termUnitCoefficient ((pq.map f).value left) k second s m a b =
      f (termUnitCoefficient (pq.value left) k second s m a b) := by
  rw [← value_map, termUnitCoefficient_map]

end FamilyParameters
end Brent
