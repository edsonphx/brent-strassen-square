/-!
# Kernel-evaluated checks for the catalogue census

Everything here depends only on `Init` and is evaluated by `decide +kernel` in the
`Brent.Catalogue.Check.K###` modules. Nothing here is trusted: `Brent.Catalogue.Sound` proves
what a passing check means for `Matrix.rank`, row and column spaces, profiles and the anchor
test.

Layout of the certificate number `C` of a point (bit offsets):
* matrix `(s, m)` occupies the 32 bits at `32 * (3 * s + m)`:
  bits 0–2 `r` (rank over `ℚ`), bits 3–8 the pivot rows `i₀ i₁ i₂` (2 bits each),
  bits 9–14 the pivot columns `j₀ j₁ j₂`, bit 15 the flag "same certificate mod 3",
  bits 16–30 a separate certificate for `ZMod 3` in the same layout (used when the flag is 0);
* at bit `4704`, six anchors (6 bits each), then at bit `4740` one group index per summand
  (3 bits each; `7` means "not rank one").
-/

namespace Brent.Catalogue

/-- Entry `(i, j)` of factor matrix `(s, m)` of a packed point: hex digit
`16 * (3 * s + m) + 4 * i + j` minus `4`. -/
def ent (N s m i j : Nat) : Int :=
  (((((N >>> (64 * (3 * s + m))) % 18446744073709551616) >>> (4 * (4 * i + j))) % 16 : Nat) : Int)
    - 4

/-- `x` vanishes in characteristic `q` (`x % 0 = x`). -/
def zq : Nat → Int → Bool
  | 0, x => x == 0
  | q + 1, x => x % ((q + 1 : Nat) : Int) == 0

/-- Conjunction over `{0, 1, 2, 3}`. -/
def all4 (f : Nat → Bool) : Bool := f 0 && f 1 && f 2 && f 3

/-- Conjunction over `{0, 1, 2}`. -/
def all3 (f : Nat → Bool) : Bool := f 0 && f 1 && f 2

/-- Conjunction over `{0, 1, 2, 3}²`. -/
def all16 (f : Nat → Nat → Bool) : Bool :=
  f 0 0 && f 0 1 && f 0 2 && f 0 3 && f 1 0 && f 1 1 && f 1 2 && f 1 3 &&
  f 2 0 && f 2 1 && f 2 2 && f 2 3 && f 3 0 && f 3 1 && f 3 2 && f 3 3

/-- Conjunction over `{0, …, n - 1}`. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allBelow n f && f n

/-- Number of `k < n` with `f k`. -/
def cnt : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => cnt n f + (if f n then 1 else 0)

/-! ### Determinants and Schur residuals -/

def det3 (a b c d e f g h k : Int) : Int :=
  a * (e * k - f * h) - b * (d * k - f * g) + c * (d * h - e * g)

def det4 (M : Nat → Nat → Int) : Int :=
  M 0 0 * det3 (M 1 1) (M 1 2) (M 1 3) (M 2 1) (M 2 2) (M 2 3) (M 3 1) (M 3 2) (M 3 3)
  - M 0 1 * det3 (M 1 0) (M 1 2) (M 1 3) (M 2 0) (M 2 2) (M 2 3) (M 3 0) (M 3 2) (M 3 3)
  + M 0 2 * det3 (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) (M 3 0) (M 3 1) (M 3 3)
  - M 0 3 * det3 (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) (M 3 0) (M 3 1) (M 3 2)

def del2 (A : Nat → Nat → Int) (i0 i1 j0 j1 : Nat) : Int :=
  A i0 j0 * A i1 j1 - A i0 j1 * A i1 j0

/-- `det D * T r j - (T[r, J] adj(D) A[I, j])` for the `2 × 2` pivot `D = A[I, J]`. -/
def span2 (T A : Nat → Nat → Int) (i0 i1 j0 j1 r j : Nat) : Int :=
  del2 A i0 i1 j0 j1 * T r j -
    (T r j0 * (A i1 j1 * A i0 j - A i0 j1 * A i1 j) +
      T r j1 * (A i0 j0 * A i1 j - A i1 j0 * A i0 j))

/-- Cofactor `C_ab` of the `3 × 3` pivot `A[I, J]`. -/
def cof3 (A : Nat → Nat → Int) (i0 i1 i2 j0 j1 j2 : Nat) (a b : Nat) : Int :=
  let d := fun (u v : Nat) =>
    A (if u = 0 then i0 else if u = 1 then i1 else i2) (if v = 0 then j0 else if v = 1 then j1 else j2)
  let r0 := if a = 0 then 1 else 0
  let r1 := if a = 2 then 1 else 2
  let c0 := if b = 0 then 1 else 0
  let c1 := if b = 2 then 1 else 2
  let m := d r0 c0 * d r1 c1 - d r0 c1 * d r1 c0
  if (a + b) % 2 = 0 then m else -m

def del3 (A : Nat → Nat → Int) (i0 i1 i2 j0 j1 j2 : Nat) : Int :=
  A i0 j0 * cof3 A i0 i1 i2 j0 j1 j2 0 0 + A i0 j1 * cof3 A i0 i1 i2 j0 j1 j2 0 1 +
    A i0 j2 * cof3 A i0 i1 i2 j0 j1 j2 0 2

def span3 (T A : Nat → Nat → Int) (i0 i1 i2 j0 j1 j2 r j : Nat) : Int :=
  let x := fun (b : Nat) => T r (if b = 0 then j0 else if b = 1 then j1 else j2)
  let y := fun (a : Nat) => A (if a = 0 then i0 else if a = 1 then i1 else i2) j
  let C := cof3 A i0 i1 i2 j0 j1 j2
  del3 A i0 i1 i2 j0 j1 j2 * T r j -
    (y 0 * (C 0 0 * x 0 + C 0 1 * x 1 + C 0 2 * x 2) +
     y 1 * (C 1 0 * x 0 + C 1 1 * x 1 + C 1 2 * x 2) +
     y 2 * (C 2 0 * x 0 + C 2 1 * x 1 + C 2 2 * x 2))

/-- The pivot determinant of a rank-`r` certificate. -/
def delta (M : Nat → Nat → Int) (r i0 i1 i2 j0 j1 j2 : Nat) : Int :=
  match r with
  | 0 => 1
  | 1 => M i0 j0
  | 2 => del2 M i0 i1 j0 j1
  | 3 => del3 M i0 i1 i2 j0 j1 j2
  | _ => det4 M

/-- The Schur residual of a rank-`r` certificate at `(i, j)`. -/
def resid (M : Nat → Nat → Int) (r i0 i1 i2 j0 j1 j2 i j : Nat) : Int :=
  match r with
  | 0 => M i j
  | 1 => M i0 j0 * M i j - M i j0 * M i0 j
  | 2 => span2 M M i0 i1 j0 j1 i j
  | 3 => span3 M M i0 i1 i2 j0 j1 j2 i j
  | _ => 0

/-- Residuals vanish at all 16 entries, for a fixed rank `r` (dispatch outside the loop). -/
def residOK (q : Nat) (M : Nat → Nat → Int) (r i0 i1 i2 j0 j1 j2 : Nat) : Bool :=
  match r with
  | 0 => all16 fun i j => zq q (M i j)
  | 1 => all16 fun i j => zq q (M i0 j0 * M i j - M i j0 * M i0 j)
  | 2 => all16 fun i j => zq q (span2 M M i0 i1 j0 j1 i j)
  | 3 => all16 fun i j => zq q (span3 M M i0 i1 i2 j0 j1 j2 i j)
  | _ => true

/-- A rank-`r` certificate in characteristic `q`: indices in range, nonzero pivot
determinant, vanishing residuals. -/
def certChk (q : Nat) (M : Nat → Nat → Int) (r i0 i1 i2 j0 j1 j2 : Nat) : Bool :=
  Nat.ble r 4 && !zq q (delta M r i0 i1 i2 j0 j1 j2) && residOK q M r i0 i1 i2 j0 j1 j2

/-! ### Decoding the certificate number -/

/-- The 32-bit code of matrix `(s, m)`. -/
def code (C s m : Nat) : Nat := (C >>> (32 * (3 * s + m))) % 4294967296

def cR (c : Nat) : Nat := c % 8
def cI0 (c : Nat) : Nat := (c >>> 3) % 4
def cI1 (c : Nat) : Nat := (c >>> 5) % 4
def cI2 (c : Nat) : Nat := (c >>> 7) % 4
def cJ0 (c : Nat) : Nat := (c >>> 9) % 4
def cJ1 (c : Nat) : Nat := (c >>> 11) % 4
def cJ2 (c : Nat) : Nat := (c >>> 13) % 4
def cSame (c : Nat) : Bool := (c >>> 15) % 2 == 1
/-- The `ZMod 3` half of a code. -/
def cF (c : Nat) : Nat := c >>> 16

/-- The factor matrix `(s, m)` of the packed point `N`. -/
def mat (N s m : Nat) : Nat → Nat → Int := fun i j => ent N s m i j

/-- Rank-certificate check with code `c` in characteristic `q`. -/
def chkCode (q : Nat) (M : Nat → Nat → Int) (c : Nat) : Bool :=
  certChk q M (cR c) (cI0 c) (cI1 c) (cI2 c) (cJ0 c) (cJ1 c) (cJ2 c)

/-- Pivot determinant of code `c`. -/
def deltaCode (M : Nat → Nat → Int) (c : Nat) : Int :=
  delta M (cR c) (cI0 c) (cI1 c) (cI2 c) (cJ0 c) (cJ1 c) (cJ2 c)

/-- The code used for `ZMod 3`. -/
def codeF (c : Nat) : Nat := if cSame c then c % 65536 else cF c

/-- Both rank certificates of matrix `(s, m)`: exact for `ℚ`; for `ZMod 3` either the same
certificate with pivot determinant nonzero mod 3, or a separate one checked mod 3. -/
def matOK (N C s m : Nat) : Bool :=
  let c := code C s m
  chkCode 0 (mat N s m) c &&
    (if cSame c then !zq 3 (deltaCode (mat N s m) c) else chkCode 3 (mat N s m) (cF c))

/-- Certified rank over `ℚ` (`f = false`) or `ZMod 3` (`f = true`). -/
def rkC (f : Bool) (C s m : Nat) : Nat :=
  if f then cR (codeF (code C s m)) else cR (code C s m)

def ranksOK (N C : Nat) : Bool :=
  allBelow 49 fun s => matOK N C s 0 && matOK N C s 1 && matOK N C s 2

/-! ### Profiles and rank bounds -/

def triple (f : Bool) (C s : Nat) (r : Nat) : Bool :=
  rkC f C s 0 == r && rkC f C s 1 == r && rkC f C s 2 == r

def fullB (f : Bool) (C : Nat) : Bool :=
  cnt 49 (fun s => triple f C s 1) == 36 && cnt 49 (fun s => triple f C s 2) == 12 &&
    cnt 49 (fun s => triple f C s 4) == 1

def rbB (f : Bool) (C : Nat) : Bool :=
  Nat.ble (cnt 49 fun s => Nat.blt 1 (rkC f C s 0) || Nat.blt 1 (rkC f C s 1) ||
    Nat.blt 1 (rkC f C s 2)) 13 &&
  Nat.ble (cnt 49 fun s => Nat.blt 2 (rkC f C s 0) || Nat.blt 2 (rkC f C s 1) ||
    Nat.blt 2 (rkC f C s 2)) 1

/-! ### Anchor certificates -/

def anc (C g : Nat) : Nat := (C >>> (4704 + 6 * g)) % 64
def grp (C t : Nat) : Nat := (C >>> (4740 + 3 * t)) % 8

/-- Row `r` of `T` lies in the row space of `A`, certified with the `2 × 2` pivot of `A`. -/
def rowIn (T A : Nat → Nat → Int) (r i0 i1 j0 j1 : Nat) : Bool :=
  all4 fun j => span2 T A i0 i1 j0 j1 r j == 0

/-- Compatibility of rank-one summand `t` with rank-two summand `a`, in every mode, using
the pivot row and column of `t` and the pivot of `a` (all from the certificates). -/
def compat (N C t a : Nat) : Bool :=
  all3 fun m =>
    (let ct := code C t m
     let ca := code C a m
     let T := mat N t m
     let A := mat N a m
     rowIn T A (cI0 ct) (cI0 ca) (cI1 ca) (cJ0 ca) (cJ1 ca) &&
     rowIn (fun i j => T j i) (fun i j => A j i) (cJ0 ct) (cJ0 ca) (cJ1 ca) (cI0 ca) (cI1 ca))

def sameAll (C : Nat) : Bool :=
  allBelow 49 fun s => cSame (code C s 0) && cSame (code C s 1) && cSame (code C s 2)

/-- The anchor certificate: six distinct rank-two anchors, every rank-one summand assigned
to a compatible anchor, every anchor with at least six assigned summands. -/
def anchorOK (N C : Nat) : Bool :=
  sameAll C &&
  (allBelow 6 fun g =>
    Nat.blt (anc C g) 49 && triple false C (anc C g) 2 &&
    (allBelow g fun h => !(anc C h == anc C g)) &&
    Nat.ble 6 (cnt 49 fun t => triple false C t 1 && grp C t == g)) &&
  (allBelow 49 fun t => !(triple false C t 1) ||
    (Nat.blt (grp C t) 6 && compat N C t (anc C (grp C t))))

end Brent.Catalogue
