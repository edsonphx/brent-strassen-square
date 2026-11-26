import Brent.Catalogue.Point
import Brent.Catalogue.NegData

/-!
# Kernel check of the anchor-test failures (points 2445 and 5969)

A witness `w` certifies that `w.a` cannot anchor `w.t`: on side `w.side` (0 rows, 1 columns) of
mode `w.m`, the vector `n` is orthogonal (in characteristic `q`) to every row of the anchor's
matrix but not to row `w.row` of the child's. `negOK f q p ws` checks all witnesses and that at
most five rank-two summands keep at least six rank-one summands without a witness.
-/

namespace Brent.Catalogue

def dotRow (M : Nat → Nat → Int) (i : Nat) (w : Wit) : Int :=
  M i 0 * w.n0 + M i 1 * w.n1 + M i 2 * w.n2 + M i 3 * w.n3

/-- The side-`w.side` view of matrix `(s, w.m)`: itself or its transpose. -/
def sideMat (N s : Nat) (w : Wit) : Nat → Nat → Int :=
  if w.side == 0 then mat N s w.m else fun i j => mat N s w.m j i

def witOK (q N : Nat) (w : Wit) : Bool :=
  Nat.blt w.t 49 && Nat.blt w.a 49 && Nat.blt w.m 3 && Nat.blt w.row 4 &&
    all4 (fun i => zq q (dotRow (sideMat N w.a w) i w)) &&
    !zq q (dotRow (sideMat N w.t w) w.row w)

def hasWit (ws : List Wit) (t a : Nat) : Bool := ws.any fun w => w.t == t && w.a == a

def negOK (f : Bool) (q p : Nat) (ws : List Wit) : Bool :=
  ws.all (witOK q (pointNat p)) &&
    Nat.ble (cnt 49 fun a => triple f (certNat p) a 2 &&
      Nat.ble 6 (cnt 49 fun t => triple f (certNat p) t 1 && !hasWit ws t a)) 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem neg2445_Q : negOK false 0 2445 w2445_Q = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem neg2445_F : negOK true 3 2445 w2445_F = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem neg5969_Q : negOK false 0 5969 w5969_Q = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem neg5969_F : negOK true 3 5969 w5969_F = true := by decide +kernel

end Brent.Catalogue
