import Brent.Catalogue.Kernel
import Brent.Catalogue.Data
import Brent.Catalogue.Cert
import Brent.Catalogue.Expected

/-!
# The per-point kernel check

`pointOK p` checks, for catalogue point `p`, all `147` rank certificates (over `ℚ` and over
`ZMod 3`), that the certified ranks give the full profile and satisfy the rank bounds exactly
when `p ∉ bad87`, and (for full-profile points outside `neg2`) the anchor certificate.
-/

namespace Brent.Catalogue

/-- The packed factors of point `p`. -/
def pointNat (p : Nat) : Nat := (Data.chunks.getD (p / 128) []).getD (p % 128) 0

/-- The certificate number of point `p`. -/
def certNat (p : Nat) : Nat := (Cert.chunks.getD (p / 128) []).getD (p % 128) 0

def pointOK (p : Nat) : Bool :=
  let N := pointNat p
  let C := certNat p
  let bad := bad87.contains p
  ranksOK N C &&
    (fullB false C == !bad) && (rbB false C == !bad) &&
    (fullB true C == !bad) && (rbB true C == !bad) &&
    (bad || neg2.contains p || anchorOK N C)

/-- `pointOK` holds on `[lo, lo + n)`. -/
def rangeOK (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => rangeOK lo n && pointOK (lo + n)

theorem rangeOK_spec (lo n : Nat) :
    rangeOK lo n = true ↔ ∀ k, k < n → pointOK (lo + k) = true := by
  induction n with
  | zero => simp [rangeOK]
  | succ n ih =>
    simp only [rangeOK, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

theorem rangeOK_append {lo n n' : Nat} (h1 : rangeOK lo n = true)
    (h2 : rangeOK (lo + n) n' = true) : rangeOK lo (n + n') = true := by
  rw [rangeOK_spec] at *
  intro k hk
  by_cases hkn : k < n
  · exact h1 k hkn
  · have := h2 (k - n) (by omega)
    rwa [show lo + n + (k - n) = lo + k by omega] at this

/-- `rangeOK_append` with every size given explicitly: the side conditions are closed by `rfl` on
numerals, so no unification of `lo + n` or `n + n'` is needed. -/
theorem rangeOK_join (lo n mid n' tot : Nat) (hmid : lo + n = mid) (htot : n + n' = tot)
    (h1 : rangeOK lo n = true) (h2 : rangeOK mid n' = true) : rangeOK lo tot = true := by
  subst hmid htot
  exact rangeOK_append h1 h2

end Brent.Catalogue
