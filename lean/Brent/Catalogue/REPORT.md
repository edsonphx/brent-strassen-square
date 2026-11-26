# Helper report — Tasks A, A′, B (PROVISIONAL)

> **Status: validation in progress.** Task A and Task A′ are complete and verified.
> Task B is fully written and every soundness proof compiles, but the kernel run over all
> 14,236 points (`Brent.Catalogue.Check.K000`–`K111`) is still building, so
> `Brent.Catalogue.Main` (the eight census theorems) has **not compiled yet**. Its
> `#print axioms` output, the clean from-scratch build, `leanchecker`, and the per-file timing
> and memory table will be added in the final version of this report.
> Task C was dropped as instructed (`VALIDATOR.md`).

Toolchain `leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`
(pins unchanged). Machine: i5-12600K (10 cores / 16 threads), 32 GB RAM, Windows 10.

## Task A — `Brent/Equidim/Equidim.lean` (done)

Statements exactly as in `TASKS.md` (namespace `Brent.Equidim`):

```lean
variable {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

theorem height_eq_ringKrullDim_of_isMaximal (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B
theorem ringKrullDim_localization_eq (m : Ideal B) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim B
theorem ringKrullDim_ne_top : ringKrullDim B ≠ ⊤

-- optional A4
theorem eq_zero_of_eval_eq_zero_of_eval_ne_zero {k : Type*} [Field k] [Infinite k]
    {τ : Type*} [Finite τ] {f : MvPolynomial τ k} (hf : f ≠ 0) (g : MvPolynomial τ k)
    (h : ∀ a : τ → k, MvPolynomial.eval a f ≠ 0 → MvPolynomial.eval a g = 0) : g = 0
```

`[IsAlgClosed k]` is kept but unused: the proofs work over any field (primed versions
`height_eq_ringKrullDim_of_isMaximal'` etc. carry no `IsAlgClosed`). Route: every maximal ideal of
`k[X₀…X_{n-1}]` has height `n` (induction via `finSuccEquiv`, Jacobson contraction,
`Polynomial.height_eq_height_add_one`); Noether normalization; going-down gives
`ht 𝔪 ≥ ht(𝔪 ∩ A)`, incomparability (strictly monotone comap) gives `≤`.

```
'Brent.Equidim.height_eq_ringKrullDim_of_isMaximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brent.Equidim.ringKrullDim_localization_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brent.Equidim.ringKrullDim_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brent.Equidim.eq_zero_of_eval_eq_zero_of_eval_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Task A′ — minimal imports (done)

`import Mathlib` replaced by (greedy minimization, each import tested for removal):

```lean
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Polynomial.RationalRoot
```

`KrullDimension.Field` gives `ringKrullDim` of a field; `Polynomial.RationalRoot` gives
UFD ⇒ integrally closed (needed for going-down over `k[X…]`). `KrullsHeightTheorem`,
`Jacobson.Ring` and `Polynomial.UniqueFactorization` come in transitively.
Check: `lake env lean Brent/Equidim/Equidim.lean` → exit 0, axioms as above.

## Task B — `Brent/Catalogue/` (written; kernel run in progress)

### Statements (exactly as in `TASKS.md`, two copies)

Definitions in `Defs.lean`: `factor`, `rk`, `profile`, `fullProfile`, `RankBounds` verbatim;
`AnchorTest` with spans:

```lean
rowSpace K M := Submodule.span K (Set.range (M.map (Int.cast : ℤ → K)))   -- rows
colSpace K M := rowSpace K Mᵀ
CanAnchor K p t a := ∀ m, rowSpace K (F t m) ≤ rowSpace K (F a m) ∧ colSpace K (F t m) ≤ colSpace K (F a m)
rankOne / rankTwo := summands with rank triple (1,1,1) / (2,2,2)
Useful K p a := a ∈ rankTwo K p ∧ 6 ≤ #(rank-one children of a)
AnchorTest K p := 6 ≤ #(useful rank-two summands) ∧ ∀ t ∈ rankOne K p, ∃ a, Useful K p a ∧ CanAnchor K p t a
```

This is the filter of paper lines 676–694 and of `alphatensor_rank_profiles.py` (a candidate
anchor is a *useful* one, as in the script's `(compatible & useful).any`).

In `Main.lean`, namespaces `Brent.Catalogue.Q` (K = ℚ) and `Brent.Catalogue.F3` (K = ZMod 3):

```lean
theorem card_fullProfile : (Finset.univ.filter fun p => profile K p = fullProfile).card = 14149
theorem fullProfile_iff_rankBounds : ∀ p, profile K p = fullProfile ↔ RankBounds K p
theorem card_not_rankBounds : (Finset.univ.filter fun p => ¬ RankBounds K p).card = 87
theorem anchor_excluded :
    (Finset.univ.filter fun p => profile K p = fullProfile ∧ ¬ AnchorTest K p) = {2445, 5969}
```

**`#print axioms`: pending** (requires the chunk run).

### Method

* **Data.** `scripts/gen_catalogue_lean.py` checks the npz SHA-256
  (`15d27e30…a06a3`, verified) and writes each point as one hex literal (digit
  `16(3s+m)+4i+j` = entry + 4), plus one certificate number per point. 112 chunks × 128 points.
* **Ranks (both fields).** For every matrix, the kernel checks a Schur certificate: a nonzero
  `r × r` pivot minor (⇒ rank ≥ r) and the identity `det D · M = X · M[I, :]` for all 16
  entries (⇒ rank ≤ r). Checked exactly over ℤ; a flag says the pivot is also nonzero mod 3,
  otherwise a separate mod-3 certificate is checked. `Sound.lean`: `certChk_sound` proves a
  passing certificate pins `Matrix.rank` over any field of characteristic `q`, so
  `rk ℚ` and `rk (ZMod 3)` are each pinned independently (`rk_eq_of_matOK`).
* **Profile / rank bounds** reduce to counts of certified ranks (`profile_eq_full_iff`,
  `rankBounds_iff`).
* **Anchors (passing points).** Witnesses only: six rank-two anchors and, for each rank-one
  summand, its anchor (six each). Per claimed pair and mode, the kernel checks that the child's
  pivot row (resp. column) is in the span of the anchor's pivot rows (resp. columns).
  `Anchor.lean` proves this gives span containment (`canAnchor_of_compat`), and `Census.lean`
  proves `anchorOK ⇒ AnchorTest` (`anchorTest_of_anchorOK`), for each field.
* **Anchor failures 2445, 5969** (own files `NegCheck.lean`, `Neg.lean`): per non-compatible
  pair a vector `n` orthogonal to the anchor's rows (columns) but not to a row (column) of the
  child; at most five rank-two summands keep ≥ 6 unwitnessed children. `not_anchorTest_of_negOK`
  proves `¬ AnchorTest`, separately for ℚ and ZMod 3.

### Discrepancies

None found. Python predictions agree with `alphatensor_rank_profiles.json` on all index lists:
14,149 full-profile points over both fields, full profile ⇔ rank bounds, the same 87 excluded
indices, and anchor failures exactly {2445, 5969} (2445 has two useful anchors, 5969 one).
One passing point (14088) has no clean 6 × 6 partition; a capacity-6 assignment exists and is used.

### Build commands

```
python -I scripts/gen_catalogue_lean.py data/alphatensor_14236_factorizations.npz project
cd project
lake exe cache get
lake build Brent.Equidim.Equidim
lake build Brent.Catalogue.Checks          # the 112 kernel-check modules (the long part)
lake build Brent.Catalogue.Main            # census theorems + #print axioms
lake env leanchecker <module>              # every module (final report)
```

Kernel checks use `decide +kernel` only; no `sorry`, `admit`, `native_decide`.
Each chunk file holds 32 theorems of 4 points (the kernel's evaluation cache is per
declaration; 8 points per declaration peaked at 2.3 GB, 128 per declaration exceeded 21 GB).

**Timings and peak memory: pending.** Measured so far: ~1.8 s of kernel time per point
(both fields), so ~7–8 CPU-hours for the full run; wall clock with 15 parallel files is
running now.

### Generated files (not in the zip — regenerate with the generator)

Generator `scripts/gen_catalogue_lean.py`, SHA-256
`5ce1ca078557916668be0a9b0be78a5fd21b7c8667baa13ba7bd526d30e1feaa`.
Regenerating writes 341 files (49 MB); re-running it here reproduced all 341 byte-identically.
Their SHA-256 sums are in `GENERATED_SHA256.txt`.
