# Paper route for §4 lines 444–482 and §5 lines 521–545

Goal: formalize the paper's own steps (Cohen–Macaulay and Hilbert–Samuel), not a replacement.
Mathlib at our pin has regular sequences (`RingTheory/Regular/RegularSequence.lean`:
`IsWeaklyRegular`, `IsRegular`, `isRegular_cons_iff`, permutation in local rings), Krull's height
theorem, `Ideal.height`, Krull's intersection theorem, and `Polynomial.hilbertPoly` (Hilbert
polynomial of `p / (1 - X)^d`). It has no Cohen–Macaulay rings, no Hilbert–Serre theorem and no
Hilbert–Samuel dimension theorem. Each step below is one small Mathlib-only file under
`Brent/CM/`, checked on the GitHub quick check before the next one starts.

Already in place: `Groebner.isGroebnerBasis_of_coprime`, `Groebner.initialIdeal_span_of_coprime`
(row 11, compiles), `Groebner.MonomialHeight.height_pairIdeal` (height 54, compiles),
`InitialForms.*` (graded presentation `gr(A/I) = gr(A)/in(I)` under regularity, drafted).

## A. Hilbert–Serre for standard graded algebras (`Brent/CM/HilbertSerre.lean`)
1. Graded pieces of a finitely generated graded `k[x₁..x_N]`-module are finite dimensional.
2. Hilbert series is `p(t) / (1 - t)^N`; induction on `N` via the exact sequence
   `0 → K → M(-1) →·x_N→ M → M/x_N M → 0`.
3. Hilbert polynomial from `Polynomial.hilbertPoly`; its degree `+ 1` is the dimension of the
   support (`d(M)`).

## B. Hilbert–Samuel dimension theorem (`Brent/CM/HilbertSamuel.lean`)
1. For a Noetherian local `(A, m)`: `n ↦ length(A/mⁿ)` is eventually a polynomial of degree
   `d(A)` (apply A to `gr_m(A)`, finitely generated over `k[x₁..x_μ]`).
2. `dim A = d(A) = δ(A)` (Krull dimension = Hilbert–Samuel degree = minimal number of
   parameters). `δ ≥ dim` is Krull's height theorem (in Mathlib); `dim ≥ d` and `d ≥ δ` are new.
3. `dim A = dim gr_m(A)`.

## C. Lemma 4.1, lines 457–482 (`Brent/CM/Lemma41.lean`)
1. `gr(A/I) = gr(A)/in(I)` when the initial forms are regular (`InitialForms`, drafted).
2. A homogeneous nonzerodivisor of degree `d` drops the Hilbert polynomial degree by one
   (A.2 exact sequence).
3. Conclusion: `dim A/I = dim gr(A/I) ≤ N − s` (B.3 + C.2 by induction).

## D. Cohen–Macaulay, lines 444–456 (`Brent/CM/CohenMacaulay.lean`)
1. Graded depth via regular sequences of homogeneous elements in the irrelevant ideal.
2. `k[x₁..x_N]` is Cohen–Macaulay: `x₁, …, x_N` is a maximal regular sequence.
3. Unmixedness: in a graded CM ring, homogeneous `f₁..f_s` with `height (f) = s` form a regular
   sequence (prime avoidance for homogeneous ideals + associated primes are minimal).
4. `height (q) = height in(q) = 54` (same Hilbert function, from the Gröbner basis: standard
   monomials are a basis of `R/I` and of `R/in(I)`), hence the `qᵢ` form a regular sequence.

## E. Lift over `ℤ₍₃₎`, lines 521–545 (`Brent/CM/Lift.lean`)
1. `3` is regular on `ℤ₍₃₎[z]`; modulo `3` the `q̃ᵢ` are the `qᵢ` over `𝔽₃` (D.4), so
   `3, q̃₁, …, q̃₅₄` is regular on `ℤ₍₃₎[z]` (`isRegular_cons_iff`).
2. Graded local permutation (Mathlib `isWeaklyRegular_of_perm_of_subset_maximalIdeal` after
   localizing at the irrelevant ideal): `q̃₁, …, q̃₅₄, 3` is regular, so `q̃` is regular over
   `ℤ₍₃₎[z]` and, by flatness, over `ℚ[z]` (`IsWeaklyRegular.isWeaklyRegular_lTensor`) and `ℚ⟦z⟧`.

Order: A → B → C (closes 457–482) → D (closes 444–456) → E (closes 521–545).
Estimated size: A ≈ 600 lines, B ≈ 900, C ≈ 200, D ≈ 900, E ≈ 300.
