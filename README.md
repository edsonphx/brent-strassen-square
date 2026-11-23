# Exact local dimension at the recursive Strassen square

At the ordered 49-summand Strassen-square point of the Brent scheme for
$4\times4$ matrix multiplication, the **local Krull dimension is 197**
in characteristics three and zero. The Zariski tangent dimension is 251.
The proof combines two exact recursive deformation families with a regular
sequence of 54 quadratic initial forms. The accompanying preprint gives the
proof, including the lift through `Z_(3)`.

| Quantity | Exact value |
| --- | ---: |
| Scalar variables and Brent equations | 2,352 and 4,096 |
| Jacobian rank | 2,101 |
| Zariski tangent dimension | 251 |
| Global isotropy and term-rescaling orbit dimension | 143 |
| Complementary recursive tangent dimensions | 54 and 54 |
| Augmented rank over Q and GF(3) | 2,749 |
| Rank of the projected mixed quadratic map over Q and GF(3) | 648 |
| Coprime leading monomials in the certificate | 54 |
| Local dimension | **197** |
| Initial local Hilbert function in both characteristics | **(1, 251, 30978)** |

The two displayed smooth formal branches each have dimension 197 and their
formal intersection has dimension 143. These statements concern the geometry
of a fixed decomposition.

The preprint derives the orbit and branch tangent dimensions by hand,
details the formal dimension argument, and specifies the finite checks
in an appendix. It also gives two explicit smooth deformations and compares
the families with the 14,236 integral AlphaTensor decompositions. Exactly
14,149 entries have the full family rank profile in both characteristics.
The anchor test excludes two of these entries from both family closures.
The 14,147 remaining entries all have the full profile and their membership
in the closures is unresolved.

## Verify

Use Python 3.9 or newer with NumPy installed. From the repository root run

```sh
bash verify.sh
```

The verifier runs offline with Python and NumPy. It checks
SHA-256 hashes, contracts the signed tensor over the integers, rebuilds the
Jacobian and all tangent generators, checks the frozen basis and ranks, and
recomputes the mixed coefficients of the 54 certified quadrics. It checks
the Jacobian and augmented ranks both modulo three and by integer row
elimination using only unit pivots. It prints
`VERIFIED: local_dim = 197` when all finite checks pass. The algebraic
implications of these checks appear in the preprint.

`bash verify.sh --full` also checks all 28,710 non-mixed monomials in
each of the 54 quadratic forms, certifies the two explicit rank-2155
deformation endpoints, and verifies 40 additional integer points.

| File | Contents |
| --- | --- |
| [paper.pdf](paper.pdf), [paper.tex](paper.tex) | Preprint and standalone LaTeX source |
| [verify_certificate.py](verify_certificate.py) | Exact integer contractions, packed GF(3) elimination, and integer rank verification |
| [data/strassen_square_factors.npz](data/strassen_square_factors.npz) | Signed integer arrays `U`, `V`, `W`, each of shape `49 x 16` |
| [data/tangent_bases.npz](data/tangent_bases.npz) | Integral arrays `G`, `X`, `Y` with 143, 54, and 54 basis directions |
| [data/regular_sequence_certificate.npz](data/regular_sequence_certificate.npz) | 54 left-kernel functionals, quadrics, and the leading-monomial matching |
| [data/54_functionals_sparse.csv](data/54_functionals_sparse.csv), [data/54_polynomials_sparse.csv](data/54_polynomials_sparse.csv) | Human-readable copies of the modular witnesses |
| [alphatensor_rank_profiles.py](alphatensor_rank_profiles.py), [alphatensor_rank_profiles.json](alphatensor_rank_profiles.json) | Exact catalogue filters and excluded indices |
| [SHA256SUMS.txt](SHA256SUMS.txt) | Integrity manifest |

The arrays use zero-based row-major coordinates and summand-major parameter
ordering. The output factors are in direct output order. The mixed monomial
$x_i y_j$ has column index `54*i+j`. Basis directions have shape
`(#directions, 49, 3, 16)` before flattening. The verifier regenerates their
ordering from the base factors and exact group derivatives.

Compile the source with `tectonic paper.tex` or two runs of `pdflatex paper.tex`.
No BibTeX database is required.

To rerun the catalogue filters, download the pinned public archive and pass
it to the census script. The main verifier works offline independently of
this experiment.

```sh
curl -fLsS https://raw.githubusercontent.com/google-deepmind/alphatensor/1949163da3bef7e3eb268a3ac015fd1c2dbfc767/nonequivalence/alphatensor_14236_factorizations.npz -o alphatensor-catalog.npz
python3 alphatensor_rank_profiles.py alphatensor-catalog.npz
```

## Citation

Edson Soares de Souza. *Exact Local Dimension of the Brent Variety V(4,4,4 | 49)
at the Recursive Strassen-Square Point via Quadratic Obstructions* (2026).
Use the commit permalink when citing this manuscript revision.

The [Zenodo concept DOI](https://doi.org/10.5281/zenodo.24449375)
resolves to the latest archived version. To cite specific files, use the
DOI shown on that version's record. Archived releases include
[version 1.1.2](https://doi.org/10.5281/zenodo.24451072),
[version 1.1.1](https://doi.org/10.5281/zenodo.24450996),
[version 1.1.0](https://doi.org/10.5281/zenodo.24450467) and the
[original five-page version](https://doi.org/10.5281/zenodo.24449376).

## Licenses

The preprint and numerical data are licensed under
[CC BY 4.0](LICENSE-CC-BY-4.0.txt). The verifier and shell script are
licensed under the [MIT License](LICENSE).
