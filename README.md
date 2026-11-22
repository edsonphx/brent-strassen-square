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
| Rank of the projected mixed quadratic map over GF(3) | 648 |
| Coprime leading monomials in the certificate | 54 |
| Local dimension | **197** |
| Initial local Hilbert function over GF(3) | **(1, 251, 30978)** |

The two displayed smooth formal branches each have dimension 197 and their
formal intersection has dimension 143. These statements concern the geometry
of a fixed decomposition.

## Verify

Use Python 3.9 or newer with NumPy installed. From the repository root run

```sh
bash verify.sh
```

The verifier runs offline with Python and NumPy. It checks
SHA-256 hashes, contracts the signed tensor over the integers, rebuilds the
Jacobian and all tangent generators, checks the frozen basis and ranks, and
recomputes the mixed coefficients of the 54 certified quadrics. It prints
`VERIFIED: local_dim = 197` when all finite checks pass. The algebraic
implications of these checks appear in the preprint.

| File | Contents |
| --- | --- |
| [paper.pdf](paper.pdf), [paper.tex](paper.tex) | Preprint and standalone LaTeX source |
| [verify_certificate.py](verify_certificate.py) | Exact integer contractions and packed GF(3) elimination |
| [data/strassen_square_factors.npz](data/strassen_square_factors.npz) | Signed integer arrays `U`, `V`, `W`, each of shape `49 x 16` |
| [data/tangent_bases.npz](data/tangent_bases.npz) | Integral arrays `G`, `X`, `Y` with 143, 54, and 54 basis directions |
| [data/cycle81_54_regular_sequence_certificate.npz](data/cycle81_54_regular_sequence_certificate.npz) | 54 left-kernel functionals, quadrics, and the leading-monomial matching |
| [data/54_functionals_sparse.csv](data/54_functionals_sparse.csv), [data/54_polynomials_sparse.csv](data/54_polynomials_sparse.csv) | Human-readable copies of the modular witnesses |
| [SHA256SUMS.txt](SHA256SUMS.txt) | Integrity manifest |

The arrays use zero-based row-major coordinates and summand-major parameter
ordering. The output factors are in direct output order. The mixed monomial
$x_i y_j$ has column index `54*i+j`. Basis directions have shape
`(#directions, 49, 3, 16)` before flattening. The verifier regenerates their
ordering from the base factors and exact group derivatives.

Compile the source with `tectonic paper.tex` or two runs of `pdflatex paper.tex`.
No BibTeX database is required.

## Citation

Edson Soares. *Exact Local Dimension of the Brent Variety V(4,4,4 | 49)
at the Recursive Strassen-Square Point via Quadratic Obstructions*.
Preprint and verification package, version 1.0.0, 2026.

[CITATION.cff](CITATION.cff) contains machine-readable citation metadata.
When the release is archived, use its version-specific Zenodo DOI.

## Licenses

The preprint and numerical data are licensed under
[CC BY 4.0](LICENSE-CC-BY-4.0.txt). The verifier and shell script are
licensed under the [MIT License](LICENSE).
