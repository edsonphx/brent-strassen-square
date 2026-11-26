# Actual AlphaTensor source replay

The supplied binary `alphatensor_14236_factorizations.npz` matches the SHA-256
pinned in the source generator and CI:

```
15d27e300a68868710c2f5824f7987b10e004c6d7de6a3e65ae35caf42ed06a3
```

Source: `google-deepmind/alphatensor`, `nonequivalence/alphatensor_14236_factorizations.npz`,
pinned revision `1949163da3bef7e3eb268a3ac015fd1c2dbfc767`.

## Executed checks

- Loaded with `allow_pickle=False`, exact signed `int64` layout `(14236, 49, 3, 16)`.
- Regenerated the full Lean catalogue with `gen_catalogue_lean.py` from the real NPZ.
  The generator checked both modular rank arrays and the equal rank-profile and
  rank-bound sets. Output: 14,149 passing, 87 failing; anchor failures `[2445, 5969]`.
- The independent `verify_source_binding.py` decoded every hexadecimal digit of
  the actual generated `Data/D*.lean` chunks. All **33,483,072** entries agree,
  with the correct point, summand, mode and row-major matrix entry ordering.
- All **341** file hashes in the checked-in `GENERATED_SHA256.txt` agree with the
  regenerated Data, Cert, Check and metadata modules (`sha256sum -c --quiet`, exit 0).
- Independent `tools/alphatensor_census.py` replay over F3 gave 14,149 passing
  rank bounds and full profile, 87 rank exclusions, and exactly `[2445, 5969]`
  anchor exclusions, total 89. The 89 excluded points passed the integer tensor
  identity check with the repository's transpose convention.
- A separate full replay of the integer-minor screen (`p=0`, exact characteristic-zero
  arithmetic) also gave 14,149 rank/profile passes with identical pass sets,
  and exactly `[2445, 5969]` anchor exclusions.
- `tools/verify_alphatensor_witnesses.py` checked the 87 existing versioned
  rank-exclusion witness batches against the actual NPZ and their nonzero
  determinants modulo 3. All 87 passed.
- Independently recomputed the exact useful-anchor lists using integer minors
  (`p=0`) and minors modulo 3 (`p=3`), not the generator's predicted witnesses:

| Index | Q (p=0) | F3 (p=3) |
|---|---|---|
| 2445 | `[1, 25]` | `[1, 25]` |
| 5969 | `[3]` | `[3]` |

The generated files are intentionally not duplicated in this patch: their
contents match the existing pinned manifest byte for byte. The CI regenerates
and checks the real source before building the Lean catalogue.

## Reproduce (repository root)

```sh
NPZ=/absolute/path/to/alphatensor_14236_factorizations.npz
python3 -I lean/tools/catalogue/gen_catalogue_lean.py "$NPZ" lean
python3 -I lean/tools/catalogue/verify_source_binding.py "$NPZ" lean
(cd lean && sha256sum -c Brent/Catalogue/GENERATED_SHA256.txt)
python3 -I tools/verify_alphatensor_witnesses.py "$NPZ" lean/Brent/Generated/AlphaTensorBound*.lean
```

The source hash and byte-to-coordinate binding are external reproducibility
checks, not theorems about NPZ parsing or SHA-256 in Lean. Mathematical
certificate soundness, per-point checks and exact anchor counts have Lean
source declarations; their compilation and kernel replay have not been
performed in this audit.
