#!/usr/bin/env python3
"""Exact verifier for the ordered recursive Strassen square. Requires NumPy."""
import argparse
from hashlib import sha256
from itertools import product
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
BASE = np.array([
    [[1,0,0,1],[0,0,1,1],[1,0,0,0],[0,0,0,1],[1,1,0,0],[-1,0,1,0],[0,1,0,-1]],
    [[1,0,0,1],[1,0,0,0],[0,1,0,-1],[-1,0,1,0],[0,0,0,1],[1,1,0,0],[0,0,1,1]],
    [[1,0,0,1],[0,0,1,-1],[0,1,0,1],[1,0,1,0],[-1,1,0,0],[0,0,0,1],[1,0,0,0]],
], dtype=np.int32).transpose(1, 0, 2)


def require(test, message):
    if not test:
        raise ValueError(message)


def verify_hashes():
    for line in (ROOT / "SHA256SUMS.txt").read_text().splitlines():
        expected, filename = line.split("  ", 1)
        require(sha256((ROOT / filename).read_bytes()).hexdigest() == expected,
                f"SHA-256 mismatch for {filename}")


def tensor(terms):
    return np.einsum("ri,rj,rk->ijk", *terms.transpose(1, 0, 2), dtype=np.int32)


def target(n):
    out = np.zeros((n*n,) * 3, dtype=np.int32)
    for i, j, k in product(range(n), repeat=3):
        out[i*n+k, k*n+j, i*n+j] = 1
    return out


def shuffled_product(a, b):
    return np.einsum("raij,sakl->rsaikjl", a.reshape(7, 3, 2, 2),
                     b.reshape(7, 3, 2, 2)).reshape(49, 3, 16)


def symmetry_directions(terms, scales):
    """Differentiate term scalings and the cyclic input/output base changes."""
    count, _, width = terms.shape
    n = int(width**0.5)
    if scales:
        for s, leg in product(range(count), (1, 2)):
            delta = np.zeros_like(terms)
            delta[s, 0] = terms[s, 0]
            delta[s, leg] = -terms[s, leg]
            yield delta
    a, b, c = terms.transpose(1, 0, 2).reshape(3, count, n, n)
    zero = np.zeros_like(a)
    for group, i, j in product(range(3), range(n), range(n)):
        e = np.zeros((n, n), dtype=np.int32)
        e[i, j] = 1
        if group == 0:
            delta = (e.T @ a, zero, -e @ c)
        elif group == 1:
            delta = (-a @ e.T, e.T @ b, zero)
        else:
            delta = (zero, -b @ e.T, c @ e)
        yield np.stack(delta, axis=1).reshape(terms.shape)


def block_directions(orientation):
    for s in range(7):
        block = np.zeros_like(BASE)
        block[s] = BASE[s]
        for delta in symmetry_directions(BASE, scales=False):
            yield shuffled_product(block, delta) if orientation == 0 else shuffled_product(delta, block)


def generators(terms):
    return [np.asarray(list(symmetry_directions(terms, True))),
            np.asarray(list(block_directions(0))), np.asarray(list(block_directions(1)))]


def jacobian_rows(terms):
    # Rows are transposed Jacobian columns. A single coordinate shift is exact.
    columns = []
    for term in terms:
        original = tensor(term[None])
        for mode, coordinate in product(range(3), range(16)):
            changed = term.copy()
            changed[mode, coordinate] += 1
            columns.append((tensor(changed[None]) - original).ravel())
    return np.array(columns, dtype=np.int16)


def pack(row):
    row = np.asarray(row) % 3
    return tuple(int.from_bytes(np.packbits(row == trit, bitorder="little").tobytes(), "little")
                 for trit in (1, 2))


class Rank:
    def __init__(self):
        self.pivots = {}

    def insert(self, row):
        a, b = pack(row)
        while a | b:
            support = a | b
            leading = support & -support
            if leading not in self.pivots:
                self.pivots[leading] = (a, b) if a & leading else (b, a)
                return True
            c, d = self.pivots[leading]
            if a & leading:
                c, d = d, c
            left_zero, right_zero = ~support, ~(c | d)
            a, b = ((a & right_zero) | (left_zero & c) | (b & d),
                    (b & right_zero) | (left_zero & d) | (a & c))
        return False

    def extend(self, rows):
        return [i for i, row in enumerate(rows) if self.insert(row)]

    def __len__(self):
        return len(self.pivots)


def extend_unit_echelon(rows, pivots):
    """Reduce integer rows by row additions and sign changes only."""
    for vector in rows:
        row = {int(i): int(vector[i]) for i in np.flatnonzero(vector)}
        while row:
            leading = min(row)
            coefficient = row[leading]
            pivot = pivots.get(leading)
            if pivot is None:
                require(abs(coefficient) == 1, "nonunit pivot in exact rank check")
                pivots[leading] = {i: coefficient * value for i, value in row.items()}
                break
            for i, value in pivot.items():
                updated = row.get(i, 0) - coefficient * value
                if updated:
                    row[i] = updated
                else:
                    row.pop(i, None)
    return len(pivots)


def select_bases(families):
    rank = Rank()
    return [family[rank.extend(family.reshape(len(family), -1))] for family in families]


def mixed_row(terms, u, v):
    common = np.any(u, axis=(1, 2)) & np.any(v, axis=(1, 2))
    s, u, v = terms[common], u[common], v[common]
    polarized = tensor(s+u+v)-tensor(s+u-v)-tensor(s-u+v)+tensor(s-u-v)
    require(not np.any(polarized % 4), "signed polarization is not divisible by four")
    return (polarized // 4).ravel()


def check_csv(path, shape, mixed=False):
    out = np.zeros(shape, dtype=np.int32)
    rows = np.loadtxt(path, delimiter=",", skiprows=1, ndmin=2, dtype=np.int32)
    i, j = rows[:, 0], rows[:, 1]
    if mixed:
        require(np.all((0 <= j) & (j < 54) & (0 <= rows[:, 2]) & (rows[:, 2] < 54)),
                "invalid mixed monomial")
        j = 54*j + rows[:, 2]
    values = rows[:, -1]
    require(np.all((0 <= i) & (i < shape[0]) & (0 <= j) & (j < shape[1]))
            and np.all(np.isin(values, [1, 2]))
            and len(np.unique(i * shape[1] + j)) == len(rows), f"invalid entries in {path.name}")
    out[i, j] = values
    return out


def verify_full_quadrics(terms, basis, functionals, quadrics):
    # Accumulate each ordered pair of tangent directions before polarization.
    count = len(basis)
    ordered = np.zeros((54, count, count), dtype=np.int32)
    tensors = functionals.reshape(54, 16, 16, 16)
    for s, term in enumerate(terms):
        for a, b, c in ((0, 1, 2), (0, 2, 1), (1, 2, 0)):
            va, vb = basis[:, s, a], basis[:, s, b]
            ia, ib = np.flatnonzero(va.any(axis=1)), np.flatnonzero(vb.any(axis=1))
            permuted = tensors.transpose(0, a+1, b+1, c+1)
            core = np.einsum("qijk,k->qij", permuted, term[c])
            contribution = va[ia] @ core @ vb[ib].T
            ordered[:, ia[:, None], ib] += contribution
    i, j = np.triu_indices(count, k=1)
    off_diagonal = (ordered[:, i, j]+ordered[:, j, i]) % 3
    in_mixed_block = (143 <= i) & (i < 197) & (197 <= j)
    require(np.array_equal(off_diagonal[:,in_mixed_block], quadrics), "full mixed block mismatch")
    require(not np.any(off_diagonal[:,~in_mixed_block]) and
            not np.any(np.diagonal(ordered, axis1=1, axis2=2) % 3), "unexpected pure/common coefficient")
    checked = count*(count+1)//2 - int(in_mixed_block.sum())
    require(checked == 28710, "wrong non-mixed monomial count")
    print(f"Full quadratic check: {checked} non-mixed monomials vanish in all 54 forms")


def unimodular_pair(n, rng):
    matrix, inverse = np.eye(n, dtype=np.int64), np.eye(n, dtype=np.int64)
    for _ in range(7):
        i, j = rng.choice(n, size=2, replace=False)
        sign = int(rng.choice([-1, 1]))
        matrix[i] += sign*matrix[j]
        inverse[:, j] -= sign*inverse[:, i]
    require(np.array_equal(matrix @ inverse, np.eye(n, dtype=np.int64)), "bad inverse")
    return matrix, inverse


def finite_move(terms, rng):
    n = int(terms.shape[2]**0.5)
    return change_basis(terms, *(unimodular_pair(n, rng) for _ in range(3)))


def change_basis(terms, p_pair, q_pair, r_pair):
    n = int(terms.shape[2]**0.5)
    p, pi = p_pair
    q, qi = q_pair
    r, ri = r_pair
    a, b, c = terms.transpose(1, 0, 2).reshape(3, len(terms), n, n)
    moved = np.stack((p.T @ a @ qi.T, q.T @ b @ ri.T, pi @ c @ r), axis=1)
    return moved.reshape(terms.shape)


def recursive_move(blocks, side):
    grid = np.empty((7, 7, 3, 16), dtype=np.int64)
    for index, changed in enumerate(blocks):
        if side == 0:
            grid[index] = shuffled_product(BASE, changed).reshape(grid.shape)[index]
        else:
            grid[:, index] = shuffled_product(changed, BASE).reshape(grid.shape)[:, index]
    return grid.reshape(49, 3, 16)


def check_integer_point(terms):
    bound = 49
    for mode in range(3):
        bound *= int(np.max(np.abs(terms[:, mode])))
    require(bound < np.iinfo(np.int64).max, "integer contraction could overflow")
    actual = np.einsum("ri,rj,rk->ijk", *terms.transpose(1, 0, 2), dtype=np.int64)
    require(np.array_equal(actual, target(4)), "unimodular family point fails the Brent identity")


def verify_families():
    rng = np.random.default_rng(8101)
    identity = np.eye(2, dtype=np.int64)
    e12 = np.array([[0, 1], [0, 0]], dtype=np.int64)
    unchanged = (identity, identity)
    upper = (identity + e12, identity - e12)
    lower = (identity + e12.T, identity - e12.T)
    blocks = [BASE] * 7
    blocks[4] = change_basis(BASE, upper, unchanged, lower)
    blocks[5] = change_basis(BASE, lower, unchanged, upper)
    for side in (0, 1):
        witness = recursive_move(blocks, side)
        check_integer_point(witness)
        rank = Rank()
        rank.extend(jacobian_rows((witness % 3).astype(np.int32)))
        require(len(rank) == 2155, "explicit shear witness has wrong Jacobian rank")
        for _ in range(20):
            sample = recursive_move([finite_move(BASE, rng) for _ in range(7)], side)
            check_integer_point(finite_move(sample, rng))
    print("Two explicit shear witnesses: integer identities and Jacobian ranks 2155")
    print("40 additional exact integer deformations across both recursive families")


def verify(full=False):
    verify_hashes()
    with np.load(DATA / "strassen_square_factors.npz", allow_pickle=False) as source:
        terms = np.stack([source[k] for k in ("U", "V", "W")], axis=1).astype(np.int32)
    require(np.array_equal(terms, shuffled_product(BASE, BASE)), "unexpected recursive factors")
    require(np.array_equal(tensor(BASE), target(2)) and np.array_equal(tensor(terms), target(4)),
            "Brent identity failed over the integers")
    print("Integer Brent identities: 4096/4096")

    jacobian = jacobian_rows(terms)
    rank = Rank()
    rank.extend(jacobian)
    require(len(rank) == 2101, "wrong Jacobian rank")
    families = generators(terms)
    gauge, left, right = select_bases(families)
    require((len(gauge), len(left), len(right)) == (143, 54, 54), "wrong tangent split")
    other = Rank()
    require(len(other.extend(gauge.reshape(143, -1))) == 143
            and len(other.extend(families[2].reshape(84, -1))) == 54, "wrong outer-family dimension")
    with np.load(DATA / "tangent_bases.npz", allow_pickle=False) as stored:
        for key, basis in zip(("G", "X", "Y"), (gauge, left, right)):
            require(np.array_equal(stored[key], basis), f"frozen basis {key} disagrees")
    for family in families:
        for direction in family.reshape(len(family), -1):
            support = np.flatnonzero(direction)
            require(not np.any(direction[support] @ jacobian[support]), "nonzero integral derivative")
    print("Jacobian rank: 2101; kernel: 251; orbit: 143; transverse: 54 + 54")

    mixed = np.array([mixed_row(terms, u, v) for u in left for v in right], dtype=np.int16)
    rank.extend(mixed)
    require(len(rank) == 2749, "wrong augmented rank modulo three")
    integer_pivots = {}
    rational_jacobian_rank = extend_unit_echelon(jacobian, integer_pivots)
    rational_augmented_rank = extend_unit_echelon(mixed, integer_pivots)
    require(rational_jacobian_rank == 2101, "wrong exact Jacobian rank")
    require(rational_augmented_rank == 2749, "wrong exact augmented rank")
    print("Augmented rank: 2749 over Q and GF(3); exact elimination uses only unit pivots")

    with np.load(DATA / "regular_sequence_certificate.npz", allow_pickle=False) as cert:
        functionals = cert["lambda_mod3"].astype(np.int32)
        quadrics = cert["quadrics_mod3"].astype(np.int32)
        pairs = cert["monomial_matching"].astype(np.int32)
        leading = cert["selected_pivots"]
    require(functionals.shape == (54, 4096) and quadrics.shape == (54, 2916)
            and pairs.shape == (54, 2) and leading.shape == (54,), "invalid certificate shape")
    require(np.array_equal(functionals, check_csv(DATA / "54_functionals_sparse.csv", (54, 4096)))
            and np.array_equal(quadrics, check_csv(DATA / "54_polynomials_sparse.csv",
                                                  (54, 2916), mixed=True)), "CSV and NPZ differ")
    require(np.array_equal(54*pairs[:, 0]+pairs[:, 1], leading)
            and np.array_equal(np.sort(pairs, axis=0), np.repeat(np.arange(54)[:, None], 2, axis=1)),
            "matching is not perfect")
    for functional, expected, pivot in zip(functionals, quadrics, leading):
        support = np.flatnonzero(functional)
        coeff = functional[support]
        require(not np.any((jacobian[:, support] @ coeff) % 3), "functional does not kill J")
        actual = (mixed[:, support] @ coeff) % 3
        require(np.array_equal(actual, expected), "quadratic coefficient mismatch")
        require(actual[pivot] == 1 and not np.any(actual[:pivot]), "invalid leading monomial")
    obstruction_rank = rational_augmented_rank - rational_jacobian_rank
    require(251*252//2 - obstruction_rank == 30978, "Hilbert coefficient mismatch")
    print("54 literal functionals and coprime leading monomials checked; mixed rank: 648")
    if full:
        verify_full_quadrics(terms, np.concatenate((gauge, left, right)), functionals, quadrics)
        verify_families()
    print("VERIFIED: local_dim = 197")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="also check all quadratic coefficients and finite family samples")
    verify(parser.parse_args().full)
