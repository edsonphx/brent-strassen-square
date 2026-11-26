#!/usr/bin/env python3
"""AlphaTensor 4x4 census (paper §7): exclusion witnesses and Lean data (item F18).

Usage:
    python3 -I tools/alphatensor_census.py CATALOGUE.npz OUTDIR

CATALOGUE.npz is DeepMind's `alphatensor_14236_factorizations.npz` (array `factorizations`,
shape (14236, 49, 3, 16), int). It is loaded with allow_pickle=False.

Conventions (all indices zero-based):
* The catalogue stores each factor as a row-major 4x4 matrix, in the *cyclic* convention:
  sum_r u_r (x) v_r (x) w_r = sum T[4i+k, 4k+j, 4j+i]. The repository uses the *direct*
  convention `matrixMultiplicationEntry a b c = [a.2 = b.1 ∧ a.1 = c.1 ∧ b.2 = c.2]`, i.e.
  T[4i+k, 4k+j, 4i+j]. So the repository point has u = U, v = V, w = W^T. This script checks that
  every point it uses is a solution of the direct Brent equations.
* Catalogue summand n (0..48) is the repository summand (n // 7, n % 7) : Fin 7 x Fin 7.
* Matrix row/column index r (0..3) is the repository vertex (r // 2, r % 2) : Fin 2 x Fin 2.
* Ranks are taken over Q and over F3. A minor that is nonzero mod 3 is nonzero over every
  field of characteristic 0 or 3, so every witness below works in both characteristics.

Tests (paper §7):
* rank bound: at most 13 summands with some mode of rank > 1, and at most 1 with rank > 2.
  A violation is witnessed by 14 distinct summands with a nonzero 2x2 minor each ("many"), or
  by 2 distinct summands with a nonzero 3x3 minor each ("pair").
* anchor test (only for points with the exact profile 36(1,1,1) + 12(2,2,2) + 1(4,4,4)): see
  `anchor_ok`. A violation is witnessed by the exact profile and the list of incompatible
  (rank-1, rank-2) pairs, each with a nonzero 3x3 minor of a stacked matrix.

Outputs: OUTDIR/alphatensor_witnesses.json and OUTDIR/AlphaTensorBound{0..5}.lean.
"""
import hashlib
import itertools
import json
import sys

import numpy as np

P = 3


def load(path):
    raw = open(path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    F = np.load(path, allow_pickle=False)["factorizations"].astype(np.int64)
    assert F.shape == (14236, 49, 3, 16), F.shape
    M = F.reshape(len(F), 49, 3, 4, 4).copy()
    M[:, :, 2] = np.swapaxes(M[:, :, 2], -1, -2)  # cyclic -> direct: w := W^T
    return M, sha


def direct_target():
    T = np.zeros((16, 16, 16), np.int64)
    for i, k, j in itertools.product(range(4), repeat=3):
        T[4 * i + k, 4 * k + j, 4 * i + j] = 1
    return T


TARGET = direct_target()


def solves(m):
    X = np.einsum("ri,rj,rk->ijk", m[:, 0].reshape(49, 16), m[:, 1].reshape(49, 16),
                  m[:, 2].reshape(49, 16))
    return bool((X == TARGET).all())


def det(a):
    return int(round(np.linalg.det(a))) if a.shape[0] > 3 else _det_exact(a)


def _det_exact(a):
    if a.shape[0] == 1:
        return int(a[0, 0])
    if a.shape[0] == 2:
        return int(a[0, 0] * a[1, 1] - a[0, 1] * a[1, 0])
    return int(a[0, 0] * (a[1, 1] * a[2, 2] - a[1, 2] * a[2, 1])
               - a[0, 1] * (a[1, 0] * a[2, 2] - a[1, 2] * a[2, 0])
               + a[0, 2] * (a[1, 0] * a[2, 1] - a[1, 1] * a[2, 0]))


def det4(a):
    return sum((-1) ** j * int(a[0, j]) * _det_exact(np.delete(a[1:], j, axis=1)) for j in range(4))


def nz(x, p):
    return x != 0 if p == 0 else x % p != 0


def minors(a, n):
    for rows in itertools.combinations(range(4), n):
        for cols in itertools.combinations(range(4), n):
            yield rows, cols, a[np.ix_(rows, cols)]


def rank(a, p):
    if nz(det4(a), p):
        return 4
    for n in (3, 2, 1):
        if any(nz(_det_exact(sub), p) for _, _, sub in minors(a, n)):
            return n
    return 0


def first_minor(m, s, n, p):
    """A nonzero n x n minor of some mode of summand s, or None."""
    for mode in range(3):
        for rows, cols, sub in minors(m[s, mode], n):
            d = _det_exact(sub)
            if nz(d, p):
                return {"summand": s, "mode": mode, "rows": list(rows), "cols": list(cols),
                        "entries": sub.astype(int).tolist(), "det": d}
    return None


def bound_witness(m, p):
    R = np.array([[rank(m[s, q], p) for q in range(3)] for s in range(49)])
    mx = R.max(1)
    if (mx > 2).sum() > 1:
        ss = [int(s) for s in np.flatnonzero(mx > 2)[:2]]
        return {"kind": "pair", "minors": [first_minor(m, s, 3, p) for s in ss]}
    if (mx > 1).sum() > 13:
        ss = [int(s) for s in np.flatnonzero(mx > 1)[:14]]
        return {"kind": "many", "minors": [first_minor(m, s, 2, p) for s in ss]}
    return None


def rowspace_contains(big, small, p):
    """rank [big; small] == rank big (= 2), via vanishing 3x3 minors of [two rows of big; v]."""
    k = [i for i in range(4) if any(nz(int(x), p) for x in small[i])][0]
    v = small[k]
    for i, j in itertools.combinations(range(4), 2):
        st = np.stack([big[i], big[j], v])
        for cols in itertools.combinations(range(4), 3):
            d = _det_exact(st[:, cols])
            if nz(d, p):
                return False, {"rows_of_anchor": [i, j], "row_of_one": k, "cols": list(cols),
                               "det": d}
    return True, None


def compatible(m, o, a, p):
    for q in range(3):
        for tr in (False, True):
            A = m[a, q].T if tr else m[a, q]
            O = m[o, q].T if tr else m[o, q]
            ok, w = rowspace_contains(A, O, p)
            if not ok:
                return False, dict(w, mode=q, transposed=tr)
    return True, None


def anchor_fast(m, prof, p):
    """Vectorized version of `anchor_check(...)["ok"]`, used for screening only."""
    def d2(a, b, c, d):
        return a * d - b * c

    def d3(x):
        return (x[..., 0, 0] * d2(x[..., 1, 1], x[..., 1, 2], x[..., 2, 1], x[..., 2, 2])
                - x[..., 0, 1] * d2(x[..., 1, 0], x[..., 1, 2], x[..., 2, 0], x[..., 2, 2])
                + x[..., 0, 2] * d2(x[..., 1, 0], x[..., 1, 1], x[..., 2, 0], x[..., 2, 1]))

    def contains(big, small):
        idx = nz(small, p).any(axis=-1).argmax(axis=-1)
        v = np.take_along_axis(small, idx[..., None, None], axis=-2)[..., 0, :]
        ok = np.ones(big.shape[:-2], bool)
        for i, j in itertools.combinations(range(4), 2):
            st = np.stack([big[..., i, :], big[..., j, :], v], axis=-2)
            for cols in itertools.combinations(range(4), 3):
                ok &= ~nz(d3(st[..., list(cols)]), p)
        return ok

    ones, twos = m[prof == 1], m[prof == 2]
    A, O = np.broadcast_arrays(twos[None], ones[:, None])
    comp = (contains(A, O) & contains(A.swapaxes(-1, -2), O.swapaxes(-1, -2))).all(axis=-1)
    useful = comp.sum(0) >= 6
    return bool(useful.sum() >= 6 and comp[:, useful].any(1).all())


def anchor_check(m, p):
    R = np.array([[rank(m[s, q], p) for q in range(3)] for s in range(49)])
    prof = R[:, 0]
    if not ((R == R[:, :1]).all() and (prof == 1).sum() == 36 and (prof == 2).sum() == 12
            and (prof == 4).sum() == 1):
        return None
    ones = [int(s) for s in np.flatnonzero(prof == 1)]
    twos = [int(s) for s in np.flatnonzero(prof == 2)]
    comp, why = {}, {}
    for o in ones:
        for a in twos:
            comp[o, a], why[o, a] = compatible(m, o, a, p)
    useful = [a for a in twos if sum(comp[o, a] for o in ones) >= 6]
    ok = len(useful) >= 6 and all(any(comp[o, a] for a in useful) for o in ones)
    return {"ok": ok, "ones": ones, "twos": twos, "useful": useful,
            "compatible_pairs": [[o, a] for (o, a), c in comp.items() if c],
            "incompatible_pairs": [{"one": o, "anchor": a, "witness": why[o, a]}
                                   for (o, a), c in comp.items() if not c]}


# ---------------------------------------------------------------- Lean output

def vx(r):
    return f"(({r // 2} : Fin 2), ({r % 2} : Fin 2))"


def lean_minor(w):
    n = len(w["rows"])
    s = w["summand"]
    mode = ".u .v .w".split()[w["mode"]]
    rows = ", ".join(vx(r) for r in w["rows"])
    cols = ", ".join(vx(c) for c in w["cols"])
    ent = "; ".join(", ".join(str(x) for x in row) for row in w["entries"])
    return (f"⟨(({s // 7} : Fin 7), ({s % 7} : Fin 7)), {mode}, ![{rows}], ![{cols}], "
            f"!![{ent}]⟩")


def lean_bound(idx, w):
    if w["kind"] == "pair":
        a, b = (lean_minor(x) for x in w["minors"])
        return f"  ({idx}, .pair\n    {a}\n    {b})"
    body = ",\n    ".join(lean_minor(x) for x in w["minors"])
    return f"  ({idx}, .many ![\n    {body}])"


def write_lean(outdir, bound, batches=6):
    items = sorted(bound.items())
    size = (len(items) + batches - 1) // batches
    for b in range(batches):
        chunk = items[b * size:(b + 1) * size]
        lines = ",\n".join(lean_bound(i, w) for i, w in chunk)
        open(f"{outdir}/AlphaTensorBound{b}.lean", "w").write(f"""import Brent.Census.Witness

/-! Generated by `tools/alphatensor_census.py`. Rank-bound witnesses, batch {b} of {batches}.
Catalogue indices are zero-based. Do not edit by hand. -/

namespace Brent.Census.Generated

set_option maxRecDepth 100000

/-- Rank-bound exclusion witnesses, batch {b}. -/
def boundBatch{b} : List (ℕ × BoundW) := [
{lines}]

set_option maxHeartbeats 4000000 in
theorem boundBatch{b}_check : (boundBatch{b}.all fun x => x.2.check) = true := by decide +kernel

end Brent.Census.Generated
""")


def screen(M, p):
    """Vectorized rank profile of every catalogue point (as in the independent census)."""
    def d2(a, b, c, d):
        return a * d - b * c

    def d3(m):
        return (m[..., 0, 0] * d2(m[..., 1, 1], m[..., 1, 2], m[..., 2, 1], m[..., 2, 2])
                - m[..., 0, 1] * d2(m[..., 1, 0], m[..., 1, 2], m[..., 2, 0], m[..., 2, 2])
                + m[..., 0, 2] * d2(m[..., 1, 0], m[..., 1, 1], m[..., 2, 0], m[..., 2, 1]))

    def d4(m):
        return sum((-1) ** j * m[..., 0, j] * d3(np.delete(m[..., 1:, :], j, axis=-1))
                   for j in range(4))

    r = np.zeros(M.shape[:-2], np.int64)
    r[nz(M, p).any(axis=(-1, -2))] = 1
    for k in (2, 3):
        hit = np.zeros(M.shape[:-2], bool)
        for rows in itertools.combinations(range(4), k):
            for cols in itertools.combinations(range(4), k):
                sub = M[..., list(rows), :][..., list(cols)]
                dd = d2(sub[..., 0, 0], sub[..., 0, 1], sub[..., 1, 0], sub[..., 1, 1]) \
                    if k == 2 else d3(sub)
                hit |= nz(dd, p)
        r[hit] = k
    r[nz(d4(M), p)] = 4
    mx = r.max(2)
    bound_ok = ((mx > 1).sum(1) <= 13) & ((mx > 2).sum(1) <= 1)
    prof = r[:, :, 0]
    exact = ((r == r[:, :, :1]).all(axis=(1, 2)) & ((prof == 1).sum(1) == 36)
             & ((prof == 2).sum(1) == 12) & ((prof == 4).sum(1) == 1))
    return bound_ok, exact, prof


def main():
    M, sha = load(sys.argv[1])
    outdir = sys.argv[2]
    bound_ok, exact, prof = screen(M, P)
    print(f"passing the rank bounds: {int(bound_ok.sum())}; exact profile: {int(exact.sum())}")
    bound, anchor = {}, {}
    for n in np.flatnonzero(~bound_ok):
        bound[int(n)] = bound_witness(M[n], P)
        assert bound[int(n)] is not None
    for n in np.flatnonzero(exact):
        if not anchor_fast(M[n], prof[n], P):
            a = anchor_check(M[n], P)
            assert not a["ok"]
            anchor[int(n)] = a
    used = sorted(bound) + sorted(anchor)
    assert all(solves(M[n]) for n in used), "convention check failed"
    # The same exclusions over Q (sanity: the mod-3 witnesses are nonzero integers).
    for n, w in bound.items():
        assert all(x["det"] != 0 for x in w["minors"])
    print(f"bound-excluded: {len(bound)}; anchor-excluded: {sorted(anchor)}; total {len(used)}")
    json.dump({"catalogue_sha256": sha, "prime": P,
               "conventions": "direct; u=U, v=V, w=W^T; summand n=(n//7,n%7); index r=(r//2,r%2)",
               "bound": {str(k): v for k, v in sorted(bound.items())},
               "anchor": {str(k): v for k, v in sorted(anchor.items())}},
              open(f"{outdir}/alphatensor_witnesses.json", "w"), indent=1)
    write_lean(outdir, bound)


if __name__ == "__main__":
    main()
