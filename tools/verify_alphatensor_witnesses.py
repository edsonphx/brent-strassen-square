#!/usr/bin/env python3
"""Independent check of the generated Lean witness batches against the catalogue (item F18).

Usage:
    python3 -I tools/verify_alphatensor_witnesses.py CATALOGUE.npz lean/Brent/Generated/AlphaTensorBound*.lean

This does not import the generator. It parses the Lean source of the batches, and for each
certificate checks against the catalogue:
* each recorded entry equals the catalogue entry under the repository convention
  (u = U, v = V, w = W^T; summand (i, j) = catalogue row 7 i + j; vertex (a, b) = index 2 a + b);
* the `BoundW.check` conditions: 14 distinct summands with 2x2 determinants nonzero mod 3, or
  2 distinct summands with 3x3 determinants nonzero mod 3;
* the catalogue indices are distinct, and there are 87 of them.
"""
import re
import sys

import numpy as np

F = np.load(sys.argv[1], allow_pickle=False)["factorizations"].astype(np.int64)
M = F.reshape(len(F), 49, 3, 4, 4).copy()
M[:, :, 2] = np.swapaxes(M[:, :, 2], -1, -2)

MINOR = re.compile(
    r"⟨\(\((\d) : Fin 7\), \((\d) : Fin 7\)\), \.([uvw]), !\[(.*?)\], !\[(.*?)\], !!\[(.*?)\]⟩")
VERT = re.compile(r"\(\((\d) : Fin 2\), \((\d) : Fin 2\)\)")
ITEM = re.compile(r"\((\d+), \.(many|pair)")


def det(a):
    a = np.array(a, dtype=object)
    if len(a) == 2:
        return a[0][0] * a[1][1] - a[0][1] * a[1][0]
    return sum((-1) ** j * a[0][j] * det(np.delete(np.delete(a, 0, 0), j, 1).tolist())
               for j in range(3))


seen = []
for path in sys.argv[2:]:
    src = open(path).read()
    starts = [m.start() for m in ITEM.finditer(src)] + [len(src)]
    for (m, end) in zip(ITEM.finditer(src), starts[1:]):
        idx, kind = int(m.group(1)), m.group(2)
        minors = MINOR.findall(src[m.start():end])
        assert len(minors) == (14 if kind == "many" else 2), (idx, kind, len(minors))
        n = 2 if kind == "many" else 3
        summands = []
        for i, j, mode, rows, cols, ent in minors:
            s = 7 * int(i) + int(j)
            q = "uvw".index(mode)
            rows = [2 * int(a) + int(b) for a, b in VERT.findall(rows)]
            cols = [2 * int(a) + int(b) for a, b in VERT.findall(cols)]
            e = [[int(x) for x in r.split(",")] for r in ent.split(";")]
            assert len(rows) == len(cols) == len(e) == n
            assert (M[idx, s, q][np.ix_(rows, cols)] == np.array(e)).all(), (idx, s, q)
            assert det(e) % 3 != 0, (idx, s, q)
            summands.append(s)
        assert len(set(summands)) == len(summands), idx
        seen.append(idx)

assert len(seen) == len(set(seen)) == 87, len(seen)
print(f"OK: {len(seen)} certificates match the catalogue and pass the check")
