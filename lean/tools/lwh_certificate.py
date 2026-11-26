"""Usage: python3 lwh_certificate.py path/to/s526.ipynb OUTDIR
(s526.ipynb: Section 5.2.2 folder of https://github.com/Xinli-zjut/Substitution)

Build all certificate data for Brent.LWH from Li-Wang-Hu's s526 table.

Outputs (JSON, in the output directory):
  lwh_point.json  - 2352 integers, indexed by the repo's squareVariableNumber (48s + 16m + 4r + c),
                    direct convention (u = U, v = V, w = W^T).
  lwh_trace.json  - mod-3 elimination trace in the format of tools/generate_smooth_trace.py
                    (keys C, E, piv, reds, ops, corrs), plus the radix bit bound needed.
  lwh_kernel.json - 197 integer kernel vectors and their free-variable minor data.
  lwh_orbit.json  - orbit generator choice: 143 kept generators, 143 coordinates, 3 relations.
Every property the Lean checks rely on is asserted here with exact integer arithmetic.
"""
import sys, json, re, itertools
from fractions import Fraction
import numpy as np
import flint

nb_path, out_dir = sys.argv[1], sys.argv[2]
nb = json.load(open(nb_path))
src = "".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code")
mats = {}
for name, idx, body in re.findall(r"^\s*([UVW])(\d+)\s*=\s*Rational\{Int\}\[(.*?)\]", src, re.S | re.M):
    rows = [r.split() for r in body.strip().splitlines() if r.strip()]
    mats[(name, int(idx))] = [[Fraction(x) for x in r] for r in rows]
assert len(mats) == 147
def integral_factors(name):
    factors = [mats[(name, k)] for k in range(1, 50)]
    if any(len(matrix) != 4 or any(len(row) != 4 for row in matrix) for matrix in factors):
        raise ValueError(f"{name}: expected 49 matrices of shape 4 × 4")
    if any(x.denominator != 1 for matrix in factors for row in matrix for x in row):
        raise ValueError(f"{name}: the certificate requires integral source entries")
    return np.array(factors, dtype=np.int64)


U, V, W = (integral_factors(name) for name in "UVW")
P = np.stack([U.reshape(49, 16), V.reshape(49, 16), W.transpose(0, 2, 1).reshape(49, 16)], 1)  # direct

# --- Brent identity in the repo's convention: entry(a,b,c) = [a.2=b.1, a.1=c.1, b.2=c.2]
T = np.zeros((16, 16, 16), np.int64)
for i, k, j in itertools.product(range(4), repeat=3):
    T[4*i+k, 4*k+j, 4*i+j] = 1
assert (np.einsum('si,sj,sk->ijk', P[:, 0], P[:, 1], P[:, 2]) == T).all()
point = P.reshape(-1)
assert point.size == 2352

def var(s, m, a): return 48*s + 16*m + a
def eqn(a, b, c): return 256*a + 16*b + c

# --- Jacobian columns (dense, exact): column x = d entry / d point[x]
J = np.zeros((4096, 2352), np.int64)
for s in range(49):
    for a in range(16):
        J[:, var(s, 0, a)] = np.einsum('i,j,k->ijk', np.eye(16, dtype=np.int64)[a], P[s, 1], P[s, 2]).ravel()
        J[:, var(s, 1, a)] = np.einsum('i,j,k->ijk', P[s, 0], np.eye(16, dtype=np.int64)[a], P[s, 2]).ravel()
        J[:, var(s, 2, a)] = np.einsum('i,j,k->ijk', P[s, 0], P[s, 1], np.eye(16, dtype=np.int64)[a]).ravel()

bal = lambda x: ((x + 1) % 3) - 1

# --- mod-3 elimination trace with exact integer bookkeeping (columns in increasing order)
reds, ops_all, corrs, C, pivcoord = [], [], [], [], []
pivrow = {}
for x in range(2352):
    col = J[:, x].copy(); cur = col.copy(); ops = []
    while True:
        nz = np.flatnonzero(cur % 3)
        if len(nz) == 0: break
        c = int(nz[0])
        if c in pivrow:
            j = pivrow[c]; a = int(bal(cur[c] * reds[j][c]))
            cur = cur - a * reds[j]; ops.append((j, a))
        else:
            break
    if len(np.flatnonzero(cur % 3)) == 0:
        continue  # dependent column modulo 3
    red = bal(cur); corr = (cur - red) // 3
    assert ((cur - red) % 3 == 0).all()
    i = len(reds)
    pivrow[c] = i; pivcoord.append(c)
    reds.append(red); ops_all.append(ops); corrs.append(corr); C.append(x)
n = len(reds)
print("rank mod 3:", n)
assert n == 2155

# exact identity reduced_i = (col - 3 corr) - sum a * reduced_j, and pivot shape
maxb, maxlen = 0, 0
for i in range(n):
    orig = J[:, C[i]] - 3 * corrs[i]
    acc = orig.copy()
    for j, a in ops_all[i]:
        assert j < i; acc -= a * reds[j]
    assert (acc == reds[i]).all()
    nz = np.flatnonzero(reds[i]); assert nz[0] == pivcoord[i] and abs(reds[i][pivcoord[i]]) == 1
    b = int(np.abs(orig).sum() + np.abs(reds[i]).sum() + sum(abs(a) * int(np.abs(reds[j]).sum()) for j, a in ops_all[i]))
    maxb = max(maxb, b)
    maxlen = max(maxlen, len(nz), int(np.count_nonzero(corrs[i])), len(ops_all[i]))
    assert np.abs(reds[i]).max() < 128 and (np.abs(corrs[i]).max() if corrs[i].any() else 0) < 128
bits = max(14, int(maxb).bit_length() + 1)
print("max radix bound", maxb, "-> bits", bits, "| max row/ops/corr length", maxlen)
assert maxlen <= 1024
E = sorted(pivcoord)
trace = {"C": C, "E": E, "piv": {str(c): pivrow[c] for c in E},
         "reds": [[(int(k), int(r[k])) for k in np.flatnonzero(r)] for r in reds],
         "ops": [[(int(j), int(a)) for j, a in o] for o in ops_all],
         "corrs": [[(int(k), int(r[k])) for k in np.flatnonzero(r)] for r in corrs],
         "bits": bits}

# --- kernel vectors: unit solutions on the free variables
free = [x for x in range(2352) if x not in set(C)]
assert len(free) == 197
A = flint.fmpq_mat(J[np.ix_(E, C)].tolist())          # 2155 x 2155, invertible
B = flint.fmpq_mat((-J[np.ix_(E, free)]).tolist())     # 2155 x 197
S = A.solve(B)                                          # pivot parts of the unit solutions
den = 1
for i in range(S.nrows()):
    for j in range(S.ncols()):
        den = int(np.lcm(den, int(S[i, j].q)))
print("common denominator of unit kernel solutions:", den)
kernel = np.zeros((197, 2352), dtype=object)
for f in range(197):
    kernel[f, free[f]] = 1
    for r in range(2155):
        q = S[r, f]
        kernel[f, C[r]] = Fraction(int(q.p), int(q.q))
assert den == 1, "non-integral unit solutions; a triangular HNF basis is needed instead"
K = kernel.astype(np.int64)
assert not (J @ K.T).any()
print("197 integer kernel vectors with identity minor on the free variables: exact J v = 0 over Z")

# --- orbit generators in the repo's index order and convention
def vertex_unit_coeff(g, i, j):
    """Mirror of Decomposition.vertexUnitCoefficient with row-major 4x4 indices."""
    out = np.zeros(2352, np.int64)
    Pm = P.reshape(49, 3, 4, 4)
    for s in range(49):
        for a, b in itertools.product(range(4), repeat=2):
            u = (Pm[s, 0, i, b] if a == j else 0) if g == 0 else ((-Pm[s, 0, a, j] if b == i else 0) if g == 1 else 0)
            v = (Pm[s, 1, i, b] if a == j else 0) if g == 1 else ((-Pm[s, 1, a, j] if b == i else 0) if g == 2 else 0)
            w = (-Pm[s, 2, j, b] if a == i else 0) if g == 0 else ((Pm[s, 2, a, i] if b == j else 0) if g == 2 else 0)
            out[var(s, 0, 4*a+b)] = u; out[var(s, 1, 4*a+b)] = v; out[var(s, 2, 4*a+b)] = w
    return out

def term_unit_coeff(k, second):
    out = np.zeros(2352, np.int64)
    out[var(k, 0, 0):var(k, 0, 0)+16] = P[k, 0]
    if second: out[var(k, 1, 0):var(k, 1, 0)+16] = -P[k, 1]
    else: out[var(k, 2, 0):var(k, 2, 0)+16] = -P[k, 2]
    return out

# index: 0..47 global (g, i, j) = (n // 16, (n % 16) // 4, n % 4); 48..145 term (k, second) = ((n-48)//2, (n-48)%2==1)
gens = [vertex_unit_coeff(n // 16, (n % 16) // 4, n % 4) for n in range(48)] + \
       [term_unit_coeff((n - 48) // 2, (n - 48) % 2 == 1) for n in range(48, 146)]
G = np.array(gens)
assert not (J @ G.T).any()
print("orbit generators tangent; rank over Q / F3:",
      flint.fmpz_mat(G.tolist()).rank(), flint.nmod_mat((G % 3).tolist(), 3).rank())

# three central relations: identity in vertex g equals a combination of term scalings
rels = []
for g in range(3):
    lhs = sum(G[16*g + 5*i] for i in range(4))     # (g, i, i)
    t_false = sum(G[48 + 2*k] for k in range(49)); t_true = sum(G[48 + 2*k + 1] for k in range(49))
    rhs = {0: t_false, 1: -t_true, 2: t_true - t_false}[g]
    assert (lhs == rhs).all(), g
    coeffs = {16*g + 5*i: 1 for i in range(4)}
    for k in range(49):
        c = {0: {0: -1}, 1: {1: 1}, 2: {1: -1, 0: 1}}[g]
        for sec, v in c.items(): coeffs[48 + 2*k + sec] = coeffs.get(48 + 2*k + sec, 0) + v
    rels.append(coeffs)  # sum coeffs[n] * G[n] = 0
for coeffs in rels:
    assert not sum(v * G[n] for n, v in coeffs.items()).any()
excluded = [16*g + 0 for g in range(3)]  # (g, 0, 0): coefficient 1 in relation g
for g, n in enumerate(excluded): assert rels[g][n] == 1 and all(rels[h].get(n, 0) == 0 for h in range(3) if h != g)
kept = [n for n in range(146) if n not in excluded]

# triangular 143 x 143 minor: greedy pivot search with +-1 pivots, upper triangular in kept order
Gk = G[kept]
order, coords, used = [], [], set()
rows = list(range(143))
# repeatedly pick a row having a coordinate where it is +-1 and all remaining rows are 0
remaining = set(rows)
while remaining:
    found = False
    for r in sorted(remaining):
        for x in np.flatnonzero(Gk[r]):
            if x in used or abs(Gk[r, x]) != 1: continue
            if all(Gk[o, x] == 0 for o in remaining if o != r):
                order.append(r); coords.append(int(x)); used.add(int(x)); remaining.remove(r); found = True; break
        if found: break
    if not found:
        raise SystemExit(f"triangular pivot search stuck with {len(remaining)} rows left")
M = Gk[order][:, coords]
assert all(M[i, j] == 0 for i in range(143) for j in range(143) if i > j) or \
       all(M[i, j] == 0 for i in range(143) for j in range(143) if i < j)
assert all(abs(M[i, i]) == 1 for i in range(143))
print("orbit: 143 kept generators with a +-1 triangular minor; 3 relations verified")

json.dump([int(x) for x in point], open(f"{out_dir}/lwh_point.json", "w"))
json.dump(trace, open(f"{out_dir}/lwh_trace.json", "w"))
json.dump({"free": free, "kernel": [[(int(x), int(K[f, x])) for x in np.flatnonzero(K[f])] for f in range(197)]},
          open(f"{out_dir}/lwh_kernel.json", "w"))
json.dump({"kept": [kept[r] for r in order], "coords": coords, "excluded": excluded,
           "relations": [{str(k): v for k, v in r.items() if v} for r in rels]},
          open(f"{out_dir}/lwh_orbit.json", "w"))
print("wrote certificate data")
