#!/usr/bin/env python3
"""Exact rank-profile filter for the two displayed Strassen-square families."""
import argparse
from hashlib import sha256
from functools import lru_cache
import json
from pathlib import Path

import numpy as np

REVISION = "1949163da3bef7e3eb268a3ac015fd1c2dbfc767"
SHA256 = "15d27e300a68868710c2f5824f7987b10e004c6d7de6a3e65ae35caf42ed06a3"

@lru_cache(maxsize=2)
def inverses(modulus):
    inv = np.zeros(modulus, dtype=np.int64)
    inv[1] = 1
    for k in range(2, modulus):
        inv[k] = -(modulus // k) * inv[modulus % k] % modulus
    return inv

def matrix_ranks(matrices, modulus):
    """Batched row elimination, preserving exactness with signed int64."""
    rows = matrices.astype(np.int64) % modulus
    inv = inverses(modulus)
    ranks = np.zeros(len(rows), dtype=np.int64)
    for column in range(4):
        nonzero = (rows[:, :, column] != 0) & (np.arange(4)[None, :] >= ranks[:, None])
        selected = np.flatnonzero(nonzero.any(axis=1))
        if not len(selected):
            continue
        pivot = nonzero[selected].argmax(axis=1)
        current = ranks[selected]
        rows[selected, current], rows[selected, pivot] = rows[selected, pivot], rows[selected, current]
        normalized = rows[selected, current] * inv[rows[selected, current, column]][:, None] % modulus
        for row in range(4):
            later = selected[ranks[selected] < row]
            rows[later, row] = (rows[later, row] -
                                rows[later, row, column, None] * normalized[np.searchsorted(selected, later)]) % modulus
        ranks[selected] += 1
    return ranks

def annihilators(matrices, modulus):
    """Return two vectors annihilating the rows of each rank-two matrix."""
    rows = matrices.reshape(-1, 4, 4).copy() % modulus
    n = len(rows)
    inv = inverses(modulus)
    ids = np.arange(n)
    pivots = np.empty((n, 2), dtype=np.int64)
    for t in range(2):
        sub = rows[:, t:, :]
        column = (sub != 0).any(axis=1).argmax(axis=1)
        pivot = t+(rows[ids, :, column][:, t:] != 0).argmax(axis=1)
        rows[ids,t],rows[ids,pivot] = rows[ids,pivot],rows[ids,t]
        normal = rows[:,t] * inv[rows[ids,t,column]][:,None] % modulus
        for other in range(4):
            if other != t:
                rows[:,other] = (rows[:,other] - rows[ids,other,column,None]*normal) % modulus
        rows[:,t] = normal
        pivots[:,t] = column
    free_mask = np.ones((n,4), dtype=bool)
    free_mask[ids[:,None],pivots] = False
    free = np.nonzero(free_mask)[1].reshape(n,2)
    answer = np.zeros((n,4,2),dtype=np.int64)
    for t in range(2):
        answer[ids,free[:,t],t] = 1
        for j in range(2):
            answer[ids,pivots[:,j],t] = -rows[ids,j,free[:,t]] % modulus
    return answer.reshape(*matrices.shape[:-2],4,2)

def anchor_filter(terms, profile, modulus):
    """Six outer blocks need rank-two anchors with six rank-one children."""
    if not len(terms):
        return np.empty(0,dtype=bool)
    rank_one = terms[profile==1].reshape(-1,36,3,4,4)
    anchors = terms[profile==2].reshape(-1,12,3,4,4)
    compatible = np.ones((len(terms),36,12),dtype=bool)
    for transpose in (False,True):
        one, two = (x.swapaxes(-1,-2) if transpose else x for x in (rank_one,anchors))
        row = np.take_along_axis(one, (one%modulus != 0).any(axis=-1).argmax(axis=-1)[...,None,None],axis=-2)[...,0,:]
        null = annihilators(two,modulus)
        values = np.einsum('brmk,bamkl->braml',row,null) % modulus
        compatible &= (values==0).all(axis=(-1,-2))
    useful = compatible.sum(axis=1)>=6
    return (useful.sum(axis=1)>=6) & (compatible & useful[:,None,:]).any(axis=2).all(axis=1)

def evaluate(factors, modulus):
    same, possible, anchors = [], [], []
    for offset in range(0, len(factors), 128):
        block = factors[offset:offset + 128]
        r = matrix_ranks(block.reshape(-1, 4, 4), modulus).reshape(-1, 49, 3)
        diagonal_triples = (r == r[:, :, :1]).all(axis=2).all(axis=1)
        profile = r[:, :, 0]
        match = np.flatnonzero(diagonal_triples &
                    ((profile == 1).sum(axis=1) == 36) & ((profile == 2).sum(axis=1) == 12) &
                    ((profile == 4).sum(axis=1) == 1))
        same.extend((offset+match).tolist())
        ok = anchor_filter(block[match].reshape(-1,49,3,4,4),profile[match],modulus)
        anchors.extend((offset+match[ok]).tolist())
        maximum = r.max(axis=2)
        possible.extend((offset+np.flatnonzero(((maximum > 1).sum(axis=1) <= 13) &
                                             ((maximum > 2).sum(axis=1) <= 1))).tolist())
    def summarize(indices):
        return {"count":len(indices),"excluded_indices":sorted(set(range(len(factors)))-set(indices))}
    return {"equal_rank_profile":summarize(same),"closure_rank_bound":summarize(possible),
            "equal_profile_with_anchors":summarize(anchors)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog",type=Path)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    if sha256(args.catalog.read_bytes()).hexdigest()!=SHA256:
        raise ValueError("unexpected AlphaTensor catalog SHA-256")
    with np.load(args.catalog,allow_pickle=False) as source:
        factors=source["factorizations"]
    if factors.shape!=(14236,49,3,16) or factors.dtype!=np.int64:
        raise ValueError("unexpected AlphaTensor catalog layout")
    # Hadamard bounds every square minor of these 4 x 4 integer matrices.
    maximum=int(np.abs(factors).max())
    bound=max((s*maximum**2)**s for s in range(1,5))
    prime=65521
    if bound>=prime**2:
        raise ValueError("the modulus does not exceed the Hadamard bound")
    report={"revision":REVISION,"sha256":SHA256,"size":len(factors),
            "factor_entry_abs_max":maximum,"characteristic_zero_prime":prime,
            "F3":evaluate(factors,3),"Q":evaluate(factors,prime)}
    if args.output: args.output.write_text(json.dumps(report,indent=2)+"\n")
    print({field:{name:items['count'] for name,items in report[field].items()} for field in ("F3","Q")})

if __name__=="__main__":
    main()
