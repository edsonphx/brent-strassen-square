#!/usr/bin/env python3
"""Independently compare every packed Lean catalogue entry with the pinned NPZ.

This is the external provenance boundary, not a Lean proof of SHA-256 or NPZ
parsing.  No rank prediction or certificate-generator code is imported.
"""
import argparse
import hashlib
import re
from pathlib import Path

import numpy as np

SHA256 = "15d27e300a68868710c2f5824f7987b10e004c6d7de6a3e65ae35caf42ed06a3"
SHAPE = (14236, 49, 3, 16)
CHUNK = 128


def verify_binding(factors, root: Path, chunk_size=CHUNK):
    """Check canonical source shape, chunk order, and every decoded coordinate."""
    if factors.ndim != 4 or factors.shape[1:] != (49, 3, 16):
        raise ValueError("unexpected factor layout")
    if not np.issubdtype(factors.dtype, np.signedinteger):
        raise ValueError("factor array is not signed integral")
    if np.any(factors < -4) or np.any(factors > 4):
        raise ValueError("factor entry outside [-4,4]")
    n = len(factors)
    width = 49 * 3 * 16
    nchunks = (n + chunk_size - 1) // chunk_size
    names = [f"d{c:03d}" for c in range(nchunks)]
    top = (root / "Data.lean").read_text(encoding="utf-8")
    body = re.findall(r"def\s+chunks\s*:\s*List\s*\(List\s+Nat\)\s*:=\s*\[([^\]]*)\]", top)
    if len(body) != 1 or [s.strip() for s in body[0].split(",")] != names:
        raise ValueError("wrong Data.chunks ordering")
    imports = re.findall(r"^import Brent\.Catalogue\.Data\.(D\d+)\s*$", top, re.M)
    if imports != [name.upper() for name in names]:
        raise ValueError("wrong Data imports")
    if sorted(p.name for p in (root / "Data").glob("*.lean")) != [name.upper()+".lean" for name in names]:
        raise ValueError("missing or unexpected Data chunk")
    for c, name in enumerate(names):
        text = (root / "Data" / (name.upper()+".lean")).read_text(encoding="utf-8")
        # Parse only the exact generated declaration, not comments or certificates.
        match = re.fullmatch(r"\s*--[^\n]*\n\s*namespace Brent\.Catalogue\.Data\s*\n"
                             r"\s*/--[^*]*-\/\s*\n\s*def " + name +
                             r"\s*:\s*List Nat\s*:=\s*\[([0-9a-fx,\s]*)\]\s*"
                             r"end Brent\.Catalogue\.Data\s*", text)
        if match is None:
            raise ValueError(f"unexpected declaration in {name}")
        nums = [s.strip() for s in match.group(1).split(",")]
        lo = c * chunk_size
        hi = min(n, lo + chunk_size)
        if len(nums) != hi - lo:
            raise ValueError(f"wrong chunk size in {name}")
        for p, literal in enumerate(nums, lo):
            if not re.fullmatch(r"0x[0-9a-f]+", literal) or len(literal) != width + 2:
                raise ValueError(f"wrong packed width at point {p}")
            # Lean ent extracts the least significant hexadecimal digits, minus 4.
            # Decode the textual literal independently of the generator's pack function.
            actual = np.frombuffer(literal[:1:-1].encode("ascii"), dtype=np.uint8).astype(np.int16)
            if np.any(actual < ord('0')) or np.any(actual > ord('8')):
                raise ValueError(f"invalid packed digit at point {p}")
            actual -= ord('0') + 4
            expected = factors[p].reshape(-1)
            mismatches = np.flatnonzero(actual != expected)
            if len(mismatches):
                i = int(mismatches[0]); s, rest = divmod(i, 48); m, ij = divmod(rest, 16)
                raise ValueError(f"source mismatch: point={p}, summand={s}, mode={m}, entry={ij}")
    return n * width


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("npz", type=Path)
    parser.add_argument("project", type=Path)
    args = parser.parse_args()
    if hashlib.sha256(args.npz.read_bytes()).hexdigest() != SHA256:
        raise ValueError("catalogue SHA-256 mismatch")
    with np.load(args.npz, allow_pickle=False) as source:
        factors = source["factorizations"]
    if factors.shape != SHAPE or factors.dtype != np.int64:
        raise ValueError("unexpected pinned catalogue layout")
    count = verify_binding(factors, args.project / "Brent" / "Catalogue")
    print(f"Verified source binding: {count:,} integer factor entries")


if __name__ == "__main__":
    main()
