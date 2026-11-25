"""Generate a signed unit-pivot trace for the Jacobian and mixed quadratic columns."""

import numpy as np

from generate_jacobian_trace import LEAN_ROOT, SOURCE_ROOT, emit_chunked_array, trace
from verify_certificate import jacobian_rows, mixed_row


JACOBIAN_COLUMNS = 2352


def pack(items):
    """Use 13 bits for a coordinate and 4 for the signed coefficient."""
    packed = 0
    for index, (coordinate, value) in enumerate(items):
        if not (0 <= coordinate < 8192 and 0 < abs(value) <= 7):
            raise ValueError(f"trace entry out of range: {(coordinate, value)}")
        code = 2 * abs(value) + (value < 0)
        packed |= ((coordinate << 4) | code) << (17 * index)
    return hex(packed)


def main():
    with np.load(SOURCE_ROOT / "data/strassen_square_factors.npz", allow_pickle=False) as arrays:
        terms = np.stack([arrays[key] for key in ("U", "V", "W")], axis=1)
    with np.load(SOURCE_ROOT / "data/tangent_bases.npz", allow_pickle=False) as arrays:
        mixed = [mixed_row(terms, x, y) for x in arrays["X"] for y in arrays["Y"]]
    reduced, operations, pivots = trace(np.concatenate((jacobian_rows(terms), mixed)))
    expected = 2749
    if len(pivots) != expected:
        raise ValueError(f"expected {expected} unit pivots, got {len(pivots)}")
    coverage = {column: index for index, (_, column) in enumerate(pivots)}
    data = [
        ("mixedReducedData", "Nat", [pack(row.items()) for row in reduced[JACOBIAN_COLUMNS:]]),
        ("mixedOperationsData", "Nat", [pack(ops) for ops in operations[JACOBIAN_COLUMNS:]]),
        ("selectData", "Fin 5268", [str(j) for _, j in pivots]),
        ("pivotData", "Fin 4096", [str(e) for e, _ in pivots]),
        ("coverData", "Option (Fin 2749)",
         [f"some {coverage[j]}" if j in coverage else "none" for j in range(len(reduced))]),
    ]
    lines = [
        "/- Generated candidate data. The kernel independently verifies the trace. -/",
        "namespace Brent.AugmentedTrace",
        "",
    ]
    for name, kind, entries in data:
        lines.extend(emit_chunked_array(name, kind, entries))
    lines.extend(("end Brent.AugmentedTrace", ""))
    path = LEAN_ROOT / "Brent" / "Generated" / "AugmentedData.lean"
    path.write_text("\n".join(lines))


if __name__ == "__main__":
    main()
