"""Record the generator index for each row of the frozen tangent frame."""

import sys

import numpy as np

from generate_jacobian_trace import LEAN_ROOT, SOURCE_ROOT, emit_chunked_array

sys.path.insert(0, str(SOURCE_ROOT))
from verify_certificate import BASE, Rank, generators, shuffled_product


def main():
    rank = Rank()
    indices = []
    with np.load(SOURCE_ROOT / "data" / "tangent_bases.npz", allow_pickle=False) as data:
        for name, candidates in zip(("G", "X", "Y"), generators(shuffled_product(BASE, BASE))):
            selected = rank.extend(candidates.reshape(len(candidates), -1))
            if not np.array_equal(candidates[selected], data[name]):
                raise ValueError(f"generator indices do not reconstruct {name}")
            indices.extend(selected)

    output = ["namespace Brent.TangentData", "", "/- Generator indices for the frozen frame. -/", ""]
    output.extend(emit_chunked_array("familyOrigins", "Nat", [str(i) for i in indices]))
    output.extend(("end Brent.TangentData", ""))
    (LEAN_ROOT / "Brent" / "Generated" / "FamilyOrigins.lean").write_text("\n".join(output))


if __name__ == "__main__":
    main()
