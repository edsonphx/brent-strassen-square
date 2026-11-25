"""Shard the finite chart-derivative replay into serial kernel batches."""

from pathlib import Path

from generate_frame_block_checks import emit


ROOT = Path(__file__).resolve().parents[1] / "Brent" / "Generated"
BLOCKS = ROOT / "OriginBlocks"
COUNT = 251
WIDTH = 2
BATCHES = (COUNT + WIDTH - 1) // WIDTH
BATCHES_PER_BLOCK = 8


def main():
    BLOCKS.mkdir(parents=True, exist_ok=True)
    dependency = "Brent.FamilyOrigin"
    for block, first in enumerate(range(0, BATCHES, BATCHES_PER_BLOCK)):
        lines = [
            f"import {dependency}",
            "",
            "/- Generated kernel replay of chart derivative certificates. -/",
            "namespace Brent.TangentData",
            "",
            "set_option maxRecDepth 32768",
            "set_option maxHeartbeats 0",
            "",
        ]
        for q in range(first, min(first + BATCHES_PER_BLOCK, BATCHES)):
            expr = f"checkOrigin (Fin.ofNat {COUNT} ({q * WIDTH} + r.val)) = true"
            lines += [
                f"theorem originBatch{q} (r : Fin {WIDTH}) : {expr} :=",
                f"  (by decide +kernel : ∀ r : Fin {WIDTH}, {expr}) r",
                "",
            ]
        emit(BLOCKS / f"Block{block}.lean", lines + ["end Brent.TangentData"])
        dependency = f"Brent.Generated.OriginBlocks.Block{block}"
    emit(ROOT / "OriginChecks.lean", [
        f"import {dependency}",
        "import Mathlib.Tactic.FinCases",
        "",
        "namespace Brent.TangentData",
        "",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        "",
        f"private theorem checkedBatch (q : Fin {BATCHES}) (r : Fin {WIDTH}) :",
        f"    checkOrigin (Fin.ofNat {COUNT} (q.val * {WIDTH} + r.val)) = true := by",
        "  fin_cases q",
        *(f"  · exact originBatch{i} r" for i in range(BATCHES)),
        "",
        f"theorem checkedOrigin (i : Fin {COUNT}) : checkOrigin i = true := by",
        "  have bound := i.isLt",
        f"  let q : Fin {BATCHES} := ⟨i.val / {WIDTH}, by omega⟩",
        f"  let r : Fin {WIDTH} := ⟨i.val % {WIDTH}, by omega⟩",
        f"  have he : Fin.ofNat {COUNT} (q.val * {WIDTH} + r.val) = i := by",
        "    apply Fin.ext",
        f"    change (i.val / {WIDTH} * {WIDTH} + i.val % {WIDTH}) % {COUNT} = i.val",
        "    omega",
        "  exact he ▸ checkedBatch q r",
        "",
        "end Brent.TangentData",
    ])


if __name__ == "__main__":
    main()
