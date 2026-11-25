"""Generate bounded kernel replay batches for the correspondence of frozen tangent blocks."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "Brent" / "Generated"
BLOCKS = ROOT / "FrameBlockChecks"
COLUMN_COUNT = 54
WIDTH = 3
BLOCK_COUNT = 3
BATCH_COUNT = (COLUMN_COUNT + WIDTH - 1) // WIDTH


def emit(path, lines):
    content = "\n".join(lines) + "\n"
    if not path.exists() or path.read_text() != content:
        path.write_text(content)


def main():
    BLOCKS.mkdir(parents=True, exist_ok=True)
    batches_per_block = BATCH_COUNT // BLOCK_COUNT
    for block in range(BLOCK_COUNT):
        dependency = "Brent.FrameBlocks" if block == 0 else f"Brent.Generated.FrameBlockChecks.Block{block - 1}"
        lines = [
            f"import {dependency}",
            "",
            "/- Generated finite checks for the correspondence of frozen tangent blocks. -/",
            "namespace Brent.TangentData",
            "",
            "set_option maxRecDepth 32768",
            "set_option maxHeartbeats 0",
            "",
        ]
        first = block * batches_per_block
        for batch in range(first, first + batches_per_block):
            expr = f"checkBlock (Fin.ofNat 54 ({batch * WIDTH} + j.val)) = true"
            lines += [
                f"theorem blockMatch{batch} (j : Fin {WIDTH}) :",
                f"    {expr} :=",
                f"  (by decide +kernel : ∀ j : Fin {WIDTH},",
                f"    {expr}) j",
                "",
            ]
        emit(BLOCKS / f"Block{block}.lean", lines + ["end Brent.TangentData"])
    lines = [
        f"import Brent.Generated.FrameBlockChecks.Block{BLOCK_COUNT - 1}",
        "import Mathlib.Tactic.FinCases",
        "",
        "/- Generated dispatch for the tangent coefficient certificate. -/",
        "namespace Brent.TangentData",
        "",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        "",
        f"private theorem checkedBatch (q : Fin {BATCH_COUNT}) (r : Fin {WIDTH}) :",
        f"    checkBlock (Fin.ofNat 54 (q.val * {WIDTH} + r.val)) = true := by",
        "  fin_cases q",
        *(f"  · exact blockMatch{i} r" for i in range(BATCH_COUNT)),
        "",
        "theorem checkedBlock (i : Fin 54) : checkBlock i = true := by",
        "  have bound := i.isLt",
        f"  let q : Fin {BATCH_COUNT} := ⟨i.val / {WIDTH}, by omega⟩",
        f"  let r : Fin {WIDTH} := ⟨i.val % {WIDTH}, by omega⟩",
        f"  have he : Fin.ofNat 54 (q.val * {WIDTH} + r.val) = i := by",
        "    apply Fin.ext",
        f"    change (i.val / {WIDTH} * {WIDTH} + i.val % {WIDTH}) % 54 = i.val",
        "    omega",
        "  exact he ▸ checkedBatch q r",
        "",
        "end Brent.TangentData",
    ]
    emit(ROOT / "FrameBlockChecks.lean", lines)


if __name__ == "__main__":
    main()
