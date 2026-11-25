"""Generate bounded kernel replay batches for the 54 mixed quadratic forms."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "Brent" / "Generated"
BLOCKS = ROOT / "MixedBlocks"
COLUMN_COUNT = 2916
WIDTH = 12
BLOCK_COUNT = 9
BATCH_COUNT = (COLUMN_COUNT + WIDTH - 1) // WIDTH


def emit(path, lines):
    content = "\n".join(lines) + "\n"
    if not path.exists() or path.read_text() != content:
        path.write_text(content)


def main():
    BLOCKS.mkdir(parents=True, exist_ok=True)
    batches_per_block = BATCH_COUNT // BLOCK_COUNT
    for block in range(BLOCK_COUNT):
        dependency = "Brent.QuadraticMixed" if block == 0 else f"Brent.Generated.MixedBlocks.Block{block - 1}"
        lines = [
            f"import {dependency}",
            "",
            "/- Generated finite checks for the archived mixed coefficients and leading terms. -/",
            "namespace Brent.QuadraticData",
            "",
            "set_option maxRecDepth 32768",
            "set_option maxHeartbeats 0",
            "",
        ]
        first = block * batches_per_block
        for batch in range(first, first + batches_per_block):
            expr = f"checkMixedNumber (Fin.ofNat 2916 ({batch * WIDTH} + j.val)) = true"
            lines += [
                f"theorem mixed{batch} (j : Fin {WIDTH}) :",
                f"    {expr} :=",
                f"  (by decide +kernel : ∀ j : Fin {WIDTH},",
                f"    {expr}) j",
                "",
            ]
        emit(BLOCKS / f"Block{block}.lean", lines + ["end Brent.QuadraticData"])
    lines = [
        f"import Brent.Generated.MixedBlocks.Block{BLOCK_COUNT - 1}",
        "import Mathlib.Tactic.FinCases",
        "",
        "/- Generated dispatch for the mixed coefficient certificate. -/",
        "namespace Brent.QuadraticData",
        "",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        "",
        f"private theorem checkedBatch (q : Fin {BATCH_COUNT}) (r : Fin {WIDTH}) :",
        f"    checkMixedNumber (Fin.ofNat 2916 (q.val * {WIDTH} + r.val)) = true := by",
        "  fin_cases q",
        *(f"  · exact mixed{i} r" for i in range(BATCH_COUNT)),
        "",
        "theorem checkedMixedNumber (i : Fin 2916) : checkMixedNumber i = true := by",
        "  have bound := i.isLt",
        f"  let q : Fin {BATCH_COUNT} := ⟨i.val / {WIDTH}, by omega⟩",
        f"  let r : Fin {WIDTH} := ⟨i.val % {WIDTH}, by omega⟩",
        f"  have he : Fin.ofNat 2916 (q.val * {WIDTH} + r.val) = i := by",
        "    apply Fin.ext",
        f"    change (i.val / {WIDTH} * {WIDTH} + i.val % {WIDTH}) % 2916 = i.val",
        "    omega",
        "  exact he ▸ checkedBatch q r",
        "",
        "end Brent.QuadraticData",
    ]
    emit(ROOT / "MixedChecks.lean", lines)


if __name__ == "__main__":
    main()
