"""Generate bounded kernel replay batches for the 54 Jacobian-annihilating covectors."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "Brent" / "Generated"
BLOCKS = ROOT / "AnnihilatorBlocks"
PIVOT_COUNT = 2101
WIDTH = 16
BLOCK_COUNT = 3
BATCH_COUNT = (PIVOT_COUNT + WIDTH - 1) // WIDTH


def emit(path, lines):
    content = "\n".join(lines) + "\n"
    if not path.exists() or path.read_text() != content:
        path.write_text(content)


def main():
    BLOCKS.mkdir(parents=True, exist_ok=True)
    batches_per_block = BATCH_COUNT // BLOCK_COUNT
    for block in range(BLOCK_COUNT):
        dependency = "Brent.QuadraticAnnihilator" if block == 0 else f"Brent.Generated.AnnihilatorBlocks.Block{block - 1}"
        lines = [
            f"import {dependency}",
            "",
            "/- Generated finite checks for the archived Jacobian covectors. -/",
            "namespace Brent.QuadraticData",
            "",
            "set_option maxRecDepth 32768",
            "set_option maxHeartbeats 0",
            "",
        ]
        first = block * batches_per_block
        for batch in range(first, first + batches_per_block):
            expr = f"checkAnnihilatorPivot (Fin.ofNat 2101 ({batch * WIDTH} + j.val)) = true"
            lines += [
                f"theorem annihilator{batch} (j : Fin {WIDTH}) :",
                f"    {expr} :=",
                f"  (by decide +kernel : ∀ j : Fin {WIDTH},",
                f"    {expr}) j",
                "",
            ]
        emit(BLOCKS / f"Block{block}.lean", lines + ["end Brent.QuadraticData"])
    lines = [
        f"import Brent.Generated.AnnihilatorBlocks.Block{BLOCK_COUNT - 1}",
        "import Mathlib.Tactic.FinCases",
        "",
        "/- Generated dispatch for the finite covector certificate. -/",
        "namespace Brent.QuadraticData",
        "",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        "",
        f"private theorem checkedBatch (q : Fin {BATCH_COUNT}) (r : Fin {WIDTH}) :",
        f"    checkAnnihilatorPivot (Fin.ofNat 2101 (q.val * {WIDTH} + r.val)) = true := by",
        "  fin_cases q",
        *(f"  · exact annihilator{i} r" for i in range(BATCH_COUNT)),
        "",
        "theorem checkedAnnihilator (i : Fin 2101) : checkAnnihilatorPivot i = true := by",
        "  have bound := i.isLt",
        f"  let q : Fin {BATCH_COUNT} := ⟨i.val / {WIDTH}, by omega⟩",
        f"  let r : Fin {WIDTH} := ⟨i.val % {WIDTH}, by omega⟩",
        f"  have he : Fin.ofNat 2101 (q.val * {WIDTH} + r.val) = i := by",
        "    apply Fin.ext",
        f"    change (i.val / {WIDTH} * {WIDTH} + i.val % {WIDTH}) % 2101 = i.val",
        "    omega",
        "  exact he ▸ checkedBatch q r",
        "",
        "end Brent.QuadraticData",
    ]
    emit(ROOT / "AnnihilatorChecks.lean", lines)


if __name__ == "__main__":
    main()
