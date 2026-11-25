"""Generate bounded kernel replay batches for the frozen Jacobian trace."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "Brent" / "Generated"
BLOCKS = ROOT / "RankBlocks"
SOURCE_ROWS = 2352
ROW_IDENTITY = "SparseRow.checkRadixStep 4096 12 original reduced operations"
PIVOT_CHECK = "checkAuxiliary"


def emit(path, lines):
    content = "\n".join(lines) + "\n"
    if not path.exists() or path.read_text() != content:
        path.write_text(content)


def write_batches(module_prefix, theorem_prefix, check, width, block_count, imports):
    batch_count = SOURCE_ROWS // width
    batches_per_block = batch_count // block_count
    for block in range(block_count):
        header = imports if block == 0 else [
            f"import Brent.Generated.RankBlocks.{module_prefix}{block - 1}"
        ]
        lines = header + [
            "",
            ("/- Generated bounded-size batches for the signed Jacobian trace. -/"
             if check == ROW_IDENTITY else "/- Generated bounded-size coverage and pivot checks. -/"),
            "namespace Brent.JacobianTrace",
            "",
            "set_option maxRecDepth 32768",
            "set_option maxHeartbeats 0",
            "",
        ]
        first = block * batches_per_block
        for chunk in range(first, first + batches_per_block):
            check_expr = f"{check} (Fin.ofNat 2352 ({chunk * width} + j.val)) = true"
            lines += [
                f"theorem {theorem_prefix}{chunk} (j : Fin {width}) :" +
                (f" {check_expr} :=" if check == PIVOT_CHECK else ""),
            ]
            if check != PIVOT_CHECK:
                lines.append(f"    {check_expr} :=")
            lines += [
                f"  (by decide +kernel : ∀ j : Fin {width},",
                f"    {check_expr}) j",
                "",
            ]
        emit(BLOCKS / f"{module_prefix}{block}.lean", lines + ["end Brent.JacobianTrace"])


def dispatch(name, prefix, prop, size):
    count = SOURCE_ROWS // size
    return [
        f"private theorem check{name}Batch (q : Fin {count}) (r : Fin {size}) :",
        f"    {prop} (Fin.ofNat {SOURCE_ROWS} (q.val * {size} + r.val)) = true := by",
        "  fin_cases q",
        *(f"  · exact {prefix}{i} r" for i in range(count)),
        "",
        f"theorem checked{name} (i : Fin {SOURCE_ROWS}) : {prop} i = true := by",
        f"  obtain ⟨⟨q, r⟩, rfl⟩ := (finProdFinEquiv (m := {count}) (n := {size})).surjective i",
        f"  have hi : finProdFinEquiv (q, r) = Fin.ofNat {SOURCE_ROWS} (q.val * {size} + r.val) := by",
        "    apply Fin.ext",
        f"    change r.val + {size} * q.val = (q.val * {size} + r.val) % {SOURCE_ROWS}",
        "    omega",
        f"  simpa only [hi] using check{name}Batch q r",
        "",
    ]


def main():
    BLOCKS.mkdir(parents=True, exist_ok=True)
    write_batches("Block", "steps", ROW_IDENTITY, 8, 7,
                  ["import Brent.JacobianTrace", "import Brent.RadixReplay"])
    write_batches("Aux", "aux", PIVOT_CHECK, 16, 3, ["import Brent.KernelCheck.Conditions"])
    lines = [
        "import Brent.Generated.RankBlocks.Block6",
        "import Brent.Generated.RankBlocks.Aux2",
        "import Mathlib.Tactic.FinCases",
        "",
        "/- Generated dispatch for the finite Jacobian certificate checks. -/",
        "namespace Brent.JacobianTrace",
        "",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        "",
    ]
    lines += dispatch("Steps", "steps", ROW_IDENTITY, 8)
    lines += dispatch("Auxiliary", "aux", PIVOT_CHECK, 16)
    emit(ROOT / "RankChecks.lean", lines + ["end Brent.JacobianTrace"])


if __name__ == "__main__":
    main()
