"""Emit bounded kernel batches for the augmented [J | M] rank trace.

The batches are spread over a linear chain of modules so that each Lean process stays
small; the dispatch module `AugmentedChecks` assembles them.
"""

from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
FAMILIES = [("Steps", "checkMixedStep", 2916, 8), ("Pivots", "checkPivotAt", 2749, 32),
            ("Cover", "checkCoverAt", 5268, 32), ("Order", "checkOrderAt", 2748, 32)]
WIDTH = 32
HEADER = ["set_option maxRecDepth 32768", "set_option maxHeartbeats 0", ""]


def main():
    folder = LEAN / "Brent/Generated/AugmentedBlocks"
    folder.mkdir(exist_ok=True)
    for old in folder.glob("*.lean"):
        old.unlink()
    previous = "Brent.AugmentedTrace"
    index = 0
    for name, check, n, per_module in FAMILIES:
        blocks = -(-n // WIDTH)
        for start in range(0, blocks, per_module):
            out = [f"import {previous}", "",
                   "/- Generated bounded-size batches for the augmented rank trace. -/",
                   "namespace Brent.AugmentedTrace", ""] + HEADER
            for q in range(start, min(blocks, start + per_module)):
                stmt = f"{check} (Fin.ofNat {n} ({q * WIDTH} + j.val)) = true"
                out += [f"theorem aug{name}{q} (j : Fin {WIDTH}) :", f"    {stmt} :=",
                        f"  (by decide +kernel : ∀ j : Fin {WIDTH},", f"    {stmt}) j", ""]
            out += ["end Brent.AugmentedTrace", ""]
            (folder / f"Block{index}.lean").write_text("\n".join(out))
            previous = f"Brent.Generated.AugmentedBlocks.Block{index}"
            index += 1
    out = [f"import {previous}", "import Mathlib.Tactic.FinCases", "",
           "/- Generated dispatch for the augmented rank trace. -/",
           "namespace Brent.AugmentedTrace", ""] + HEADER
    for name, check, n, _ in FAMILIES:
        blocks = -(-n // WIDTH)
        out += [f"private theorem aug{name}Batch (q : Fin {blocks}) (r : Fin {WIDTH}) :",
                f"    {check} (Fin.ofNat {n} (q.val * {WIDTH} + r.val)) = true := by",
                "  fin_cases q"]
        out += [f"  · exact aug{name}{q} r" for q in range(blocks)]
        out += ["", f"theorem checked{name} (i : Fin {n}) : {check} i = true := by",
                "  have bound := i.isLt",
                f"  let q : Fin {blocks} := ⟨i.val / {WIDTH}, by omega⟩",
                f"  let r : Fin {WIDTH} := ⟨i.val % {WIDTH}, by omega⟩",
                f"  have he : Fin.ofNat {n} (q.val * {WIDTH} + r.val) = i := by",
                "    apply Fin.ext",
                f"    change (i.val / {WIDTH} * {WIDTH} + i.val % {WIDTH}) % {n} = i.val",
                "    omega",
                f"  exact he ▸ aug{name}Batch q r", ""]
    out += ["/-- **Augmented rank.** The Jacobian columns together with the 2916 mixed quadratic",
            "columns span a space of dimension 2749 over every field. -/",
            "theorem augmented_rank (k : Type) [Field k] :",
            "    Module.finrank k (Submodule.span k (Set.range (fun i =>",
            "      SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (original i)))) = 2749 :=",
            "  rank_of_checks k checkedSteps checkedPivots checkedCover checkedOrder", "",
            "end Brent.AugmentedTrace", ""]
    (LEAN / "Brent/Generated/AugmentedChecks.lean").write_text("\n".join(out))
    print(index, "block modules")


if __name__ == "__main__":
    main()
