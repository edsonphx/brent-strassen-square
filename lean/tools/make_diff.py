"""Make a unified .diff between a pristine copy and a working copy, without git.

Usage (from anywhere):
    python make_diff.py <pristine_dir> <working_dir> <out.diff>

Compares every .lean, .py, .md, .txt and .toml file. Paths in the diff are relative to the two
directories, with a/ and b/ prefixes, so `git apply -p1 out.diff` works in the repository root.
Skips .lake/, build output, and the generated catalogue files listed in GENERATED_SHA256.txt.
"""

import difflib
import os
import sys

EXTS = (".lean", ".py", ".md", ".txt", ".toml")
SKIP = {".lake", "build", "__pycache__", ".git"}


def files(root):
    out = set()
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x not in SKIP]
        for f in fs:
            if f.endswith(EXTS):
                out.add(os.path.relpath(os.path.join(d, f), root).replace(os.sep, "/"))
    return out


def read(path):
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8", newline="") as h:
        return h.read().replace("\r\n", "\n").splitlines(keepends=True)


def generated(root):
    """Files produced by the catalogue generator (listed in GENERATED_SHA256.txt)."""
    for lst in ("lean/Brent/Catalogue/GENERATED_SHA256.txt", "Brent/Catalogue/GENERATED_SHA256.txt"):
        path = os.path.join(root, lst)
        if os.path.exists(path):
            prefix = "lean/" if lst.startswith("lean/") else ""
            with open(path, encoding="utf-8-sig") as h:
                return {prefix + line.split()[1] for line in h if line.strip()}
    return set()


def main():
    old_root, new_root, out = sys.argv[1:4]
    skip = generated(old_root) | generated(new_root)
    names = sorted((files(old_root) | files(new_root)) - skip)
    chunks = []
    for n in names:
        a, b = read(os.path.join(old_root, n)), read(os.path.join(new_root, n))
        if a == b:
            continue
        chunks.extend(difflib.unified_diff(
            a, b, fromfile="a/" + n if a else "/dev/null", tofile="b/" + n if b else "/dev/null"))
        if chunks and not chunks[-1].endswith("\n"):
            chunks[-1] += "\n\\ No newline at end of file\n"
    with open(out, "w", encoding="utf-8", newline="\n") as h:
        h.writelines(chunks)
    changed = sum(1 for c in chunks if c.startswith("+++ "))
    print(f"{changed} files changed -> {out}")


if __name__ == "__main__":
    main()
