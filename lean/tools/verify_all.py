#!/usr/bin/env python3
"""Fail-closed local Lean build, axiom audit and kernel replay.

Run from any directory; paths are relative to lean/.  No build is deleted.
CI is intentionally separate because of runner memory limits.
"""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Brent/Catalogue/GENERATED_SHA256.txt"
NPZ_NAME = "alphatensor_14236_factorizations.npz"
NPZ_SHA = "15d27e300a68868710c2f5824f7987b10e004c6d7de6a3e65ae35caf42ed06a3"
NPZ_URLS = (
    "https://raw.githubusercontent.com/google-deepmind/alphatensor/"
    "1949163da3bef7e3eb268a3ac015fd1c2dbfc767/nonequivalence/" + NPZ_NAME,
    # The branch URL is only a transport fallback; the pinned hash is mandatory.
    "https://github.com/google-deepmind/alphatensor/raw/refs/heads/main/nonequivalence/" + NPZ_NAME,
)
ENV = dict(os.environ)
ENV.setdefault("LEAN_NUM_THREADS", "1")
LOG = None


def report(message):
    print(message, flush=True)
    if LOG is not None:
        print(message, file=LOG, flush=True)


def run(*args):
    args = [str(a) for a in args]
    report("+ " + " ".join(shlex.quote(a) for a in args))
    if LOG is None:
        subprocess.run(args, cwd=ROOT, env=ENV, check=True)
        return
    with subprocess.Popen(args, cwd=ROOT, env=ENV, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                          errors="replace") as process:
        for line in process.stdout:
            report(line.rstrip("\n"))
        code = process.wait()
    if code:
        raise subprocess.CalledProcessError(code, args)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def generated_manifest():
    result = {}
    for line in MANIFEST.read_text(encoding="utf-8-sig").splitlines():
        if not line.strip():
            continue
        digest, name = line.split(maxsplit=1)
        p = Path(name.strip())
        if (p.is_absolute() or ".." in p.parts or p.parts[:2] != ("Brent", "Catalogue")
                or p.suffix != ".lean" or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or p in result):
            raise ValueError(f"Invalid generated manifest row: {line}")
        result[p] = digest
    if not result:
        raise ValueError("Empty generated catalogue manifest")
    return result


def generated_errors():
    return [str(p) for p, expected in generated_manifest().items()
            if not (ROOT / p).is_file() or sha(ROOT / p) != expected]


def check_generated():
    errors = generated_errors()
    if errors:
        raise ValueError(f"Missing or changed generated catalogue files ({len(errors)}): "
                         + ", ".join(errors[:5]) + "; regenerate from the pinned NPZ")
    report(f"Generated catalogue hashes: {len(generated_manifest())} OK")


def prepare_catalogue(npz):
    cache = ROOT / ".lake/catalogue"
    cache.mkdir(parents=True, exist_ok=True)
    if npz is None:
        candidates = [cache / NPZ_NAME, ROOT.parent / NPZ_NAME,
                      ROOT.parent / "alphatensor-catalog.npz",
                      Path.home() / "Downloads" / NPZ_NAME, Path("/tmp") / NPZ_NAME]
        npz = next((p for p in candidates if p.is_file() and sha(p) == NPZ_SHA), None)
        if npz is None:
            npz = cache / NPZ_NAME
            temp = cache / (NPZ_NAME + ".part")
            report(f"Downloading pinned catalogue to {npz}")
            errors = []
            for url in NPZ_URLS:
                try:
                    request = urllib.request.Request(url, headers={"User-Agent": "brent-verifier"})
                    with urllib.request.urlopen(request, timeout=120) as source, temp.open("wb") as out:
                        shutil.copyfileobj(source, out)
                    if sha(temp) != NPZ_SHA:
                        raise ValueError("Downloaded catalogue SHA-256 mismatch")
                    temp.replace(npz)
                    break
                except (OSError, ValueError) as error:
                    errors.append(f"{url}: {error}")
                finally:
                    temp.unlink(missing_ok=True)
            else:
                raise ValueError("Cannot download pinned catalogue; supply --npz PATH. "
                                 + "; ".join(errors))
    if not npz.is_file() or sha(npz) != NPZ_SHA:
        raise ValueError(f"Missing or invalid pinned catalogue: {npz}")
    report(f"Pinned catalogue SHA-256 OK: {npz}")
    # Use the selected Python environment; do not silently install or change packages.
    python = sys.executable
    if subprocess.run([python, "-I", "-c", "import numpy"],
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
        raise ValueError("NumPy is required: install it in your chosen Python environment")
    if generated_errors():
        run(python, "-I", "tools/catalogue/gen_catalogue_lean.py", npz, ROOT)
    check_generated()
    run(python, "-I", "tools/catalogue/verify_source_binding.py", npz, ROOT)
    witnesses = sorted((ROOT / "Brent/Generated").glob("AlphaTensorBound*.lean"))
    if not witnesses:
        raise ValueError("Missing AlphaTensor rank witnesses")
    run(python, "-I", ROOT.parent / "tools/verify_alphatensor_witnesses.py", npz, *witnesses)


def module_name(path):
    return ".".join(path.with_suffix("").parts)


def inventory():
    # Include expected generated files even before the catalogue phase creates them.
    paths = {Path("Brent.lean"), Path("Audit.lean"), *generated_manifest()}
    paths.update(p.relative_to(ROOT) for p in (ROOT / "Brent").rglob("*.lean"))
    return {module_name(p): p for p in sorted(paths)}


def imports(path):
    # All repository imports are conventional, one line per import. Strip trailing comments.
    for line in path.read_text(encoding="utf-8-sig").splitlines():
        match = re.match(r"^\s*(?:(?:public|meta)\s+)*import\s+(.+)$", line)
        if match:
            yield from match[1].split("--", 1)[0].split()


def ordered_modules(modules, selected):
    # Topological order avoids repeated recursive builds and puts Audit last.
    seen, visiting, result = set(), set(), []

    def visit(m):
        if m in seen:
            return
        if m in visiting:
            raise ValueError(f"Cyclic local import involving {m}")
        visiting.add(m)
        p = ROOT / modules[m]
        if not p.is_file():
            raise ValueError(f"Missing module source: {p}")
        for dep in imports(p):
            if dep == "Brent" or dep.startswith("Brent.") or dep == "Audit":
                if dep not in modules:
                    raise ValueError(f"{m} imports unknown local module {dep}")
                visit(dep)
        visiting.remove(m)
        seen.add(m)
        if m in selected:
            result.append(m)

    for m in sorted(selected - {"Audit"}):
        visit(m)
    if "Audit" in selected:
        visit("Audit")
    return result


def main():
    global LOG
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--npz", type=lambda p: Path(p).expanduser().resolve(),
                        help="local copy of the pinned catalogue (otherwise auto-detect/download)")
    parser.add_argument("--list", action="store_true", help="list inventory without building")
    parser.add_argument("--build-only", action="store_true", help="omit independent kernel replay, not the axiom audit")
    parser.add_argument("--cache", action="store_true", help="fetch prebuilt Mathlib dependencies")
    parser.add_argument("--log", type=Path, help="also write a verification transcript to this file")
    args = parser.parse_args()
    if args.log is not None:
        LOG = args.log.open("w", encoding="utf-8")
    if args.list:
        for m in sorted(inventory()):
            report(m)
        return
    if shutil.which("lake") is None:
        raise ValueError("lake not found on PATH; install Elan and the pinned Lean toolchain")
    run("lake", "--version")
    prepare_catalogue(args.npz)
    modules = inventory()
    ordered = ordered_modules(modules, set(modules))
    if set(ordered) != set(modules) or len(ordered) != len(modules) or ordered[-1] != "Audit":
        raise ValueError("Incomplete build plan or Audit is not last")
    if args.cache:
        # Fetch only the Mathlib imports used by the checked-in and generated sources.
        mathlib = sorted({dep for path in modules.values() if (ROOT / path).is_file()
                          for dep in imports(ROOT / path)
                          if dep == "Mathlib" or dep.startswith("Mathlib.")})
        if not mathlib:
            raise ValueError("No Mathlib imports found")
        run("lake", "exe", "cache", "get", *mathlib)
    for i, m in enumerate(ordered, 1):
        report(f"BUILD [{i}/{len(ordered)}] {m}")
        if m == "Audit":
            # Audit is a standalone source, not a member of the lightweight Brent library.
            # Elaborate its commands on every invocation and retain an object for replay.
            target = ROOT / ".lake/build/lib/lean/Audit.olean"
            target.parent.mkdir(parents=True, exist_ok=True)
            run("lake", "env", "lean", "-o", target, "Audit.lean")
        else:
            run("lake", "build", "+" + m)
    if not args.build_only:
        for i, m in enumerate(ordered, 1):
            report(f"REPLAY [{i}/{len(ordered)}] {m}")
            run("lake", "env", "leanchecker", "-v", m)
    report(f"PASS: {len(ordered)} modules; axiom audit executed; "
           f"kernel replay {'skipped' if args.build_only else 'completed'}")



if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as e:
        message = f"VERIFICATION FAILED: {e}"
        print(message, file=sys.stderr)
        if LOG is not None:
            print(message, file=LOG, flush=True)
        sys.exit(1)
    finally:
        if LOG is not None:
            LOG.close()
