"""Rebuild the Lean proof modules from source and audit their reported axioms."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
# Lean imports must be available before the modules that depend on them.
MODULES = (
    "Diagonal", "BoardCuts", "BoardCells", "StripCounts", "StripGeometry",
    "StripProducts", "StripPlacement", "BoardEncoding", "BoardRoundtrip",
    "KingEnumeration",
)
MAIN_RESULTS = {
    "DimerDiagonal.exactly_one_diagonal_tiling",
    "KingEnumeration.exactly_two_rectangle",
    "KingEnumeration.exactly_two_square",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)


def audit(source, output):
    """Check that Lean reported every requested declaration in this module."""
    requested = re.findall(r"^#print axioms\s+(\S+)", source, re.MULTILINE)
    reports = list(AXIOM_REPORT.finditer(output))
    if [m[1].split(".")[-1] for m in reports] != [n.split(".")[-1] for n in requested]:
        raise SystemExit("Incomplete axiom report:\n" + output)
    for match in reports:
        axioms = {x.strip() for x in (match[2] or "").split(",") if x.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise SystemExit("Unexpected axiom dependency: " + match[0])
    return [m[1] for m in reports]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="path to the Lean executable")
    parser.add_argument("--report", type=Path, help="write the audit log to this file")
    args = parser.parse_args()
    found = shutil.which(args.lean)
    if not found:
        parser.error("Lean was not found. Install elan or provide --lean PATH.")
    lean = str(Path(found).absolute())  # keep elan's 'lean' proxy name on Unix
    version = subprocess.check_output([lean, "--version"], cwd=ROOT, encoding="utf-8").strip()
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    release = toolchain.rsplit(":v", 1)[-1]
    if not re.search(r"\bversion " + re.escape(release) + r"(?=,|\))", version):
        parser.error("Expected " + toolchain + ", found " + version)

    lines = []

    def log(message):
        print(message, flush=True)
        lines.append(message)

    log(version)
    log("Rebuilding from source with --trust=0 -DwarningAsError=true.")
    sources = [Path("KingGrid") / (module + ".lean") for module in MODULES]
    sources.append(Path("KingGrid.lean"))
    tracked = {p.relative_to(ROOT) for p in (ROOT / "KingGrid").rglob("*.lean")}
    if tracked != set(sources[:-1]):
        raise SystemExit("Module list differs from the Lean proofs in KingGrid/.")

    declarations = []
    with tempfile.TemporaryDirectory(prefix="king-grid-lean-") as directory:
        clean = Path(directory)
        (clean / "KingGrid").mkdir()
        shutil.copyfile(ROOT / "lean-toolchain", clean / "lean-toolchain")
        env = dict(os.environ, LEAN_PATH=str(clean))
        for path in sources:
            shutil.copyfile(ROOT / path, clean / path)
            command = [lean, "--trust=0", "-DwarningAsError=true",
                       "-o", str(path.with_suffix(".olean")), str(path)]
            run = subprocess.run(command, cwd=clean, env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, encoding="utf-8")
            output = run.stdout.strip()
            log("\n" + path.as_posix())
            if output:
                log(output)
            if run.returncode:
                raise SystemExit(run.returncode)
            declarations.extend(audit((clean / path).read_text(encoding="utf-8"), output))
    missing = MAIN_RESULTS - set(declarations)
    if missing:
        raise SystemExit("Missing main theorem reports: " + ", ".join(sorted(missing)))
    log(f"\nPASS: {len(sources)} modules, {len(declarations)} axiom reports.")
    if args.report:
        args.report.write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
