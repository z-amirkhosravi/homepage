#!/usr/bin/env python3
"""Build every local module, audit transitive axioms, and retain a replayable record."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "MATH_RESEARCH_AUDIT "


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="JSON run record (relative to formal/)")
    parser.add_argument("--clean-local", action="store_true",
                        help="Remove only this project’s build outputs before compiling; keep dependencies")
    parser.add_argument("--verbose-build", action="store_true",
                        help="Record Lake’s complete trace output, including compiler commands")
    args = parser.parse_args()
    now = datetime.now(timezone.utc)
    output = args.output or Path("runs") / (now.strftime("%Y%m%dT%H%M%S.%fZ") + ".json")
    if not output.is_absolute():
        output = ROOT / output
    if output.exists():
        parser.error(f"Refusing to overwrite an existing evidence record: {output}")

    env = os.environ.copy()
    env["ELAN_HOME"] = str((ROOT / ".elan").resolve())
    env["XDG_CACHE_HOME"] = str((ROOT / ".cache").resolve())
    env["PATH"] = str((ROOT / ".elan/bin").resolve()) + os.pathsep + env["PATH"]
    sources = [ROOT / "MathResearch.lean", *sorted((ROOT / "MathResearch").rglob("*.lean"))]
    inputs = sources + [ROOT / "lean-toolchain", ROOT / "lakefile.toml",
                       ROOT / "lake-manifest.json", *sorted((ROOT / "scripts").glob("*.*"))]
    inputs = [p for p in inputs if p.is_file()]
    before = {str(p.relative_to(ROOT)): fingerprint(p) for p in inputs}
    record = {
        "schema_version": 1,
        "started_utc": now.isoformat(),
        "scope": "Local Lean declarations; correspondence with written mathematics is explained separately.",
        "build_mode": "clean-local" if args.clean_local else "incremental",
        "dependency_artifacts": "Pinned upstream release caches retained; not rebuilt from source.",
        "source_sha256": before,
        "platform": platform.platform(),
        "python_version": platform.python_version(),
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "commands": [],
        "declarations": [],
        "status": "failed",
    }

    def run(command):
        print("Running:", " ".join(command), flush=True)
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        record["commands"].append({"argv": command, "exit_code": result.returncode,
                                   "output": result.stdout})
        print(result.stdout, end="", flush=True)
        if result.returncode:
            raise RuntimeError(f"Command failed ({result.returncode}): {' '.join(command)}")
        return result.stdout.strip()

    try:
        record["repository_head"] = run(["git", "rev-parse", "HEAD"])
        record["lean_version"] = run(["lean", "--version"])
        record["lake_version"] = run(["lake", "--version"])
        record["elan_version"] = run(["elan", "--version"])
        if not (ROOT / "lake-manifest.json").is_file():
            raise RuntimeError("Missing dependency lockfile. Run scripts/setup.sh first.")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        record["dependency_pins"] = {p["name"]: p.get("rev") for p in manifest["packages"]}
        record["dependency_heads"] = {}
        for name, pin in record["dependency_pins"].items():
            package_dir = f".lake/packages/{name}"
            actual = run(["git", "-C", package_dir, "rev-parse", "HEAD"])
            record["dependency_heads"][name] = actual
            if actual != pin:
                raise RuntimeError(f"Installed dependency {name} differs from the lockfile")
            run(["git", "-C", package_dir, "diff", "--exit-code", "HEAD", "--"])
        # Explicit module targets avoid silently omitting a file not imported by the root.
        modules = [".".join(p.relative_to(ROOT).with_suffix("").parts) for p in sources]
        if args.clean_local:
            build_dir = ROOT / ".lake/build"
            if build_dir.is_symlink():
                raise RuntimeError("Refusing to clean a symlinked local build directory")
            if build_dir.exists():
                shutil.rmtree(build_dir)
            record["local_build_cleaned"] = True
            print("Removed local .lake/build; upstream dependency artifacts retained.", flush=True)
        run(["lake", *(["--verbose"] if args.verbose_build else []), "build", *modules])
        audit = ROOT / ".lake" / "MathResearchAudit.lean"
        audit.write_text("module\n\n" + "".join(f"import all {module}\n" for module in modules)
                         + (ROOT / "scripts/Audit.lean").read_text())
        record["audit_source_sha256"] = fingerprint(audit)
        audit_output = run(["lake", "env", "lean", "-DwarningAsError=true",
                            str(audit.relative_to(ROOT))])
        rows = [json.loads(line[len(PREFIX):]) for line in audit_output.splitlines()
                if line.startswith(PREFIX)]
        record["declarations"] = sorted(rows, key=lambda row: row["declaration"])
        if not rows or not any(row["kind"] == "theorem" for row in rows):
            raise RuntimeError("Audit did not report any project theorems")
        if any(row["unexpected_axioms"] for row in rows):
            raise RuntimeError("Audit reported additional axioms")
        if before != {str(p.relative_to(ROOT)): fingerprint(p) for p in inputs}:
            raise RuntimeError("Formal source or configuration changed during verification")
        record["status"] = "passed"
    except (OSError, ValueError, KeyError, RuntimeError) as exc:
        record["error"] = str(exc)
        print(str(exc), file=sys.stderr)
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        print(f"Evidence: {output}")
    return 0 if record["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
