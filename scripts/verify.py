#!/usr/bin/env python3
"""Check local Lean evidence and report an unfinished main proof as incomplete.

This script never submits to Palomar and is not Comparator or NanoDa.
Exit 0: local proof gate passed (external checks still needed).
Exit 1: a local build/audit/layout check failed.
Exit 2: the checked core passed but the original main proof is incomplete.
"""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def run(args: list[str], name: str) -> str:
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True,
                            encoding="utf-8", errors="replace")
    text = result.stdout + result.stderr
    (OUT / name).write_text(text, encoding="utf-8")
    require(result.returncode == 0, f"{' '.join(args)} failed; see verification/{name}")
    return text


def axioms(text: str) -> dict[str, list[str]]:
    return {name: [a.strip() for a in body.split(",") if a.strip()]
            for name, body in re.findall(
                r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)}


def lean_code(text: str) -> str:
    """Remove nested Lean comments and strings for the supplementary source scan."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i):
                depth -= 1; i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1; i += 2; out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1; break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def main() -> int:
    OUT.mkdir(exist_ok=True)
    report = {"checked_at": dt.datetime.now(dt.timezone.utc).isoformat(),
              "status": "failed", "core": "not_checked", "full_target": "not_checked",
              "comparator": "not_run", "nanoda": "not_run",
              "rendering": "not_run", "editorial_review": "not_requested",
              "registration": "not_requested"}
    exit_code = 1
    try:
        config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8-sig"))
        require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
                "Challenge and Solution must be separate modules")
        require(config["theorem_names"] == ["MI32.main_upper"], "The original target must be retained")
        require(set(config["permitted_axioms"]) == ALLOWED, "Only standard foundations are permitted")
        require(config.get("definition_names", []) == [], "No unspecified definitions are permitted")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
        for package in manifest["packages"]:
            require(package["type"] == "git", "Local-path dependency is not portable")
            require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]) is not None, "Unpinned dependency")
            require(re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+",
                                 package["url"]) is not None, "Invalid dependency URL")
        require(sum((ROOT / p).exists() for p in ("lakefile.lean", "lakefile.toml")) == 1,
                "Exactly one root Lakefile is required")
        challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8-sig")
        require(len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000,
                "Challenge exceeds the Palomar size cap")
        imports = re.findall(r"^import\s+(\S+)", lean_code(challenge), re.M)
        require(imports and all(m.startswith("Mathlib.") or m == "Mathlib" for m in imports),
                "Challenge must import only Mathlib modules")
        statement = (ROOT / "MI32/Statement.lean").read_text(encoding="utf-8-sig")
        require(challenge.startswith(statement.rsplit("end MI32", 1)[0]),
                "Challenge definitions differ from the implementation statement")
        core_files = sorted((ROOT / "MI32").glob("*.lean")) + [ROOT / "MI32.lean"]
        core_files += sorted((ROOT / "vendor").rglob("*.lean"))
        forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")
        for path in core_files:
            code = lean_code(path.read_text(encoding="utf-8-sig"))
            require(not forbidden.search(code), f"Proof escape in {path.relative_to(ROOT)}")
            require(not re.search(r"^import\s+(Challenge|Solution)\b", code, re.M),
                    "Completed core must not import the unfinished target")
        for item in json.loads((ROOT / "vendor/graph-matrices/manifest.json").read_text(encoding="utf-8-sig"))["copied_modules"]:
            require(sha(ROOT / "vendor/graph-matrices" / item["path"]) == item["sha256"],
                    "Vendored source differs from its recorded provenance")
        report["layout"] = "passed_local_checks"
        report["lean_version"] = run(["lake", "env", "lean", "--version"], "lean-version.log").strip()
        # Build every first-party proof source explicitly, including a newly
        # added module not yet imported by the root. A source hash alone does
        # not show that Lean checked that file.
        core_targets = ["MI32"] + [
            p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
            for p in sorted((ROOT / "MI32").glob("*.lean"))]
        run(["lake", "build", *core_targets], "core-build.log")
        report["checked_core_modules"] = core_targets
        core_audit = axioms(run(["lake", "env", "lean", "Audit.lean"], "core-axioms.log"))
        wanted = re.findall(r"^#print axioms (\S+)", (ROOT / "Audit.lean").read_text(encoding="utf-8-sig"), re.M)
        require(set(core_audit) == set(wanted), "Core axiom audit did not report every requested theorem")
        require(all(set(values) <= ALLOWED for values in core_audit.values()),
                "Core theorem depends on an unpermitted axiom")
        report["core"] = "passed"
        report["core_axioms"] = core_audit
        run(["lake", "build", "Challenge", "Solution"], "target-elaboration.log")
        target_audit = axioms(run(["lake", "env", "lean", "FullTargetAudit.lean"], "full-target-axioms.log"))
        require("MI32.main_upper" in target_audit, "Full target audit is missing")
        report["full_target_axioms"] = target_audit["MI32.main_upper"]
        solution_code = lean_code((ROOT / "Solution.lean").read_text(encoding="utf-8-sig"))
        report["solution_sorry_count"] = len(re.findall(r"\bsorry\b", solution_code))
        if set(target_audit["MI32.main_upper"]) <= ALLOWED:
            report.update(status="local_proof_gate_passed", full_target="passed_local_axiom_audit")
            exit_code = 0
        else:
            report.update(status="incomplete", full_target="unproved",
                          reason="The original MI-32 theorem depends on sorryAx; do not submit as a completed proof.")
            exit_code = 2
    except Exception as error:
        report["error"] = str(error)
    source_paths = []
    for directory, dirs, filenames in os.walk(ROOT, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".lake", ".git", "__pycache__", "verification"}]
        source_paths.extend(Path(directory) / name for name in filenames)
    report["source_sha256"] = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(source_paths)}
    (OUT / "status.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k not in {"source_sha256", "core_axioms"}}, indent=2))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
