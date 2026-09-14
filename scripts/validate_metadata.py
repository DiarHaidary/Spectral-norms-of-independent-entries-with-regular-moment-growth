#!/usr/bin/env python3
"""Run the pinned public Palomar metadata contract locally; no submission."""
import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PIN = "ef2fa1eadcb246c2346ddba39b52eaa53d4bb763"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--palomar-submission", required=True, type=Path,
                    help="Local checkout of public PalomarRegistry/PalomarSubmission at the recorded pin")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
checkout = args.palomar_submission.resolve()
revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
if revision != PIN:
    raise SystemExit("Tool checkout differs from the recorded exact pin")
sys.path.insert(0, str(checkout))
from scripts.submission_contract import load_formalization_metadata

metadata = load_formalization_metadata(root / "formalization.yaml")
report = {"status": "passed", "tool_commit": PIN,
          "checked_at": dt.datetime.now(dt.timezone.utc).isoformat(),
          "metadata_sha256": hashlib.sha256((root / "formalization.yaml").read_bytes()).hexdigest(),
          "project": metadata["project"]["name"],
          "scope": "Pinned metadata mechanical minimum only; not proof verification or submission"}
(root / "verification/metadata.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
