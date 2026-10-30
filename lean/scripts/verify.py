#!/usr/bin/env python3
"""Build the project and reject nonstandard transitive axioms in the audited results.

With --static only the source-level checks are run: the recorded hashes of the adapted upstream
sources, the agreement of the statement vocabulary and of the three statements with the
Comparator challenge, and the absence of proof holes. Nothing is built and no record is written.
"""
from pathlib import Path
import argparse
import json
import re
import subprocess
import sys
import hashlib
from datetime import datetime, timezone
from check_blueprint import check_blueprint, listed_in_audit_files
from make_lean4web import code_mask

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--static", action="store_true", help="source-level checks only; no build")
args = parser.parse_args()
ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / "verification"
LOG.mkdir(exist_ok=True)
allowed = {"propext", "Classical.choice", "Quot.sound"}
results = []
NAMESPACE = "BrenierStability"
CONFIG = "ComparatorChallenges/BrenierMomentStability.json"
CHALLENGE = "ComparatorChallenges/BrenierMomentStability.lean"
MODEL = "BrenierMoment/Presentation/Model.lean"
PRESENTATION = "BrenierMoment/FCPresentation.lean"
ORIGINAL_THEOREMS = ["BrenierMoment.moment_stability", "BrenierMoment.moment_rate_sharp",
                     "BrenierMoment.no_modulus_at_second_moment"]

# The adapted upstream sources must be the recorded ones, with nothing added or missing.
vendor = json.loads((ROOT / "VENDOR.json").read_text())["openai_math"]
vendor_root = ROOT / "vendor/openai"
for module, expected in vendor["sha256"].items():
    source = vendor_root / (module.replace(".", "/") + ".lean")
    if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != expected:
        raise SystemExit(f"Vendored source changed: {source}")
present = {path.relative_to(vendor_root).with_suffix("").as_posix().replace("/", ".")
           for path in vendor_root.rglob("*.lean")}
if present != set(vendor["sha256"]):
    raise SystemExit(f"Vendored file set changed: {sorted(present ^ set(vendor['sha256']))}")

# The Mathlib-only statements must use one vocabulary: the definitions of the solution-side
# model and of the Comparator challenge are the same text, both import the same Mathlib
# modules and nothing else, and each challenge theorem is stated exactly as the one that is
# proved.
comparator = json.loads((ROOT / CONFIG).read_text())
challenge = (ROOT / CHALLENGE).read_text()
model = (ROOT / MODEL).read_text()
presentation = (ROOT / PRESENTATION).read_text()


def vocabulary(text):
    return text.split(f"namespace {NAMESPACE}\n", 1)[1].split("-- END MODEL", 1)[0]


def statement(text, leaf):
    found = re.search(r"^theorem " + re.escape(leaf) + r"\b(.*?):=", text, re.S | re.M)
    if not found:
        raise SystemExit(f"Statement not found: {leaf}")
    return " ".join(found.group(1).split())


# The challenge is generated from the Formal Conjectures draft and carries no markers.
if not challenge.split(f"namespace {NAMESPACE}\n", 1)[1].startswith(
        vocabulary(model).replace("-- BEGIN MODEL\n", "", 1)):
    raise SystemExit("The Comparator challenge and the model define different vocabularies")
model_imports = re.findall(r"^public import (\S+)", model, re.M)
challenge_imports = re.findall(r"^import (\S+)", challenge, re.M)
if model_imports != challenge_imports or not model_imports or any(
        not module.startswith("Mathlib.") for module in model_imports):
    raise SystemExit("Both statement vocabularies must use the same explicit Mathlib imports")
if re.findall(r"^(?:private )?import (\S+)", model, re.M):
    raise SystemExit("The model must import its dependencies publicly")
if set(comparator["permitted_axioms"]) != allowed:
    raise SystemExit("Unexpected permitted axioms in the Comparator configuration")
if (comparator["challenge_module"] != "ComparatorChallenges.BrenierMomentStability" or
        comparator["solution_module"] != "BrenierMoment.FCPresentation" or
        comparator["definition_names"]):
    raise SystemExit("Unexpected Comparator configuration")
proved_statements = presentation.split(f"\nnamespace {NAMESPACE}\n", 1)[1]
for theorem in comparator["theorem_names"]:
    namespace, leaf = theorem.rsplit(".", 1)
    if namespace != NAMESPACE or statement(challenge, leaf) != statement(proved_statements, leaf):
        raise SystemExit(f"Challenge and proved statement differ: {theorem}")

# These modules must never contain holes or extra axioms. The challenge is not among them.
proof_sources = (sorted((ROOT / "BrenierMoment").rglob("*.lean")) + [ROOT / "BrenierMoment.lean"]
                 + sorted(vendor_root.rglob("*.lean")))
for source in proof_sources:
    code = code_mask(source.read_text())
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
        raise SystemExit(f"Proof hole or axiom in {source.relative_to(ROOT)}")
    if re.search(r"^(?:public |private )?import ComparatorChallenges\b", code, re.M):
        raise SystemExit(f"{source.relative_to(ROOT)} imports the Comparator challenge")

if args.static:
    ledger = check_blueprint(listed_in_audit_files())
    print(f"Source-level checks passed: {len(vendor['sha256'])} adapted upstream sources match their "
          f"recorded hashes, the challenge and the model share one vocabulary and "
          f"{len(comparator['theorem_names'])} statements, {len(proof_sources)} proof sources "
          f"contain no hole or axiom, and the ledger has {ledger['nodes']} nodes whose "
          f"{ledger['audited_lean_witnesses']} witnesses are declared and listed for the axiom audit. "
          "Nothing was built.")
    sys.exit(0)

for name, cmd in [("build", ["lake", "build", "BrenierMoment", "OAI.Analysis.Brenier.Stability"]),
                  ("challenge", ["lake", "build", "ComparatorChallenges"]),
                  ("fc-model", [sys.executable, "scripts/verify_fc_statement.py"]),
                  ("axioms", ["lake", "env", "lean", "Audit.lean"]),
                  ("fc-axioms", ["lake", "env", "lean", "FCAudit.lean"]),
                  ("statement", ["lake", "env", "lean", "--run", "scripts/CompareStatement.lean",
                                 CONFIG])]:
    p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    (LOG / f"{name}.log").write_text(p.stdout)
    print(p.stdout, end="", flush=True)
    results.append({"step": name, "command": cmd, "exit_code": p.returncode})
    if p.returncode:
        sys.exit(p.returncode)


def reports(log_name, source_name):
    """Axiom reports of one audit file; every `#print axioms` line must have exactly one."""
    log = (LOG / log_name).read_text()
    if re.search(r"\berror:", log):
        raise SystemExit(f"Lean errors in {log_name}")
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    entries += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    expected = re.findall(r"^#print axioms (\S+)", (ROOT / source_name).read_text(), re.M)
    if sorted(n for n, _ in entries) != sorted(expected):
        raise SystemExit(f"Missing or unexpected transitive axiom reports in {log_name}")
    for theorem, text in entries:
        axioms = {v.strip() for v in text.split(",") if v.strip()}
        if axioms - allowed:
            raise SystemExit(f"Unexpected axioms for {theorem}: {sorted(axioms - allowed)}")
    return entries


entries = reports("axioms.log", "Audit.lean")
fc_entries = reports("fc-axioms.log", "FCAudit.lean")
audited = dict(entries) | dict(fc_entries)
blueprint_check = check_blueprint(audited)
missing = [name for name in ORIGINAL_THEOREMS + comparator["theorem_names"] if name not in audited]
if missing:
    raise SystemExit(f"Final theorems missing from the axiom audit: {missing}")

record = {"verified_utc": datetime.now(timezone.utc).isoformat(),
          "steps": results, "axiom_audit": audited,
          "target_status": "proved: the upper bound BrenierMoment.moment_stability, sharpness "
                           "BrenierMoment.moment_rate_sharp and the endpoint "
                           "BrenierMoment.no_modulus_at_second_moment, and the three Mathlib-only "
                           "statements of the namespace BrenierStability derived from them; hosted "
                           "CI, the leanprover/comparator run and publication are separate checks",
          "original_theorems": ORIGINAL_THEOREMS,
          "mathlib_only_statements": {
              "theorems": comparator["theorem_names"],
              "challenge_module": comparator["challenge_module"],
              "solution_module": comparator["solution_module"],
              "vocabulary_text_identical": True,
              "statement_comparison": "passed in scripts/CompareStatement.lean; this follows the "
                                      "checks of leanprover/comparator but is not that tool"},
          "vendored_sources_matched": len(vendor["sha256"]),
          "blueprint_check": blueprint_check,
          "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip()}
(LOG / "result.json").write_text(json.dumps(record, indent=2) + "\n")
sources = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "VENDOR.json",
           "BrenierMoment.lean", "Audit.lean", "FCAudit.lean", CHALLENGE, CONFIG]
sources += sorted(str(f.relative_to(ROOT)) for f in (ROOT / "scripts").iterdir() if f.is_file())
sources += sorted(str(f.relative_to(ROOT)) for f in (ROOT / "BrenierMoment").rglob("*.lean"))
sources += sorted(str(f.relative_to(ROOT)) for f in vendor_root.rglob("*.lean"))
hashes = {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in sources}
(LOG / "source-sha256.json").write_text(json.dumps(
    {"verified_utc": record["verified_utc"], "source_sha256": hashes}, indent=2, ensure_ascii=False) + "\n")
print(f"Verified build and {len(audited)} transitive axiom reports. "
      "The three theorems and the Mathlib-only statements are proved.")
