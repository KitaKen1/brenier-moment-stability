#!/usr/bin/env python3
"""Check the compact FC definitions, variant types and OpenAI's original result.

The FC import and metadata are omitted. No statement is assumed or left unproved: the
generated file checks the three variant types by `rfl` against the compiled Mathlib-only
model and derives the original compact-target statement directly from OpenAI's theorem.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import subprocess
from make_fc_statement import (check_vocabulary, fc_vocabulary, compact_signature, statements, DEFINITION_DOCS,
                               ORIGINAL_NAME, ORIGINAL_SIGNATURE, theorem_signature)

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
FC = ROOT / "FClikelean/BrenierMomentStability.lean"
MODEL = LEAN / "BrenierMoment/Presentation/Model.lean"
PROOF = LEAN / "BrenierMoment/FCPresentation.lean"
NAMESPACE = "BrenierFCCheck"


def statement_def(name, signature):
    binders, proposition = signature.split(":\n", 1)
    return f"def fcCheck_{name}{binders}: Prop :=\n{proposition}\n"


def check_source(report_original_axioms=True):
    fc = FC.read_text()
    model = MODEL.read_text()
    check_vocabulary(fc, model)
    vocabulary = fc_vocabulary(fc)
    public_statements = statements(PROOF.read_text())
    fc_types, proof_types = [], []
    for _, name, signature, _ in public_statements:
        fc_signature = theorem_signature(fc, name)
        expected = compact_signature(name, signature, model)
        if " ".join(fc_signature.split()) != " ".join(expected.split()):
            raise ValueError("FC statement differs from the proved theorem: " + name)
        fc_types.append(statement_def(name, fc_signature))
        proof_types.append(statement_def(name, signature))
    opening = "\nnoncomputable section\nopen MeasureTheory\nopen scoped ENNReal\n\n"
    original = (f"theorem fcCheck_{ORIGINAL_NAME}{ORIGINAL_SIGNATURE} := by\n"
                "  exact OAI.Problem358.one_third_stability d K Y hd hK hKc hKn hY hYn\n")
    source = ("import BrenierMoment.Presentation.Model\n"
              "import OAI.Analysis.Brenier.Stability\n\n"
              f"namespace {NAMESPACE}" + opening + vocabulary + "\n" + "\n".join(fc_types)
              + "\n" + original
              + f"\nend\nend {NAMESPACE}\n\nnamespace BrenierStability" + opening
              + "\n".join(proof_types) + "\nend\nend BrenierStability\n\n")
    for name in [*DEFINITION_DOCS, *("fcCheck_" + name for _, name, _, _ in public_statements)]:
        source += f"example : @{NAMESPACE}.{name} = @BrenierStability.{name} := rfl\n"
    if report_original_axioms:
        source += f"#print axioms {NAMESPACE}.fcCheck_{ORIGINAL_NAME}\n"
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="Lean binary; defaults to lake env lean")
    parser.add_argument("--model-lib", type=Path, help="Read-only compiled model search directory")
    parser.add_argument("--cache", action="append", type=Path, default=[],
                        help="Read-only pinned Mathlib search directory")
    parser.add_argument("--skip-original-axiom-report", action="store_true",
                        help="Omit the repeated axiom report; still derive the original theorem")
    args = parser.parse_args()
    log_dir = LEAN / "verification"
    log_dir.mkdir(exist_ok=True)
    source = log_dir / "FCModelCheck.lean"
    source.write_text(check_source(not args.skip_original_axiom_report))
    env = os.environ.copy()
    search = ([args.model_lib] if args.model_lib else []) + args.cache
    if search:
        env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in search)
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    command += ["-DautoImplicit=false", str(source)]
    run = subprocess.run(command, cwd=LEAN, env=env, text=True, capture_output=True)
    output = run.stdout + run.stderr
    (log_dir / "fc-model.log").write_text(output)
    record = {
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "command": command,
        "exit_code": run.returncode,
        "status": "passed" if run.returncode == 0 else "failed",
        "definition_equalities": len(DEFINITION_DOCS),
        "statement_type_equalities": len(statements(PROOF.read_text())),
        "original_result_proof": "OAI.Problem358.one_third_stability",
        "original_axioms_reported": not args.skip_original_axiom_report,
        "input_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in (FC, MODEL, PROOF, Path(__file__))},
        "scope": "Lean checks the compact definitions and three variant types against the "
                 "compiled Mathlib-only model by rfl, and derives the original result from "
                 "OpenAI's one_third_stability. The FormalConjecturesUtil import and "
                 "metadata are omitted; FC checkout compatibility is not checked.",
    }
    (log_dir / "fc-model.json").write_text(json.dumps(record, indent=2) + "\n")
    if run.returncode:
        print(output)
        raise SystemExit(run.returncode)
    print(f"Compact FC model passed: {len(DEFINITION_DOCS)} definition equalities, 3 variant-type equalities by rfl "
          "and the original compact-target result derived from OpenAI's proof.")


if __name__ == "__main__":
    main()
