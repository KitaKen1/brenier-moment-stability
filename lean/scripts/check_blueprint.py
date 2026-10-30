#!/usr/bin/env python3
"""Check the mathematical DAG and its witnesses against the Lean axiom audit.

The mathematical dependency edges are authored, not extracted Lean imports.
A node with status `lean_verified_conditional` witnesses statements that carry a hypothesis
discharged in a later node.
"""
from pathlib import Path
import json
import re
import unicodedata

ROOT = Path(__file__).resolve().parents[1]
MAIN_WITNESSES = {"BrenierStability.moment_stability", "BrenierStability.moment_rate_sharp",
                  "BrenierStability.no_modulus_at_second_moment"}


def resolve(source):
    """Locate a ledger source below ROOT, in either Unicode normalization form."""
    for form in (None, "NFC", "NFD"):
        candidate = ROOT / (source if form is None else unicodedata.normalize(form, source))
        if candidate.is_file():
            return candidate
    return None


def listed_in_audit_files():
    """The declarations named by `#print axioms` in the two audit files."""
    names = []
    for name in ("Audit.lean", "FCAudit.lean"):
        names += re.findall(r"^#print axioms (\S+)", (ROOT / name).read_text(), re.M)
    return names


def check_blueprint(audited_names):
    manifest = ROOT / "blueprint/dependencies.json"
    data = json.loads(manifest.read_text())
    nodes = data["nodes"]
    ids = [n["id"] for n in nodes]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate Blueprint node")
    by_id = {n["id"]: n for n in nodes}
    audited = set(audited_names)
    seen, active, ordered, witnesses = set(), set(), [], set()

    def visit(key):
        if key in active:
            raise ValueError(f"Blueprint cycle at {key}")
        if key in seen:
            return
        if key not in by_id:
            raise ValueError(f"Missing Blueprint dependency: {key}")
        active.add(key)
        node = by_id[key]
        for dep in node["needs"]:
            visit(dep)
        active.remove(key)
        seen.add(key)
        ordered.append(key)
        if node["source"] and resolve(node["source"]) is None:
            raise ValueError(f"Missing Blueprint source: {key}")
        if node["status"].startswith("lean_verified"):
            refs = node.get("lean_declarations", [])
            if not refs:
                raise ValueError(f"No audited Lean witness: {key}")
            code = resolve(node["source"]).read_text()
            for name in refs:
                if name not in audited:
                    raise ValueError(f"Unaudited Lean witness: {name}")
                leaf = name.rsplit(".", 1)[-1]
                if not re.search(r"\b(?:theorem|lemma)\s+(?:[\w.]*\.)?" + re.escape(leaf) + r"\b", code):
                    raise ValueError(f"Lean witness not declared in source: {name}")
                witnesses.add(name)
        elif node.get("lean_declarations"):
            raise ValueError(f"Open node incorrectly carries completed witnesses: {key}")

    for key in ids:
        visit(key)
    main = by_id["main"]
    if main["status"] != "lean_verified" or not MAIN_WITNESSES <= set(main["lean_declarations"]):
        raise ValueError("The main node must witness the three Mathlib-only statements")
    return {"nodes": len(nodes), "audited_lean_witnesses": len(witnesses),
            "audited_declarations_without_a_node": sorted(set(
                re.findall(r"^#print axioms (\S+)", (ROOT / "Audit.lean").read_text(), re.M)) - witnesses),
            "acyclic": True, "topological_order": ordered,
            "scope": data["scope"]}


if __name__ == "__main__":
    print(json.dumps(check_blueprint(listed_in_audit_files()), indent=2, ensure_ascii=False))
