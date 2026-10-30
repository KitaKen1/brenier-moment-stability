#!/usr/bin/env python3
"""Check that the publication's specification copies and proof packaging agree."""
from pathlib import Path
import json
import re
from make_lean4web import code_mask
from make_fc_statement import check_vocabulary, compact_signature, theorem_signature, statements, ORIGINAL_NAME

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
TOOLCHAIN = "leanprover/lean4:v4.34.1"
MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"


def main():
    config = json.loads((LEAN / "ComparatorChallenges/BrenierMomentStability.json").read_text())
    if set(config["permitted_axioms"]) != {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit("Unexpected permitted axioms")
    model = (LEAN / "BrenierMoment/Presentation/Model.lean").read_text()
    vocabulary = model.split("-- BEGIN MODEL\n", 1)[1].split("-- END MODEL", 1)[0].strip()
    fc = (ROOT / "FClikelean/BrenierMomentStability.lean").read_text()
    check_vocabulary(fc, model)
    proof = (LEAN / "BrenierMoment/FCPresentation.lean").read_text()
    proved_signatures = {name: signature for _, name, signature, _ in statements(proof)}
    for theorem in config["theorem_names"]:
        name = theorem.rsplit(".", 1)[-1]
        expected = compact_signature(name, proved_signatures[name], model)
        if " ".join(theorem_signature(fc, name).split()) != " ".join(expected.split()):
            raise SystemExit(f"FC statement differs from the compact proved theorem: {name}")
    fc_names = re.findall(r"^theorem (\w+)\b", fc, re.M)
    target_names = [name.rsplit(".", 1)[-1] for name in config["theorem_names"]]
    if sorted(fc_names) != sorted([ORIGINAL_NAME, *target_names]):
        raise SystemExit("The FC draft must contain the original result and the three variant targets")
    # The Lean code quoted in the root README is the code of the sources.
    quoted = [" ".join(block.split()) for block in
              re.findall(r"```lean\n(.*?)```", (ROOT / "README.md").read_text(), re.S)]
    for theorem in config["theorem_names"]:
        name = theorem.rsplit(".", 1)[-1]
        found = re.search(r"^theorem " + name + r"\b(.*?):=", proof.split(
            "\nnamespace BrenierStability\n", 1)[1], re.M | re.S)
        if " ".join(("theorem " + name + found.group(1)).split()) not in quoted:
            raise SystemExit(f"The README quotes another statement of {name}")
    # A full definition listing is optional in the README. If one is quoted, it must
    # still agree with the model; FC definitions are checked independently above.
    quotes_definitions = any(re.search(r"\b(?:abbrev|def)\s", block) for block in quoted)
    if quotes_definitions and " ".join(re.sub(
            r"/--.*?-/\n", "", vocabulary + "\n", flags=re.S).split()) not in quoted:
        raise SystemExit("The README quotes other definitions than the model")
    for project in ("lean", "lean4web", "leanWithoutComparator"):
        if (ROOT / project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise SystemExit(f"Unexpected toolchain: {project}")
    generated = ROOT / "lean4web/BrenierMomentStabilityLean4Web.lean"
    code = code_mask(generated.read_text())
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
        raise SystemExit("Hole, additional axiom or native_decide in the single-file proof")
    imports = re.findall(r"^import (\S+)\s*$", code, re.M)
    generated_manifest = json.loads((ROOT / "lean4web/sources.json").read_text())
    if imports != generated_manifest["output_imports"] or any(
            module != "Mathlib" and not module.startswith(("Mathlib.", "Aesop.", "Lean.", "Batteries."))
            for module in imports):
        raise SystemExit(f"Unexpected single-file imports: {imports}")
    for path in (ROOT / "lean4web/lake-manifest.json", LEAN / "lake-manifest.json",
                 ROOT / "leanWithoutComparator/lake-manifest.json"):
        lock = json.loads(path.read_text())
        if any(package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"])
               for package in lock["packages"]):
            raise SystemExit(f"Unpinned or local dependency in {path}")
        mathlib = next(package for package in lock["packages"] if package["name"] == "mathlib")
        if mathlib["rev"] != MATHLIB:
            raise SystemExit(f"Unexpected Mathlib revision in {path}")
    print("Publication checks passed: FC vocabulary/signatures, Comparator axioms, pinned "
          "dependencies and hole-free single-file proof")


if __name__ == "__main__":
    main()
