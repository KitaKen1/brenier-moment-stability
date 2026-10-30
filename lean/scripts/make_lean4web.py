#!/usr/bin/env python3
"""Generate a Mathlib-only, single-file edition of the complete proof.

The source graph is visited in dependency order. Each original file is put in a
section to preserve its local instances, options, variables and open namespaces.
Module-system headers are removed. Private identifiers are renamed only if two
sources declare the same name. All definitions, statements and proofs are retained.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
OUTPUT = ROOT / "lean4web/BrenierMomentStabilityLean4Web.lean"
MANIFEST = ROOT / "lean4web/sources.json"
ROOT_MODULE = "BrenierMoment"
SOURCE_DIRECTORIES = ("", "vendor/openai")
FINAL_THEOREMS = [
    "BrenierStability.moment_stability",
    "BrenierStability.moment_rate_sharp",
    "BrenierStability.no_modulus_at_second_moment",
    "BrenierMoment.moment_stability",
    "BrenierMoment.moment_rate_sharp",
    "BrenierMoment.no_modulus_at_second_moment",
    "BrenierMoment.moment_rate_two_sided",
]
DECLARATION = (r"(?:noncomputable\s+)?(?:def|lemma|theorem|abbrev|instance|structure|inductive|class)")
# In the modular build a module sees only what it imports. In one file it also sees every
# earlier source, and a short name can then resolve to a declaration of a deeper namespace
# that the module never imported. Such references are qualified here; nothing else changes.
# module -> [(text, replacement, number of occurrences, description)]
SHADOWED = ("Inside the namespace CellGeometry the short name would resolve to "
            "CellGeometry.eventually_injective_sites of FixedMass.lean, which this module does not "
            "import. The reference is qualified so that it names "
            "OAI.Problem358.eventually_injective_sites, as in the modular build.")
ADJUSTMENTS = {
    "OAI.Analysis.Brenier.CellContinuity": [
        ("eventually_injective_sites y c hinj",
         "_root_.OAI.Problem358.eventually_injective_sites y c hinj", 2, SHADOWED)],
    "OAI.Analysis.Brenier.CanonicalLaplacian": [
        ("eventually_injective_sites y c hy",
         "_root_.OAI.Problem358.eventually_injective_sites y c hy", 1, SHADOWED)],
}


def code_mask(text):
    """Blank nested comments and strings, preserving offsets and newlines."""
    result = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text[i:i + 2] == "/-":
                depth += 1
                result[i:i + 2] = "  "
                i += 2
            elif text[i:i + 2] == "-/":
                depth -= 1
                result[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                result[i:i + 2] = "  "
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif text[i:i + 2] == "/-":
            depth = 1
            result[i:i + 2] = "  "
            i += 2
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            string = True
            result[i] = " "
            i += 1
        else:
            i += 1
    return "".join(result)


def source_path(module):
    relative = Path(*module.split(".")).with_suffix(".lean")
    for directory in SOURCE_DIRECTORIES:
        candidate = LEAN / directory / relative
        if candidate.is_file():
            return candidate
    return None


def collect():
    """Sources in dependency order, and the external modules they import."""
    sources, external, seen, active = [], set(), set(), set()

    def visit(module):
        if module in active:
            raise ValueError(f"Import cycle at {module}")
        if module in seen:
            return
        path = source_path(module)
        if path is None:
            if not module.startswith(("Mathlib", "Lean", "Batteries", "Aesop")):
                raise ValueError(f"Missing source for {module}")
            external.add(module)
            return
        active.add(module)
        original = path.read_text()
        masked = code_mask(original)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", masked):
            raise ValueError(f"Proof hole or additional axiom in {path}")
        for dependencies in re.findall(r"^(?:(?:public|private) )?import (.+)$", masked, re.M):
            for dependency in dependencies.split():
                visit(dependency)
        active.remove(module)
        seen.add(module)
        body_lines = []
        for line, code in zip(original.splitlines(), masked.splitlines()):
            if re.match(r"^(?:(?:public|private) )?import\b|^module\s*$|"
                        r"^(?:@\[expose\] )?public section\s*$", code):
                continue
            body_lines.append(line)
        body = "\n".join(body_lines).strip()
        if re.search(r"^\s*(?:public|meta)\s|@\[expose\]|\bimport all\b", code_mask(body), re.M):
            raise ValueError(f"Module-system syntax left in the body of {path}")
        adjustments = []
        for text, replacement, count, description in ADJUSTMENTS.get(module, []):
            if len(re.findall(r"(?<![\w.])" + re.escape(text), body)) != count:
                raise ValueError(f"Expected {count} occurrence(s) of {text!r} in {path}")
            body = re.sub(r"(?<![\w.])" + re.escape(text), lambda _: replacement, body)
            adjustments.append({"text": text, "replacement": replacement, "occurrences": count,
                                "reason": description})
        sources.append({"module": module, "path": path.relative_to(LEAN).as_posix(),
                        "source_sha256": hashlib.sha256(original.encode()).hexdigest(),
                        "proof_adjustments": adjustments,
                        "body": body})

    visit(ROOT_MODULE)
    unused = set(ADJUSTMENTS) - {source["module"] for source in sources}
    if unused:
        raise ValueError(f"Adjustments for modules that are not included: {sorted(unused)}")
    return sources, external


def rename_colliding_private_names(sources):
    """A private name is file-local in a module but not in one combined file."""
    declared = {}
    for index, source in enumerate(sources):
        code = code_mask(source["body"])
        source["private_names"] = re.findall(r"\bprivate\s+" + DECLARATION + r"\s+(\S+)", code)
        for name in re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)?" + DECLARATION
                               + r"\s+(\S+)", code, re.M):
            declared.setdefault(name.rsplit(".", 1)[-1], set()).add(index)
    for index, source in enumerate(sources):
        source["private_renames"] = {}
        for name in source["private_names"]:
            leaf = name.rsplit(".", 1)[-1]
            if declared[leaf] == {index}:
                continue
            new = f"{name}_lean4web_{index}"
            source["private_renames"][name] = new
            source["body"] = re.sub(r"(?<![\w'.])" + re.escape(leaf) + r"(?![\w'])",
                                    f"{leaf}_lean4web_{index}", source["body"])
        del source["private_names"]


def generate():
    sources, external = collect()
    rename_colliding_private_names(sources)
    for source in sources:
        scopes = []
        for line in code_mask(source["body"]).splitlines():
            start = re.match(r"^\s*(?:noncomputable )?(section|namespace)\b\s*(.*)$", line)
            if start:
                scopes.append(start.group(2).strip())
            elif re.match(r"^\s*end(?:\s+\S+)?\s*$", line):
                if not scopes:
                    raise ValueError(f"Unmatched end in {source['path']}: {line}")
                scopes.pop()
        closing = "".join("end" + (" " + name if name else "") + "\n" for name in reversed(scopes))
        source["content"] = (f"-- BEGIN SOURCE: {source['path']}\n"
                             "section\n" + source["body"] + "\n" + closing + "end\n"
                             f"-- END SOURCE: {source['path']}\n")
    # The upstream modules rely on the umbrella import, so it is kept.
    output_imports = ["Mathlib"]
    header = "\n".join("import " + module for module in output_imports) + '''

/-!
# Sharp moment stability of Brenier maps: complete single-file proof

Generated by lean/scripts/make_lean4web.py. All project sources and the adapted
sources from openai/math needed by the proof are included below; only Mathlib is
imported. The pinned environment is recorded in lean4web/lean-toolchain and
lean4web/lake-manifest.json. No compatibility with a different Mathlib version
is implied. See lean4web/README.md for the hosted Lean4Web status.

The sources under vendor/openai are adapted from openai/math, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0); see lean/VENDOR.json.
Changes for this edition: import and module headers removed, and each source
enclosed in a section. Definitions and statements are unchanged. In two proofs
a reference is written with its full name, because in one file the short name
would resolve to a declaration that the original module does not import. These
adjustments and any renamed private identifier are listed per source in
sources.json. Apache-2.0.
-/

set_option autoImplicit false

'''
    audit = "\n" + "".join(f"#print axioms {name}\n" for name in FINAL_THEOREMS)
    content = header + "\n".join(source["content"] for source in sources) + audit
    manifest = {"root_module": ROOT_MODULE, "module_count": len(sources),
                "line_count": len(content.splitlines()),
                "external_imports_encountered": sorted(external),
                "output_imports": output_imports,
                "final_theorems": FINAL_THEOREMS,
                "packaging": "Import and module-system header lines are removed and each source is "
                             "enclosed in a section, with its open namespaces and sections closed at "
                             "the end. The umbrella Mathlib import of the upstream modules is the only "
                             "import. A private identifier is renamed only when another source declares "
                             "the same name. A reference is qualified where the short name would "
                             "resolve, in one file, to a declaration that the original module does not "
                             "import; each such change is listed under proof_adjustments. No "
                             "definition, statement or axiom is added or changed.",
                "output": OUTPUT.relative_to(ROOT).as_posix(),
                "output_sha256": hashlib.sha256(content.encode()).hexdigest(),
                "sources": [{k: v for k, v in source.items() if k not in ("content", "body")}
                            for source in sources]}
    return content, json.dumps(manifest, ensure_ascii=False, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check the committed output")
    args = parser.parse_args()
    content, manifest = generate()
    if args.check:
        if OUTPUT.read_text() != content or MANIFEST.read_text() != manifest:
            raise SystemExit("Lean4Web output is stale; run lean/scripts/make_lean4web.py")
        print("Lean4Web source and provenance match the project")
    else:
        OUTPUT.write_text(content)
        MANIFEST.write_text(manifest)
        print(f"Generated {OUTPUT.name}: {len(content.splitlines())} lines")


if __name__ == "__main__":
    main()
