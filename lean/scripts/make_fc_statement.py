#!/usr/bin/env python3
"""Write the Formal Conjectures form of the Mathlib-only statements.

The vocabulary is generated from BrenierMoment/Presentation/Model.lean, with transport helpers
inlined, and the theorem statements from BrenierMoment/FCPresentation.lean. The
`formal_proof` links are pinned to the given commit of the public repository and to the current
line numbers of the proved theorems.

The output is a draft until it has been built inside a Formal Conjectures checkout, which pins
another Lean and Mathlib version than this project.
"""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/KitaKen1/brenier-moment-stability"
PLACEHOLDER = "COMMIT_OF_THE_PUBLIC_REPOSITORY"
NAMESPACE = "BrenierStability"
OUTPUT = "FClikelean/BrenierMomentStability.lean"
ATTRIBUTES = "category research solved, AMS 49 60"

HEADER = '''/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import FormalConjecturesUtil

/-!
# Sharp moment stability of Brenier maps

For a log-concave source with bounded support, a power-logarithmic moment bound on one
target gives a sharp modulus of continuity for Brenier maps. A second-moment bound alone
gives no modulus. `original_compact_stability` is OpenAI's result [OAI26];
`moment_stability` is its moment variant [Ki26]. The square-root conjecture [L26] is false.

*References:*
- [L26] C. Letrouit, *Unstable optimal transport maps*, Conjecture 3 (2026).
  https://doi.org/10.5802/crmath.834
- [OAI26] OpenAI, *Sharp One-Third Stability of Brenier Maps* (2026), result 374.
  https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/374.md
- [Ki26] K. Kitamura, *Sharp moment stability of Brenier maps* (2026).
  https://github.com/KitaKen1/brenier-moment-stability
-/

@[expose] public section

namespace BrenierStability

noncomputable section
open MeasureTheory
open scoped ENNReal

'''

DEFINITION_DOCS = {
    "wasserstein": r"The quadratic Wasserstein distance $W_2(\mu,\nu)$.",
    "IsBrenierMap": "A measurable transport map whose graph is the unique optimal quadratic coupling.",
    "moment": r"The moment $\int |y|^p[\log(e+|y|)]^\beta\,d\mu(y)$.",
}
THEOREM_DOCS = {
    "moment_stability": "Variant of `original_compact_stability`: log-concave source, one-sided moment bound,\n"
                        "and moment-dependent rate [Ki26].",
    "moment_rate_sharp": "The modulus is sharp, already for four-atom targets and a uniform box source [Ki26].",
    "no_modulus_at_second_moment": "A second-moment bound alone gives no modulus of continuity for Brenier maps [Ki26].",
}


def expand_space(text):
    return re.sub(r"\bSpace d\b", "EuclideanSpace ℝ (Fin d)", text.replace(
        "Space (d + 2)", "EuclideanSpace ℝ (Fin (d + 2))"))


ORIGINAL_NAME = "original_compact_stability"
ORIGINAL_PROOF_URL = (
    "https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/"
    "lean/OAI/Analysis/Brenier/Stability.lean#L19")
ORIGINAL_SIGNATURE = expand_space(''' {d : ℕ} (hd : 2 ≤ d) {K Y : Set (Space d)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKn : (interior K).Nonempty)
    (hY : IsCompact Y) (hYn : Y.Nonempty) :
    let ρ : Measure (Space d) := (volume K)⁻¹ • volume.restrict K
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ μ ν : Measure (Space d), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        μ (Yᶜ) = 0 → ν (Yᶜ) = 0 →
        ∃ Tμ Tν : Space d → Space d,
          IsBrenierMap ρ μ Tμ ∧ IsBrenierMap ρ ν Tν ∧
          Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ) ≤
            C * wasserstein μ ν ^ (1 / 3 : ℝ)''')


def original_statement():
    return ("/-- OpenAI's sharp compact-target bound, replacing the false square-root conjecture [OAI26]. -/\n"
            f"@[{ATTRIBUTES},\n    formal_proof using lean4 at \"{ORIGINAL_PROOF_URL}\"]\n"
            f"theorem {ORIGINAL_NAME}{ORIGINAL_SIGNATURE} := by\n  sorry\n")


def fc_vocabulary(fc):
    return fc.split("open scoped ENNReal\n\n", 1)[1].split(original_statement(), 1)[0]


def theorem_signature(text, name):
    """Extract an FC stub type; local lets may also contain :=, before the final := by."""
    found = re.search(r"^theorem " + re.escape(name) + r"\b(.*?) := by\b", text, re.M | re.S)
    if not found:
        raise ValueError("Missing theorem: " + name)
    return found.group(1).rstrip()


def model_vocabulary(model):
    return model.split("-- BEGIN MODEL\n", 1)[1].split("-- END MODEL", 1)[0]


def model_declarations(model):
    vocabulary = model_vocabulary(model)
    declarations = {}
    for match in re.finditer(
            r"/--(?:(?!-/).)*-/\n((?:def|abbrev) (\w+)\b.*?)(?=\n\n|\Z)",
            vocabulary, re.S):
        declarations[match.group(2)] = match.group(1)
    if set(declarations) != {"Space", "IsCoupling", "cost", "wasserstein", "graph",
                             "IsBrenierMap", "mapDist", "logConcaveSource", "moment",
                             "modulus", "box", "boxSource", "HasFourAtoms"}:
        raise ValueError("Unexpected model vocabulary")
    return declarations


def compact_vocabulary(model):
    """Keep just the Wasserstein distance, Brenier map and moment."""
    declarations = model_declarations(model)

    def body(name):
        return declarations[name].split(":=\n", 1)[1].strip()

    coupling = body("IsCoupling")
    cost = body("cost")
    graph = body("graph")
    declarations["wasserstein"] = declarations["wasserstein"].replace(
        "IsCoupling μ ν π", "(" + coupling.replace(
            " ∧ Measure.map Prod.fst", " ∧\n      Measure.map Prod.fst") + ")").replace(
        " cost π = r", f"\n      ({cost}) = r")
    signature, optimality = declarations["IsBrenierMap"].split(":=\n", 1)
    coupling = coupling.replace("μ", "ρ").replace("ν", "μ")
    declarations["IsBrenierMap"] = (
        signature + ":=\n"
        "  let cost (π : Measure (Space d × Space d)) : ℝ≥0∞ :=\n    " + cost + "\n"
        "  let graph := " + graph + "\n"
        "  let coupling (π : Measure (Space d × Space d)) : Prop :=\n    " + coupling + "\n"
        + optimality.replace("IsCoupling ρ μ π", "coupling π").replace(
            "(graph ρ T)", "graph").replace("graph ρ T", "graph"))
    return expand_space("\n\n".join(f"/-- {doc} -/\n{declarations[name].rstrip()}"
                                   for name, doc in DEFINITION_DOCS.items()) + "\n")


def compact_signature(name, signature, model):
    """Expand the removed definitions inside the theorem, preserving its type by reduction."""
    declarations = model_declarations(model)
    binders, proposition = signature.split(":\n", 1)
    error = "Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ)"
    rate = lambda delta: (f"({delta} ^ ((p - 2) / (3 * p - 2)) *\n"
                          f"              Real.log (Real.exp 1 / {delta}) ^ (-(2 * β) / (3 * p - 2)))")
    if name == "moment_stability":
        source = declarations["logConcaveSource"].split(":=\n", 1)[1]
        source = source.replace("  (m Set.univ)⁻¹ • m", "  let ρ := (m Set.univ)⁻¹ • m")
        source = "\n".join("  " + line for line in source.splitlines()) + "\n"
        proposition = proposition.replace("(logConcaveSource U V)", "ρ")
        old_bound = ("          (0 < wasserstein μ ν → wasserstein μ ν ≤ δ₀ →\n"
                     "            mapDist ρ Tμ Tν ≤ C * modulus p β (wasserstein μ ν))")
        new_bound = ("          (let δ := wasserstein μ ν\n"
                     "           0 < δ → δ ≤ δ₀ →\n"
                     f"            {error} ≤ C * {rate('δ')})")
        if old_bound not in proposition:
            raise ValueError("Unexpected upper-bound statement")
        proposition = source + proposition.replace(old_bound, new_bound)
    elif name in {"moment_rate_sharp", "no_modulus_at_second_moment"}:
        box = declarations["box"].split(":=\n", 1)[1].strip()
        atoms = declarations["HasFourAtoms"].split(":=\n", 1)[1]
        atoms = atoms.replace("Space d", "Space (d + 2)")
        source = (f"    let B : Set (Space (d + 2)) := {box}\n"
                  "    let ρ : Measure (Space (d + 2)) := (volume B)⁻¹ • volume.restrict B\n"
                  "    let fourAtoms (μ : Measure (Space (d + 2))) : Prop :=\n"
                  + "\n".join("    " + line for line in atoms.splitlines()) + "\n")
        proposition = proposition.replace("(boxSource d)", "ρ").replace("HasFourAtoms", "fourAtoms")
        proposition = proposition.replace("mapDist ρ Tμ Tν", error)
        proposition = proposition.replace("modulus p β δ", rate("δ"))
        proposition = source + proposition
    else:
        raise ValueError("Unexpected variant theorem: " + name)
    return expand_space(binders + ":\n" + proposition)


def check_vocabulary(fc, model):
    """The compact FC definitions must be precisely the generated expansions of the model."""
    definitions = fc_vocabulary(fc)
    if definitions.strip() != compact_vocabulary(model).strip():
        raise ValueError("FC vocabulary differs from the compact proved model")
    if original_statement() not in fc:
        raise ValueError("Original compact-target statement or proof link changed")


def statements(proof):
    """(docstring, name, signature, line) of every theorem of the public namespace."""
    _, public = proof.split(f"\nnamespace {NAMESPACE}\n", 1)
    found = []
    for match in re.finditer(r"(/--(?:(?!-/).)*-/\n)theorem (\w+)\b(.*?):=", public, re.S):
        doc, name, signature = match.groups()
        line = proof[:proof.index("theorem " + name + " ", proof.index(f"\nnamespace {NAMESPACE}\n"))].count("\n") + 1
        found.append((doc, name, signature.rstrip(), line))
    return found


def generate(repository=REPOSITORY, commit=PLACEHOLDER):
    model = (ROOT / "BrenierMoment/Presentation/Model.lean").read_text()
    vocabulary = compact_vocabulary(model)
    proof_file = "BrenierMoment/FCPresentation.lean"
    proof = (ROOT / proof_file).read_text()
    text = HEADER + vocabulary + "\n" + original_statement()
    for _, name, signature, line in statements(proof):
        signature = compact_signature(name, signature, model)
        doc = f"/-- {THEOREM_DOCS[name]} -/\n"
        link = f"{repository.rstrip('/')}/blob/{commit}/lean/{proof_file}#L{line}"
        text += (f"\n{doc}@[{ATTRIBUTES},\n"
                 f"    formal_proof using lean4 at \"{link}\"]\n"
                 f"theorem {name}{signature} := by\n  sorry\n")
    text += f"\nend\n\nend {NAMESPACE}\n"
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", default=PLACEHOLDER,
                        help="commit of the public repository that contains the proof")
    parser.add_argument("--repository", default=REPOSITORY,
                        help="public repository URL containing the proof sources")
    parser.add_argument("--output", default=None,
                        help="file to write; the default is FClikelean/ in the repository root")
    args = parser.parse_args()
    text = generate(args.repository, args.commit)
    output = Path(args.output) if args.output else ROOT.parent / OUTPUT
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"Wrote {output}")
    if args.commit == PLACEHOLDER:
        print("The formal_proof links still carry the commit placeholder.")


if __name__ == "__main__":
    main()
