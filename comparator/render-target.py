#!/usr/bin/env python3
"""Render the FC targets with the proved model's expanded helper definitions."""
from pathlib import Path
import argparse
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
PATH = 'FClikelean/BrenierMomentStability.lean'
CHALLENGE = 'lean/ComparatorChallenges/BrenierMomentStability.lean'
NAMESPACE = 'BrenierStability'
TARGETS = ['moment_stability', 'moment_rate_sharp', 'no_modulus_at_second_moment']
sys.path.insert(0, str(ROOT / 'lean/scripts'))
from make_fc_statement import check_vocabulary, compact_signature, model_vocabulary, statements, theorem_signature
IMPORTS = """import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity"""

def generated():
    text = (ROOT / PATH).read_text()
    if text.count('  sorry\n') != len(TARGETS) + 1:
        raise ValueError('Expected one hole for the original result and one for each variant target')
    model = (ROOT / 'lean/BrenierMoment/Presentation/Model.lean').read_text()
    proof = (ROOT / 'lean/BrenierMoment/FCPresentation.lean').read_text()
    check_vocabulary(text, model)
    body = (f'namespace {NAMESPACE}\n\nnoncomputable section\n'
            'open MeasureTheory\nopen scoped ENNReal\n\n' + model_vocabulary(model))
    for doc, name, signature, _ in statements(proof):
        if name not in TARGETS or text.count('theorem ' + name + ' ') != 1:
            raise ValueError('Expected exactly one statement of ' + name)
        fc_signature = theorem_signature(text, name)
        expected = compact_signature(name, signature, model)
        if ' '.join(fc_signature.split()) != ' '.join(expected.split()):
            raise ValueError('FC statement differs from the proved theorem: ' + name)
        body += f'\n{doc}theorem {name}{signature} := by\n  sorry\n'
    body += f'\nend\n\nend {NAMESPACE}\n'
    return {CHALLENGE: IMPORTS + '\n\n' + body}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    for name, content in generated().items():
        path = ROOT / name
        if args.check:
            if path.read_text() != content:
                raise SystemExit('Generated file differs: ' + name)
        else:
            path.write_text(content)
    print('Expanded FC mathematical body checked.' if args.check else 'Challenge generated.')
