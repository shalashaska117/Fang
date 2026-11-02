#!/usr/bin/env python3
"""Extend the frozen input slice with checked rectification and NNF goals."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import hashlib
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'evidence/verification/fof-kernel-generator-draft-v15-20261023'
EXPECTED = 'ad51b80526139c9592086366bb488f5e37926c8cb39ca0b9b874e05c023e8c15'


def base_generator():
    import json
    assert hashlib.sha256((BASE / 'manifest.json').read_bytes()).hexdigest() == EXPECTED
    manifest = json.loads((BASE / 'manifest.json').read_text())
    path = BASE / 'generate.py'
    expected = next(value for key, value in manifest['input_helper_tool_sha256'].items() if key.endswith('/kernel-generator/generate.py'))
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected
    spec = importlib.util.spec_from_file_location('frozen_generator', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def statistics(values):
    return '⟨' + ', '.join(str(value) + '#usize' for value in values) + '⟩'


def retained_bindings(value):
    """Suggest the exact inactive stack; the actual rectifier equation checks it."""
    entries, active, fresh = [], 0, 0
    def visit(node):
        nonlocal active, fresh
        if node[0] in ('all', 'ex'):
            binding = (node[1], fresh)
            fresh += 1
            if active < len(entries):
                entries[active] = binding
            else:
                entries.append(binding)
            active += 1
            visit(node[2])
            active -= 1
        elif node[0] == 'not':
            visit(node[1])
        elif node[0] in ('conj', 'disj', 'implies'):
            visit(node[1])
            visit(node[2])
        elif node[0] not in ('atom', 'truth', 'falsity'):
            raise ValueError('Unsupported rectification witness shape')
    visit(value)
    return entries, fresh


def nnf(g, value):
    if value[0] in ('truth', 'falsity'):
        return '(.' + {'truth': 'True', 'falsity': 'False'}[value[0]] + ')'
    if value[0] in ('conj', 'disj'):
        return '(.' + {'conj': 'And', 'disj': 'Or'}[value[0]] + ' ' + nnf(g, value[1]) + ' ' + nnf(g, value[2]) + ')'
    if value[0] == 'literal':
        positive, predicate, arguments = value[1]
        literal = '⟨' + str(positive).lower() + ', ' + str(predicate) + '#u32, ' + g.vec([g.term(arg) for arg in arguments]) + '⟩'
        return '(.Literal ' + literal + ')'
    if value[0] in ('all', 'ex'):
        return '(.' + {'all': 'Forall', 'ex': 'Exists'}[value[0]] + ' ' + str(value[1]) + '#u32 ' + nnf(g, value[2]) + ')'
    raise ValueError('Unsupported NNF constructor')


def emit(g, witness, namespace):
    common = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Observed outputs are untrusted witnesses; Lean checks actual generated calls. -/\n'
    intro = 'open Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nopen fang_skolem_core.fang_quantified_fof_core\nnamespace ' + namespace + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    modules = {}
    for index, (declaration, observed) in enumerate(zip(witness['declarations'], witness['standalone'])):
        rectified = f'rectified{index}'
        count = observed['binder_count']
        bindings, suggested_count = retained_bindings(declaration['formula'])
        if suggested_count != count:
            raise ValueError('Observed binder count differs from suggested frame traversal')
        stack = '⟨' + g.vec(['⟨' + str(original) + '#u32, ' + str(fresh) + '#u32⟩' for original, fresh in bindings]) + ', 0#usize⟩'
        code = common + f'import TransformPrimitives\nimport {namespace}Validate{index}\n' + intro
        code += f'def {rectified} : Formula :=\n  {g.formula(observed["rectified"])}\n'
        code += f'def rectifiedStats{index} : Statistics := {statistics(observed["rectified_stats"])}\n'
        code += f'theorem rectify{index}_body :\n  rectify_formula formula{index} ⟨alloc.vec.Vec.new _, 0#usize⟩ 0#u32 skolemLimits.core\n    ⟨{statistics(observed["validated"])}⟩ =\n  .ok (.Ok {rectified}, {stack}, {count}#u32, ⟨rectifiedStats{index}⟩) := by\n'
        code += f'  simp only [formula{index}, {rectified}, rectifiedStats{index}]\n  generated_transform\n'
        code += f'theorem rectify{index}_eq : rectify_closed formula{index} signature skolemLimits.core =\n    .ok (.Ok ⟨{rectified}, {count}#u32, rectifiedStats{index}⟩) :=\n  FangQuantifiedKernel.rectify_closed_of_parts _ _ _ _ _ _ _ _ validate{index}_eq rectify{index}_body\n'
        code += f'#print axioms {namespace}.rectify{index}_body\n#print axioms {namespace}.rectify{index}_eq\nend {namespace}\n'
        modules[namespace + 'Rectify' + str(index)] = code
        code = common + f'import {namespace}Rectify{index}\n' + intro
        code += f'def normalized{index} : Nnf :=\n  {nnf(g, observed["normalized"])}\n'
        code += f'def normalizedStats{index} : Statistics := {statistics(observed["normalized_stats"])}\n'
        code += f'theorem normalize{index}_body : normalize_formula {rectified} true skolemLimits.core ⟨rectifiedStats{index}⟩ =\n    .ok (.Ok normalized{index}, ⟨normalizedStats{index}⟩) := by\n'
        code += f'  simp only [{rectified}, rectifiedStats{index}, normalized{index}, normalizedStats{index}]\n  generated_transform\n'
        code += f'theorem normalize{index}_eq : rectify_normalize_closed formula{index} true signature skolemLimits.core =\n    .ok (.Ok ⟨normalized{index}, normalizedStats{index}⟩) := by\n  simp only [rectify_normalize_closed, rectify{index}_eq, bind_ok,\n    core.result.Result.Insts.CoreOpsTry.branch, normalize{index}_body, Aeneas.Std.uncurry]\n'
        code += f'#print axioms {namespace}.normalize{index}_body\n#print axioms {namespace}.normalize{index}_eq\nend {namespace}\n'
        modules[namespace + 'Normalize' + str(index)] = code
    return modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--witness', type=Path, required=True)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--namespace', required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    g = base_generator()
    source = g.read_bounded(args.input, g.MAX_SOURCE)
    certificate = g.read_bounded(args.certificate, g.MAX_CERTIFICATE)
    witness = g.validate(g.read_bounded(args.witness, g.MAX_WITNESS), source, certificate)
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', args.namespace), 'Invalid namespace')
    args.out.mkdir(parents=True, exist_ok=False)
    for name, code in emit(g, witness, args.namespace).items():
        (args.out / (name + '.lean')).write_bytes(code.encode('utf-8'))


if __name__ == '__main__':
    main()
