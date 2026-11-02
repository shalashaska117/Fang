#!/usr/bin/env python3
"""Emit exact actual Skolem preparation equations from bounded witnesses."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'evidence/verification/fof-kernel-generator-draft-v15-20261023'
BASE_PIN = 'ad51b80526139c9592086366bb488f5e37926c8cb39ca0b9b874e05c023e8c15'


def generator():
    raw = (BASE / 'manifest.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != BASE_PIN:
        raise ValueError('Frozen input generator receipt changed')
    manifest = json.loads(raw)
    path = BASE / 'generate.py'
    expected = next(value for key, value in manifest['input_helper_tool_sha256'].items() if key.endswith('/kernel-generator/generate.py'))
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError('Frozen generator changed')
    spec = importlib.util.spec_from_file_location('frozen_input_generator', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def emit(g, witness, namespace):
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', namespace), 'Invalid namespace')
    # Suggested private counters, not native observations. The emitted equations
    # check the actual calls including all remaining-budget calculations.
    operations = sum(value['validated'][0] + 1 for value in witness['standalone'])
    stored = sum(value['validated'][3] for value in witness['standalone'])
    function_count, predicate_count = len(witness['functions']), len(witness['predicates'])
    common = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Suggested private counters are untrusted; Lean checks each actual call. -/\n'
    code = common + f'import TransformPrimitives\nimport {namespace}Encoded\nopen Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    code += f'def validatedWork : fang_skolem_core.Work := ⟨⟨{operations}#usize, {stored}#usize⟩⟩\n'
    code += 'theorem validate_declarations_eq : fang_skolem_core.validate_declarations declarations signature skolemLimits\n  ⟨⟨0#usize, 0#usize⟩⟩ = .ok (.Ok (), validatedWork) := by\n'
    code += '  simp only [' + ', '.join(['declarations', 'signature', 'validatedWork'] + ['formula' + str(i) for i in range(len(witness['declarations']))]) + ']\n  generated_transform\n'
    code += f'def functionsWork : fang_skolem_core.Work := ⟨⟨{operations + function_count}#usize, {stored + function_count}#usize⟩⟩\n'
    code += 'theorem copy_functions_eq : fang_skolem_core.copy_arities (alloc.vec.Vec.deref signature.functions) skolemLimits validatedWork =\n    .ok (.Ok signature.functions, functionsWork) := by\n  simp only [signature, validatedWork, functionsWork]\n  generated_transform\n'
    code += f'def preparedWork : fang_skolem_core.Work := ⟨⟨{operations + function_count + predicate_count}#usize, {stored + function_count + predicate_count}#usize⟩⟩\n'
    code += 'theorem copy_predicates_eq : fang_skolem_core.copy_arities (alloc.vec.Vec.deref signature.predicates) skolemLimits functionsWork =\n    .ok (.Ok signature.predicates, preparedWork) := by\n  simp only [signature, functionsWork, preparedWork]\n  generated_transform\n'
    code += ''.join(f'#print axioms {namespace}.{name}\n' for name in ('validate_declarations_eq', 'copy_functions_eq', 'copy_predicates_eq'))
    code += f'end {namespace}\n'
    return {namespace + 'Preparation': code}
