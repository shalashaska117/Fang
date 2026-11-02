#!/usr/bin/env python3
"""Emit actual removal equations from the sealed Skolem output witnesses."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.


def without_universals(g, value):
    # This only suggests an expected result. The emitted equation checks the
    # unchanged remover on the complete input, including every universal node.
    while value[0] == 'all':
        value = value[2]
    if value[0] in ('literal', 'truth', 'falsity'):
        return value
    g.require(value[0] in ('conj', 'disj'), 'Unsupported removal witness constructor')
    return [value[0], without_universals(g, value[1]), without_universals(g, value[2])]


def emit(g, render_nnf, witness, namespace):
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', namespace), 'Invalid namespace')
    modules = {}
    for index, (formula, block) in enumerate(zip(witness['skolem']['formulas'], witness['blocks'])):
        erased = without_universals(g, formula)
        code = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Expected erasure and counters are untrusted; Lean checks the actual call. -/\n'
        code += f'import RemovalPrimitives\nimport {namespace}Encoded\nopen Aeneas Aeneas.Std\nnamespace {namespace}\n'
        code += 'set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
        code += f'def skolemOutput{index} : fang_skolem_core.fang_quantified_fof_core.Nnf :=\n  {render_nnf(g, formula)}\n'
        code += f'def removed{index} : fang_binder_removal_core.Removed :=\n  ⟨{render_nnf(g, erased)}, ⟨' + ', '.join(str(n) + '#usize' for n in block['removal_stats']) + '⟩⟩\n'
        code += f'theorem remove{index}_eq : fang_binder_removal_core.remove_universals\n    (FangQuantifiedPipeline.skolemNnf skolemOutput{index}) FangKernelGenerator.removalLimits =\n    .ok (.Ok removed{index}) := by\n'
        code += f'  change fang_binder_removal_core.remove_universals {render_nnf(g, formula)}\n    FangKernelGenerator.removalLimits = .ok (.Ok removed{index})\n  simp only [removed{index}]\n  generated_removal\n'
        code += f'#print axioms {namespace}.remove{index}_eq\nend {namespace}\n'
        modules[namespace + 'Removal' + str(index)] = code
    return modules
