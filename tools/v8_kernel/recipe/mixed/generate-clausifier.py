#!/usr/bin/env python3
"""Emit actual clausifier equations preserving observed clause and literal order."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.


def literal(g, value):
    positive, predicate, arguments = value
    return '⟨' + str(positive).lower() + ', ' + str(predicate) + '#u32, ' + g.vec([g.term(arg) for arg in arguments]) + '⟩'


def emit(g, render_nnf, removal, witness, namespace):
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', namespace), 'Invalid namespace')
    modules = {}
    for index, (formula, block) in enumerate(zip(witness['skolem']['formulas'], witness['blocks'])):
        erased = removal.without_universals(g, formula)
        clauses = g.vec([g.vec([literal(g, value) for value in clause]) for clause in block['clauses']])
        code = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Observed clauses and counters are untrusted; Lean checks the actual call. -/\n'
        code += f'import BooleanClausifierPrimitives\nimport {namespace}Removal{index}\nopen Aeneas Aeneas.Std\nnamespace {namespace}\n'
        code += 'set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
        code += f'def block{index} : fang_fof_core.Preprocessed :=\n  ⟨{clauses}, ⟨' + ', '.join(str(n) + '#usize' for n in block['clausifier_stats']) + '⟩⟩\n'
        code += f'theorem clausify{index}_eq : fang_fof_core.nnf_entry.clausify_nnf_from\n    (FangQuantifiedPipeline.removedNnf removed{index}.formula) FangQuantifiedKernel.Clausifier.limits\n    FangOriginalReplay.initialStatistics = .ok (.Ok block{index}) := by\n'
        code += f'  change fang_fof_core.nnf_entry.clausify_nnf_from {render_nnf(g, erased)}\n    FangQuantifiedKernel.Clausifier.limits FangOriginalReplay.initialStatistics = .ok (.Ok block{index})\n'
        code += f'  simp only [block{index}]\n  generated_boolean_clausifier\n'
        code += f'#print axioms {namespace}.clausify{index}_eq\nend {namespace}\n'
        modules[namespace + 'Clausify' + str(index)] = code
    return modules
