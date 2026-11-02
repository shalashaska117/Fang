#!/usr/bin/env python3
"""Compose suggested declaration states with actual generated normalization/loops."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.


def emit(g, render_nnf, split, public, witness, namespace):
    nodes, declarations = split.suggest(witness)
    common = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Suggested private states are checked through the actual declaration loop. -/\n'
    intro = f'open Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'

    def work(value):
        return '⟨⟨' + str(value[0]) + '#usize, ' + str(value[1]) + '#usize⟩⟩'

    def state(value):
        origins = ['⟨' + str(d) + '#usize, ' + str(b) + '#u32, ' + str(f) + '#u32, '
                   + g.vec([str(n) + '#u32' for n in us]) + '⟩' for d, b, f, us in value['introduced']]
        return ('⟨' + g.vec([str(n) + '#usize' for n in value['functions']]) + ', '
                + g.vec(origins) + ', ⟨' + g.vec([str(n) + '#u32' for n in value['entries']])
                + ', ' + str(value['active']) + '#usize⟩, ' + str(value['declaration'])
                + '#usize, ' + work(value['work']) + '⟩')

    data = common + f'import {namespace}TransformData\nimport SkolemLoopKernel\n'
    data += ''.join(f'import {namespace}Normalize{i}\n' for i in range(len(declarations))) + intro
    for d in declarations:
        i = d['index']
        data += f'def loop{i}_before : fang_skolem_core.Transformer := {state(d["before"])}\n'
        data += f'def loop{i}_ticked : fang_skolem_core.Work := {work(d["ticked"])}\n'
        data += f'def loop{i}_remaining : fang_skolem_core.fang_quantified_fof_core.Limits :=\n  {{ skolemLimits.core with max_operations := {5000000 - d["ticked"][0]}#usize, max_stored_nodes := {1000000 - d["ticked"][1]}#usize }}\n'
    count = len(declarations)
    final_state = declarations[-1]['after'] if declarations else split.initial_state(witness)
    data += f'def loop{count}_before : fang_skolem_core.Transformer := {state(final_state)}\n'
    for i in range(count + 1):
        data += f'def loop{i}_outputs : alloc.vec.Vec fang_skolem_core.fang_quantified_fof_core.Nnf := '
        data += g.vec([f't{d["root"]}_value' for d in declarations[:i]]) + '\n'
    data += f'end {namespace}\n'
    modules, audits = {namespace + 'LoopData': data}, {namespace + 'LoopData': []}
    if not declarations:
        name = namespace + 'DeclarationLoop0'
        code = common + f'import {namespace}LoopData\n' + intro
        code += 'theorem loop0_eq : fang_skolem_core.transform_declarations_loop declarations signature skolemLimits\n  loop0_before loop0_outputs = .ok (.Ok loop0_outputs, loop0_before) := by\n'
        code += '  exact FangQuantifiedKernel.declarations_finished declarations signature skolemLimits\n    loop0_before loop0_outputs (by simp [loop0_before, declarations])\n'
        code += f'#print axioms {namespace}.loop0_eq\nend {namespace}\n'
        modules[name], audits[name] = code, [namespace + '.loop0_eq']
    for d in declarations:
        i = d['index']
        name = namespace + f'NormalizeRemaining{i}'
        code = common + f'import {namespace}LoopData\n' + intro
        code += f'theorem normalize_remaining{i} : fang_skolem_core.fang_quantified_fof_core.rectify_normalize_closed\n  formula{i} true signature loop{i}_remaining = .ok (.Ok ⟨normalized{i}, normalizedStats{i}⟩) := by\n'
        code += f'  simp only [formula{i}, signature, loop{i}_remaining, normalized{i}, normalizedStats{i}]\n  generated_transform\n'
        code += f'#print axioms {namespace}.normalize_remaining{i}\nend {namespace}\n'
        modules[name], audits[name] = code, [f'{namespace}.normalize_remaining{i}']
    for d in reversed(declarations):
        i, root = d['index'], d['root']
        name = namespace + f'DeclarationLoop{i}'
        code = common + f'import {namespace}NormalizeRemaining{i}\nimport {namespace}Transform{root}\n'
        if i + 1 < count:
            code += f'import {namespace}DeclarationLoop{i + 1}\n'
        code += intro
        code += f'theorem loop{i}_eq : fang_skolem_core.transform_declarations_loop declarations signature skolemLimits\n  loop{i}_before loop{i}_outputs = .ok (.Ok loop{count}_outputs, loop{count}_before) := by\n'
        code += f'  apply FangQuantifiedKernel.declaration_step declarations signature skolemLimits loop{i}_before\n    loop{i}_outputs ⟨formula{i}, true⟩ loop{i}_ticked loop{i}_remaining\n    ⟨normalized{i}, normalizedStats{i}⟩ t{root}_before.work t{root}_value t{root}_after\n    loop{i + 1}_before.work loop{i + 1}_outputs {i + 1}#usize loop{count}_outputs loop{count}_before\n'
        code += f'  · simp [loop{i}_before, declarations]\n'
        code += f'  · simp only [loop{i}_before, loop{i}_ticked]\n    reduce_transform_primitives\n'
        code += f'  · simp (disch := kernel_scalar) [loop{i}_before, declarations, Slice.index_usize]\n'
        code += f'  · simp only [loop{i}_ticked, loop{i}_remaining]\n    reduce_transform_primitives\n'
        code += f'  · exact normalize_remaining{i}\n'
        code += f'  · simp only [loop{i}_ticked, normalizedStats{i}, t{root}_before]\n    reduce_transform_primitives\n'
        code += f'  · exact t{root}_transform\n'
        code += f'  · simp only [t{root}_after, loop{i + 1}_before]\n    reduce_transform_primitives\n'
        code += f'  · simp only [loop{i}_outputs, loop{i + 1}_outputs]\n    reduce_transform_primitives\n'
        code += f'  · simp only [loop{i}_before]\n    reduce_transform_primitives\n'
        code += f'  · rfl\n'
        if i + 1 < count:
            code += f'  · exact loop{i + 1}_eq\n'
        else:
            code += f'  · exact FangQuantifiedKernel.declarations_finished declarations signature skolemLimits\n      loop{count}_before loop{count}_outputs (by simp [loop{count}_before, declarations])\n'
        code += f'#print axioms {namespace}.loop{i}_eq\nend {namespace}\n'
        modules[name], audits[name] = code, [f'{namespace}.loop{i}_eq']
    result = public.emit(g, render_nnf, witness, namespace)[namespace + 'Skolem']
    result = result.replace(f'import {namespace}Preparation\n', f'import {namespace}DeclarationLoop0\n')
    begin = result.index('  simp only [declarations, signature, preparedWork, skolemized,')
    end = result.index('#print axioms', begin)
    result = result[:begin] + '  unfold fang_skolem_core.transform_declarations\n  erw [loop0_eq]\n  simp only [bind_ok, Aeneas.Std.uncurry]\n'
    result += f'  rfl\n#print axioms {namespace}.skolemize_eq\nend {namespace}\n'
    modules[namespace + 'Skolem'], audits[namespace + 'Skolem'] = result, [namespace + '.skolemize_eq']
    return modules, audits
