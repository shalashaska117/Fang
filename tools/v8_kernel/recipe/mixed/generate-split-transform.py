#!/usr/bin/env python3
"""Suggest bounded private states, then emit equations for the actual calls.

The Python traversal is untrusted witness construction. Every emitted step
must compile in Lean, and the final result must match the retained observation.
This first slice accepts only literal leaves under universal/existential prefixes.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from copy import deepcopy


def initial_state(witness):
    return {
        'functions': [arity for _, arity in witness['functions']], 'introduced': [], 'entries': [],
        'active': 0, 'declaration': 0,
        'work': [sum(v['validated'][0] + 1 for v in witness['standalone'])
                 + len(witness['functions']) + len(witness['predicates']),
                 sum(v['validated'][3] for v in witness['standalone'])
                 + len(witness['functions']) + len(witness['predicates'])],
    }


def suggest(witness):
    nodes, declarations = [], []
    state = initial_state(witness)

    def cost(work, operations=0, stored=0):
        work[0] += operations
        work[1] += stored
        if work[0] > 5000000 or work[1] > 1000000:
            raise ValueError('Suggested state exceeds the declared replay limits')

    def copy_term(term, work):
        cost(work, 1, 1)
        if term[0] == 'fun':
            for child in term[2]:
                copy_term(child, work)
        elif term[0] != 'var':
            raise ValueError('Unknown term constructor')
        return deepcopy(term)

    def substitute_term(term, binder, replacement, work):
        cost(work, 1)
        if term[0] == 'var' and term[1] == binder:
            return copy_term(replacement, work)
        cost(work, stored=1)
        if term[0] == 'var':
            return deepcopy(term)
        if term[0] != 'fun':
            raise ValueError('Unknown term constructor')
        return ['fun', term[1], [substitute_term(c, binder, replacement, work) for c in term[2]]]

    def substitute(formula, binder, replacement, active, work):
        cost(work, 1, 1)
        if formula[0] == 'literal':
            polarity, predicate, args = formula[1]
            changed = [substitute_term(t, binder, replacement, work) if active else copy_term(t, work)
                       for t in args]
            return ['literal', [polarity, predicate, changed]]
        if formula[0] in ('all', 'ex'):
            return [formula[0], formula[1], substitute(formula[2], binder, replacement,
                    active and formula[1] != binder, work)]
        if formula[0] in ('truth', 'falsity'):
            return deepcopy(formula)
        if formula[0] in ('conj', 'disj'):
            return [formula[0], substitute(formula[1], binder, replacement, active, work),
                    substitute(formula[2], binder, replacement, active, work)]
        raise ValueError('Unsupported Skolem substitution constructor')

    def transform(formula, current):
        if len(nodes) >= 128:
            raise ValueError('Private-state suggestion limit exceeded')
        index = len(nodes)
        node = {'index': index, 'input': deepcopy(formula), 'before': deepcopy(current)}
        nodes.append(node)
        cost(current['work'], 1)
        node['ticked'] = current['work'][:]
        kind = formula[0]
        if kind in ('literal', 'truth', 'falsity'):
            cost(current['work'], stored=1)
            for term in (formula[1][2] if kind == 'literal' else []):
                copy_term(term, current['work'])
            value = deepcopy(formula)
        elif kind in ('conj', 'disj'):
            cost(current['work'], stored=1)
            node['allocated'] = current['work'][:]
            left, left_value = transform(formula[1], current)
            right, right_value = transform(formula[2], current)
            node['left'], node['right'] = left, right
            value = [kind, left_value, right_value]
        elif kind == 'all':
            cost(current['work'], stored=1)
            node['allocated'] = current['work'][:]
            cost(current['work'], 1)
            active = current['active']
            if active < len(current['entries']):
                current['entries'][active] = formula[1]
            else:
                cost(current['work'], stored=1)
                current['entries'].append(formula[1])
            current['active'] += 1
            node['pushed'] = deepcopy(current)
            child, value = transform(formula[2], current)
            node['child'] = child
            current['active'] -= 1
            value = ['all', formula[1], value]
        elif kind == 'ex':
            cost(current['work'], 1, 3)
            dependencies = current['entries'][:current['active']]
            cost(current['work'], len(dependencies), 2 * len(dependencies))
            function = len(current['functions'])
            replacement = ['fun', function, [['var', n] for n in dependencies]]
            current['functions'].append(current['active'])
            current['introduced'].append([current['declaration'], formula[1], function, dependencies])
            node['replacement'] = replacement
            node['introduced'] = deepcopy(current)
            substituted = substitute(formula[2], formula[1], replacement, True, current['work'])
            node['substituted'] = substituted
            node['substitutedWork'] = current['work'][:]
            child, value = transform(substituted, current)
            node['child'] = child
        else:
            raise ValueError('Unsupported Skolem transform constructor')
        node['value'], node['after'] = deepcopy(value), deepcopy(current)
        return index, value

    values = []
    for index, observation in enumerate(witness['standalone']):
        declaration = {'index': index, 'before': deepcopy(state)}
        cost(state['work'], 1)
        declaration['ticked'] = state['work'][:]
        stats = observation['normalized_stats']
        cost(state['work'], stats[0], stats[3])
        declaration['absorbed'] = state['work'][:]
        root, value = transform(observation['normalized'], state)
        declaration['root'] = root
        values.append(value)
        cost(state['work'], stored=1)
        state['declaration'] += 1
        declaration['after'] = deepcopy(state)
        declarations.append(declaration)
    observed = witness['skolem']
    if (values != observed['formulas'] or state['functions'] != observed['functions']
            or state['introduced'] != observed['introduced'] or state['work'] != observed['statistics']):
        raise ValueError('Suggested private states do not match the observed public result')
    return nodes, declarations


def emit(g, render_nnf, witness, namespace):
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', namespace), 'Invalid namespace')
    nodes, declarations = suggest(witness)
    common = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Suggested private states are untrusted; Lean checks actual generated calls. -/\n'
    intro = f'open Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'

    def work(value):
        return '⟨⟨' + str(value[0]) + '#usize, ' + str(value[1]) + '#usize⟩⟩'

    def universals(value):
        return '⟨' + g.vec([str(n) + '#u32' for n in value['entries']]) + ', ' + str(value['active']) + '#usize⟩'

    def state(value):
        origins = ['⟨' + str(d) + '#usize, ' + str(b) + '#u32, ' + str(f) + '#u32, '
                   + g.vec([str(n) + '#u32' for n in us]) + '⟩' for d, b, f, us in value['introduced']]
        return ('⟨' + g.vec([str(n) + '#usize' for n in value['functions']]) + ', '
                + g.vec(origins) + ', ' + universals(value) + ', ' + str(value['declaration'])
                + '#usize, ' + work(value['work']) + '⟩')

    data_name = namespace + 'TransformData'
    data = common + f'import {namespace}Preparation\nimport BooleanTransformComposition\n' + intro
    for node in nodes:
        n = str(node['index'])
        for field in ('before', 'after', 'pushed', 'introduced'):
            if field in node:
                data += f'def t{n}_{field} : fang_skolem_core.Transformer := {state(node[field])}\n'
        for field in ('ticked', 'allocated', 'substitutedWork'):
            if field in node:
                data += f'def t{n}_{field} : fang_skolem_core.Work := {work(node[field])}\n'
        for field in ('input', 'value', 'substituted'):
            if field in node:
                data += f'def t{n}_{field} : fang_skolem_core.fang_quantified_fof_core.Nnf := {render_nnf(g, node[field])}\n'
        if 'replacement' in node:
            data += f'def t{n}_replacement : fang_skolem_core.fang.syntax.Term := {g.term(node["replacement"])}\n'
    data += f'end {namespace}\n'
    modules = {data_name: data}
    audits = {data_name: []}
    for node in reversed(nodes):
        n, kind = str(node['index']), node['input'][0]
        name = namespace + 'Transform' + n
        imports = [data_name]
        if 'child' in node:
            imports.append(namespace + 'Transform' + str(node['child']))
        if 'left' in node:
            imports.extend(namespace + 'Transform' + str(node[key]) for key in ('left', 'right'))
        code = common + ''.join('import ' + name + '\n' for name in imports) + intro
        if kind == 'ex':
            code += f'theorem t{n}_introduce : fang_skolem_core.Transformer.introduce\n  {{ t{n}_before with work := t{n}_ticked }} {node["input"][1]}#u32 skolemLimits =\n  .ok (.Ok t{n}_replacement, t{n}_introduced) := by\n'
            code += f'  simp only [t{n}_before, t{n}_ticked, t{n}_replacement, t{n}_introduced]\n  generated_transform\n'
            code += f'theorem t{n}_substitute : fang_skolem_core.substitute_nnf\n  {render_nnf(g, node["input"][2])} {node["input"][1]}#u32 t{n}_replacement true skolemLimits t{n}_introduced.work =\n  .ok (.Ok t{n}_substituted, t{n}_substitutedWork) := by\n'
            code += f'  simp only [t{n}_replacement, t{n}_introduced, t{n}_substituted, t{n}_substitutedWork]\n  generated_transform\n'
        code += f'theorem t{n}_transform : fang_skolem_core.Transformer.transform t{n}_before t{n}_input skolemLimits =\n  .ok (.Ok t{n}_value, t{n}_after) := by\n'
        if kind in ('literal', 'truth', 'falsity'):
            code += f'  simp only [t{n}_before, t{n}_input, t{n}_value, t{n}_after]\n  generated_transform\n'
        elif kind == 'all':
            c = str(node['child'])
            code += f'  exact FangKernelGenerator.transform_forall_of_parts\n    (before := t{n}_before) (ticked := t{n}_ticked) (allocated := t{n}_allocated)\n    (pushed := t{n}_pushed.universals) (pushedWork := t{n}_pushed.work)\n    (changed := t{c}_after) (popped := t{n}_after.universals)\n'
            for fields in (('before', 'ticked'), ('ticked', 'allocated'), ('before', 'allocated', 'pushed')):
                code += '    (by simp only [' + ', '.join(f't{n}_{field}' for field in fields) + ']; reduce_transform_primitives)\n'
            code += f'    t{c}_transform\n    (by simp only [t{c}_after, t{n}_after]; reduce_transform_primitives)\n'
        elif kind == 'ex':
            code += f'  exact FangKernelGenerator.transform_exists_of_parts\n    (before := t{n}_before) (ticked := t{n}_ticked)\n    (by simp only [t{n}_before, t{n}_ticked]; reduce_transform_primitives)\n    t{n}_introduce t{n}_substitute t{node["child"]}_transform\n'
        elif kind in ('conj', 'disj'):
            rule = 'and' if kind == 'conj' else 'or'
            code += f'  exact FangKernelGenerator.transform_{rule}_of_parts\n    (before := t{n}_before) (ticked := t{n}_ticked) (allocated := t{n}_allocated)\n'
            for fields in (('before', 'ticked'), ('ticked', 'allocated')):
                code += '    (by simp only [' + ', '.join(f't{n}_{field}' for field in fields) + ']; reduce_transform_primitives)\n'
            code += f'    t{node["left"]}_transform t{node["right"]}_transform\n'
        theorem_names = [f'{namespace}.t{n}_' + field for field in
                         (('introduce', 'substitute', 'transform') if kind == 'ex' else ('transform',))]
        code += ''.join('#print axioms ' + name + '\n' for name in theorem_names)
        code += f'end {namespace}\n'
        modules[name], audits[name] = code, theorem_names
    return modules, audits, nodes, declarations
