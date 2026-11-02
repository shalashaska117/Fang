#!/usr/bin/env python3
"""Compose checked actual calls and the same sealed version-6 proof bytes."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.


def term(value):
    if value[0] == 'var':
        return '(.var ' + str(value[1]) + ')'
    return '(.app ' + str(value[1]) + ' [' + ', '.join(term(arg) for arg in value[2]) + '])'


def literal(value):
    return '⟨' + str(value[0]).lower() + ', ' + str(value[1]) + ', [' + ', '.join(term(arg) for arg in value[2]) + ']⟩'


def emit(g, witness, namespace):
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', namespace), 'Invalid namespace')
    count = len(witness['blocks'])
    common = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Generated actual-call composition for the sealed input/certificate pair. -/\n'
    intro = f'namespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    code = common + f'import {namespace}Decoded\nimport OriginalCertificateInput\n' + intro
    blocks = ['[' + ', '.join('[' + ', '.join(literal(lit) for lit in clause) + ']' for clause in block['clauses']) + ']' for block in witness['blocks']]
    code += 'def clauseBlocks : List Fang.Problem := [' + ', '.join(blocks) + ']\n'
    clauses, block_index = [], 0
    for declaration in witness['source_declarations']:
        kind, body = declaration['body']
        if kind == 'cnf':
            clauses.append(body)
        else:
            clauses.extend(witness['blocks'][block_index]['clauses'])
            block_index += 1
    g.require(block_index == count, 'Mixed assembly block count')
    code += 'def assembledClauses : Fang.Problem := [' + ', '.join('[' + ', '.join(literal(lit) for lit in clause) + ']' for clause in clauses) + ']\n'
    code += 'def prepared : Fang.DecodedProblem :=\n  ⟨Fang.preprocess assembledClauses, ' + str(witness['skolem']['functions']) + ', ' + str(witness['skolem']['predicates']) + '⟩\n'
    code += 'theorem prepared_certificate_checked : FangOriginalCertificate.checkPrepared prepared certificateBytes = .ok true := by cbv\n'
    code += f'#print axioms {namespace}.prepared_certificate_checked\nend {namespace}\n'
    modules = {namespace + 'Certificate': code}
    code = common + f'import {namespace}Skolem\nimport {namespace}Certificate\n' + ''.join(f'import {namespace}Clausify{i}\n' for i in range(count)) + 'import OriginalCertificate\nimport ReplayComposition\nopen Aeneas Aeneas.Std\n' + intro
    projection = code + 'set_option linter.unusedSimpArgs false\n'
    projection += 'theorem output_list_eq : skolemized.formulas.val = [' + ', '.join('skolemOutput' + str(i) for i in range(count)) + '] := rfl\n'
    projection += f'#print axioms {namespace}.output_list_eq\n'
    projection += 'theorem decoded_blocks_eq : [' + ', '.join('FangScopedFof.decodeClauses block' + str(i) + '.clauses.val' for i in range(count)) + '] = clauseBlocks := by\n'
    projection += '  simp [' + ''.join('block' + str(i) + ', ' for i in range(count)) + 'clauseBlocks,\n    FangScopedFof.decodeClauses, FangScopedFof.clauseLists, FangScopedFof.decodeLiteral,\n    FangScopedFof.decodeVec, FangQuantifiedKernel.vector, alloc.vec.Vec.val,\n    Slice.from, Slice.val, Aeneas.Data.ListN.ListN.toList, FangScopedFof.decodeSlice, Aeneas.Data.ListN.ListN.fromList,\n    FangScopedFof.decodeTerms, FangScopedFof.decodeTerm]\n'
    projection += f'#print axioms {namespace}.decoded_blocks_eq\n'
    for table in ('function', 'predicate'):
        projection += f'theorem {table}_arities_eq : skolemized.signature.{table}s.val.map (fun value => value.val) = prepared.{table}Arities := by\n'
        projection += '  simp [skolemized, prepared, FangQuantifiedKernel.vector, alloc.vec.Vec.val]\n'
        projection += f'#print axioms {namespace}.{table}_arities_eq\n'
    projection += f'end {namespace}\n'
    modules[namespace + 'Projection'] = projection
    code = common + f'import {namespace}Projection\nimport RemovalPrimitives\nimport QuantifiedClausifierKernel\nopen Aeneas Aeneas.Std\n' + intro
    code += 'def replayLimits : FangOriginalReplay.Limits := {\n  skolem := FangOriginalKernelProbe.skolemLimits\n  removal := FangKernelGenerator.removalLimits\n  clausification := FangQuantifiedKernel.Clausifier.limits }\n'
    code += 'theorem replay_blocks_eq : FangOriginalReplay.replayBlocks replayLimits skolemized.formulas.val = .ok clauseBlocks := by\n'
    code += '  rw [output_list_eq, ← decoded_blocks_eq]\n'
    code += '  have tailRun : FangOriginalReplay.replayBlocks replayLimits [] = .ok [] := rfl\n'
    for index in reversed(range(count)):
        rest = '[' + ', '.join('skolemOutput' + str(i) for i in range(index + 1, count)) + ']'
        tails = '[' + ', '.join('FangScopedFof.decodeClauses block' + str(i) + '.clauses.val' for i in range(index + 1, count)) + ']'
        code += f'  have step{index} := FangKernelGenerator.replay_blocks_cons\n    (limits := replayLimits) (formula := skolemOutput{index}) (rest := {rest})\n    (removed := removed{index}) (output := block{index}) (blocks := {tails})\n    remove{index}_eq clausify{index}_eq ' + ('tailRun' if index == count - 1 else f'step{index + 1}') + '\n'
    code += '  exact ' + ('step0' if count else 'tailRun') + '\n'
    code += 'theorem assemble_eq : FangOriginalReplay.assemble decoded.declarations clauseBlocks = .ok prepared.problem := by\n  simp [FangOriginalReplay.assemble, decoded, clauseBlocks, prepared, assembledClauses, Fang.preprocess]\n'
    code += 'theorem prepare_eq : FangOriginalReplay.prepare input replayLimits = .ok prepared := by\n'
    code += '  have result := FangKernelGenerator.prepare_of_parts (input := input) (limits := replayLimits)\n    (decoded := decoded) (encoded := encoded) (transformed := skolemized)\n    (blocks := clauseBlocks) (problem := prepared.problem)\n    decode_eq encode_eq skolemize_eq replay_blocks_eq assemble_eq\n  rw [function_arities_eq, predicate_arities_eq] at result\n  exact result\n'
    code += 'theorem certificate_accepts : FangOriginalCertificate.accepts input certificateBytes replayLimits = .ok true := by\n  exact FangKernelGenerator.certificate_accepts_of_parts (input := input)\n    (bytes := certificateBytes) (limits := replayLimits) (prepared := prepared)\n    prepare_eq prepared_certificate_checked\n'
    code += 'theorem certificate_original_unsat :\n    ¬ Fang.NamedQuantified.Grammar.BytesSatisfiable (Fang.Source.Grammar.spelling input) :=\n  FangOriginalCertificate.accepts_original_unsat (input := input) (proof := certificateBytes)\n    (limits := replayLimits) certificate_accepts\n'
    code += ''.join(f'#print axioms {namespace}.{name}\n' for name in ('replay_blocks_eq', 'assemble_eq', 'prepare_eq', 'certificate_accepts', 'certificate_original_unsat'))
    code += f'end {namespace}\n'
    blocks_end = code.index('theorem assemble_eq')
    assembly_end = code.index('theorem prepare_eq')
    audits_start = code.index('#print axioms')
    modules[namespace + 'Blocks'] = code[:blocks_end] + f'#print axioms {namespace}.replay_blocks_eq\nend {namespace}\n'
    modules[namespace + 'Assembly'] = common + f'import {namespace}Blocks\n' + intro + code[blocks_end:assembly_end] + f'#print axioms {namespace}.assemble_eq\nend {namespace}\n'
    prepare_end = code.index('theorem certificate_accepts')
    modules[namespace + 'Prepare'] = common + f'import {namespace}Assembly\n' + intro + code[assembly_end:prepare_end] + f'#print axioms {namespace}.prepare_eq\nend {namespace}\n'
    modules[namespace + 'Replay'] = common + f'import {namespace}Prepare\n' + intro + code[prepare_end:audits_start] + ''.join(f'#print axioms {namespace}.{name}\n' for name in ('certificate_accepts', 'certificate_original_unsat')) + f'end {namespace}\n'
    return modules
