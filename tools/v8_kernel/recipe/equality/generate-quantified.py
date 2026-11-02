#!/usr/bin/env python3
"""Equality kernel instances: sealed mixed bytes, actual preprocessing and conversion.

All
expected values are bounded suggestions; Lean checks the original decoder,
actual generated calls, mixed assembly and exact supplied version-7 bytes.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json

EMITTERS = {'input': 'generate.py', 'rectify': 'generate-rectify.py',
            'prepare': 'generate-skolem.py', 'public': 'generate-transform.py',
            'transform': 'generate-split-transform.py', 'declarations': 'generate-split-declarations.py',
            'remove': 'generate-removal.py', 'clausify': 'generate-clausifier.py'}
HEADER = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Untrusted observations are checked against actual calls and sealed bytes. -/\n'
INTRO = '\nopen Aeneas Aeneas.Std\nnamespace EqInstance\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'


def module(imports, body, audits=()):
    return (HEADER + ''.join('import ' + name + '\n' for name in imports) + INTRO + body +
            ''.join('#print axioms EqInstance.' + name + '\n' for name in audits) + 'end EqInstance\n')


def build(source, certificate, raw, emitters):
    g = emitters['input']
    w = json.loads(raw, object_pairs_hook=g.no_duplicate_keys)
    g.fields(w, ('schema', 'source_hex', 'certificate_hex', 'functions', 'original_predicates',
                 'equality_id', 'extended_predicates', 'source_declarations', 'declarations',
                 'standalone', 'skolem', 'blocks', 'ordinary', 'equality'))
    g.require(w['schema'] == 'fang-equality-kernel-witness-1', 'Equality witness schema')
    g.require(w['equality_id'] == len(w['original_predicates']), 'Reserved index suggestion')
    g.require(w['extended_predicates'] == [arity for _, arity in w['original_predicates']] + [2],
              'Extended table suggestion')
    spelling = 'reserved_equality'
    while spelling in [name for name, _ in w['original_predicates']]:
        spelling += '_'
    common = {key: w[key] for key in ('source_hex', 'certificate_hex', 'functions',
              'source_declarations', 'declarations', 'standalone', 'skolem', 'blocks')}
    common.update(schema=g.SCHEMA, predicates=w['original_predicates'] + [[spelling, 2]])
    common = g.validate(json.dumps(common).encode(), source, certificate)
    ordinary, block_index = [], 0
    for declaration in common['source_declarations']:
        kind, body = declaration['body']
        if kind == 'cnf':
            clauses = [body]
        else:
            clauses = common['blocks'][block_index]['clauses']
            block_index += 1
        for row in clauses:
            clause = []
            for literal in row:
                if literal not in clause:
                    clause.append(literal)
            ordinary.append(clause)
    g.require(block_index == len(common['blocks']), 'Mixed block count')
    g.require(w['ordinary'] == ordinary, 'Observed ordinary assembly differs')
    expected = [[[positive, ['equal', args[0], args[1]] if symbol == w['equality_id']
                  else ['predicate', symbol, args]] for positive, symbol, args in clause] for clause in ordinary]
    g.require(w['equality'] == expected, 'Observed equality conversion differs')

    def clause(value):
        return '[' + ', '.join('⟨' + str(p).lower() + ', ' + str(s) + ', [' +
                              ', '.join(g.term(t, True) for t in args) + ']⟩' for p, s, args in value) + ']'

    def input_literal(value, numeric=False):
        positive, atom = value
        if atom[0] == 'equal':
            body = '(.' + ('equal' if numeric else 'Equal') + ' ' + g.term(atom[1], numeric) + ' ' + g.term(atom[2], numeric) + ')'
        else:
            args = '[' + ', '.join(g.term(t, True) for t in atom[2]) + ']' if numeric else g.vec([g.term(t) for t in atom[2]])
            body = ('(.predicate ⟨' + str(atom[1]) + ', ' + args + '⟩)' if numeric else
                    '(.Predicate ' + str(atom[1]) + '#u32 ' + args + ')')
        return '⟨' + str(positive).lower() + ', ' + body + '⟩'

    result = g.emit(common, source, certificate, 'EqInstance')
    rows = ['(.' + d['body'][0] + ' ' + json.dumps(d['name']) + ' ' + (clause(d['body'][1]) if d['body'][0] == 'cnf' else g.formula(d['body'][1], True)) + ')' for d in common['source_declarations']]
    symbols = lambda table: '[' + ', '.join('(' + json.dumps(name) + ', ' + str(arity) + ')' for name, arity in table) + ']'
    result['EqInstanceDecoded'] = module(['EqualityQuantifiedBytes'],
        'def input : String := ' + json.dumps(source.decode('ascii')) + '\n' +
        'def certificateBytes : String := ' + json.dumps(certificate.decode('ascii')) + '\n' +
        'def decoded : Fang.QuantifiedEqualityFrontend.Encoding.Encoded := {\n' +
        '  functions := ' + symbols(w['functions']) + '\n  originalPredicates := ' + symbols(w['original_predicates']) +
        '\n  equalityId := ' + str(w['equality_id']) + '\n  predicateArities := ' + str(w['extended_predicates']) +
        '\n  declarations := [' + ', '.join(rows) + '] }\n' +
        'theorem decode_eq : Fang.QuantifiedEqualityFrontend.decode input = .ok decoded := by cbv\n', ['decode_eq']).replace('open Aeneas Aeneas.Std\n', '')
    reservation = '⟨' + g.vec([str(a) + '#usize' for _, a in w['original_predicates']]) + ', ' + str(w['equality_id']) + '#u32⟩'
    original = '⟨' + g.vec([str(a) + '#usize' for _, a in w['functions']]) + ', ' + g.vec([str(a) + '#usize' for _, a in w['original_predicates']]) + '⟩'
    declaration_values = ', '.join('⟨formula' + str(i) + ', true⟩' for i in range(len(common['declarations'])))
    widths, identifiers = g.encoding_bounds(common)
    axioms_bounds = ''.join(f'  have width{n} : {n} ≤ Usize.max := by scalar_tac\n' for n in widths) + ''.join(f'  have identifier{n} : {n} ≤ U32.max := by scalar_tac\n' for n in identifiers)
    axioms_names = [f'width{n}' for n in widths] + [f'identifier{n}' for n in identifiers] + [f'formula{i}' for i in range(len(common['declarations']))]
    result['EqInstanceEncoded'] = module(['EqInstanceData', 'EqInstanceDecoded', 'EqualityBridgeKernel'], f'''
set_option linter.unusedSimpArgs false
def originalSignature : fang_skolem_core.fang_quantified_fof_core.Signature := {original}
def reservation : fang_fof_equality_bridge.Reservation := {reservation}
def declarations : Slice fang_skolem_core.Declaration := Slice.from [{declaration_values}] (by simp; scalar_tac)
def encoded : FangQuantifiedEqualityInput.Prepared := ⟨decoded, declarations, signature, reservation⟩
theorem original_signature_eq : FangQuantifiedTransport.encodeSignature
    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by cbv
theorem reservation_eq : fang_fof_equality_bridge.Reservation.new originalSignature.predicates 100000#usize =
    .ok (.Ok reservation) := by
  apply FangEqualityKernelGenerator.reservation_eq
  · simp [originalSignature, FangQuantifiedKernel.vector, alloc.vec.Vec.val]
  · rfl
theorem extended_eq : fang_fof_equality_bridge.Reservation.extended_arities reservation = .ok signature.predicates := by
  apply FangEqualityKernelGenerator.extended_arities_eq
  · simp [reservation, FangQuantifiedKernel.vector, alloc.vec.Vec.val]; scalar_tac
  · rfl
theorem axioms_eq : FangOriginalInput.encodeAxioms
    (Fang.QuantifiedCertificate.formulas (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations)) = .ok declarations.val := by
{axioms_bounds}  simp [{''.join(name + ', ' for name in axioms_names)}decoded, declarations,
    FangQuantifiedEqualityInput.numericDeclarations, FangQuantifiedEqualityInput.numericDeclaration,
    Fang.QuantifiedCertificate.formulas, FangOriginalInput.encodeAxioms, FangOriginalInput.liftWidth,
    FangQuantifiedTransport.encodeDeclaration, FangQuantifiedTransport.encodeFormula,
    FangQuantifiedTransport.encodeTerm, FangQuantifiedTransport.encodeTerms,
    FangQuantifiedTransport.checkedU32, FangQuantifiedTransport.checkedVec,
    FangQuantifiedKernel.vector, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals (repeat' (first | rfl | constructor))
theorem slice_eq : FangOriginalInput.checkedSlice declarations.val = .ok declarations := by
  unfold FangOriginalInput.checkedSlice
  rw [dite_eq_left declarations.property]
  rfl
theorem transport_eq : FangQuantifiedEqualityInput.transport decoded 100000#usize = .ok encoded := by
  unfold FangQuantifiedEqualityInput.transport
  rw [original_signature_eq]
  simp only [FangQuantifiedEqualityInput.liftTransport, FangOriginalInput.liftWidth, Except.mapError,
    Bind.bind, Except.bind, FangQuantifiedEqualityInput.reserve, reservation_eq,
    FangQuantifiedEqualityInput.observe, Result.match.ok, extended_eq, axioms_eq,
    slice_eq, Pure.pure, Except.pure]
  rfl
theorem input_eq : FangQuantifiedEqualityInput.prepareInput input 100000#usize = .ok encoded := by
  simp [FangQuantifiedEqualityInput.prepareInput, decode_eq, transport_eq, Except.mapError, Bind.bind, Except.bind]
''', ['original_signature_eq', 'reservation_eq', 'extended_eq', 'axioms_eq', 'slice_eq', 'transport_eq', 'input_eq'])
    input_names = list(result)
    rectification = emitters['rectify'].emit(g, common, 'EqInstance')
    result.update(rectification)
    preparation = emitters['prepare'].emit(g, common, 'EqInstance')
    result.update(preparation)
    transform, _, _, _ = emitters['transform'].emit(g, emitters['rectify'].nnf, common, 'EqInstance')
    result.update(transform)
    declarations, _ = emitters['declarations'].emit(g, emitters['rectify'].nnf,
        emitters['transform'], emitters['public'], common, 'EqInstance')
    result.update(declarations)
    removal = emitters['remove'].emit(g, emitters['rectify'].nnf, common, 'EqInstance')
    result.update(removal)
    clausification = emitters['clausify'].emit(g, emitters['rectify'].nnf, emitters['remove'], common, 'EqInstance')
    result.update(clausification)
    conversion_names = []
    for i, (ordinary_clause, explicit) in enumerate(zip(ordinary, w['equality'])):
        widths, identifiers = {len(ordinary_clause)}, set()
        def bounds(term):
            identifiers.add(term[1])
            if term[0] == 'fun':
                widths.add(len(term[2]))
                for child in term[2]:
                    bounds(child)
        for _, symbol, arguments in ordinary_clause:
            identifiers.add(symbol)
            widths.add(len(arguments))
            for argument in arguments:
                bounds(argument)
        width_lines = ''.join(f'  have width{n} : {n} ≤ Usize.max := by scalar_tac\n' for n in sorted(widths - {0}))
        width_lines += ''.join(f'  have identifier{n} : {n} ≤ U32.max := by scalar_tac\n' for n in sorted(identifiers - {0}))
        width_names = [f'width{n}' for n in sorted(widths - {0})] + [f'identifier{n}' for n in sorted(identifiers - {0})]
        source_vector = g.vec(['⟨' + str(p).lower() + ', ' + str(s) + '#u32, ' + g.vec([g.term(t) for t in args]) + '⟩' for p, s, args in ordinary_clause])
        target_vector = g.vec([input_literal(lit) for lit in explicit])
        name = 'EqInstanceConversion' + str(i)
        body = f'''def ordinary{i} : Fang.Clause := {clause(ordinary_clause)}
def bridgeSource{i} : alloc.vec.Vec FangEqualityBridge.OutputLiteral := {source_vector}
def bridgeTarget{i} : alloc.vec.Vec FangEqualityBridge.InputLiteral := {target_vector}
def equality{i} : Fang.Equality.Clause := [{', '.join(input_literal(lit, True) for lit in explicit)}]
set_option linter.unusedSimpArgs false
theorem encode_clause{i}_eq : FangQuantifiedEqualityReplay.Transport.encodeClause ordinary{i} = .ok bridgeSource{i} := by
{width_lines}  simp [{''.join(n + ', ' for n in width_names)}ordinary{i}, bridgeSource{i}, FangQuantifiedKernel.vector,
    FangQuantifiedEqualityReplay.Transport.encodeClause, FangQuantifiedEqualityReplay.Transport.encodeLiterals,
    FangQuantifiedEqualityReplay.Transport.encodeLiteral, FangQuantifiedEqualityReplay.Transport.encodeTerms,
    FangQuantifiedEqualityReplay.Transport.encodeTerm, FangQuantifiedTransport.checkedVec,
    FangQuantifiedTransport.checkedU32, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals rfl
theorem clause_relation{i} : List.Forall₂ (FangEqualityBridge.EncodesLiteral reservation)
    bridgeTarget{i}.val bridgeSource{i}.val := by
  simp [bridgeTarget{i}, bridgeSource{i}, reservation, FangQuantifiedKernel.vector, alloc.vec.Vec.val,
    FangEqualityBridge.EncodesLiteral, FangEqualityBridge.LiteralValid, FangEqualityBridge.OrdinaryAnswer]
theorem decode_clause{i}_eq : fang_fof_equality_bridge.Reservation.decode_clause reservation bridgeSource{i} 256#usize =
    .ok (.Ok bridgeTarget{i}) := by
  apply FangEqualityKernelGenerator.decode_clause_eq
  · rfl
  · simp [bridgeSource{i}, FangQuantifiedKernel.vector, alloc.vec.Vec.val]
  · exact clause_relation{i}
theorem conversion{i}_eq : FangQuantifiedEqualityReplay.Conversion.clause reservation 256#usize ordinary{i} = .ok equality{i} := by
  exact FangEqualityKernelGenerator.conversion_clause_eq reservation 256#usize ordinary{i}
    bridgeSource{i} bridgeTarget{i} encode_clause{i}_eq decode_clause{i}_eq
'''
        result[name] = module(['EqInstanceEncoded'], body,
            ['encode_clause' + str(i) + '_eq', 'clause_relation' + str(i), 'decode_clause' + str(i) + '_eq', 'conversion' + str(i) + '_eq'])
        conversion_names.append(name)
    block_rows = ['[' + ', '.join(clause(row) for row in block['clauses']) + ']' for block in common['blocks']]
    body = 'def clauseBlocks : List Fang.Problem := [' + ', '.join(block_rows) + ']\n'
    body += """def replayLimits : FangOriginalReplay.Limits := {
  skolem := FangOriginalKernelProbe.skolemLimits
  removal := FangKernelGenerator.removalLimits
  clausification := FangQuantifiedKernel.Clausifier.limits }
"""
    body += 'def ordinary : Fang.Problem := [' + ', '.join('ordinary' + str(i) for i in range(len(ordinary))) + ']\n'
    body += 'def prepared : FangQuantifiedEqualityReplay.Prepared := ⟨[' + ', '.join('equality' + str(i) for i in range(len(ordinary))) + '], ' + str(w['skolem']['functions']) + ', ' + str([a for _, a in w['original_predicates']]) + '⟩\n'
    body += 'theorem blocks_eq : FangOriginalReplay.replayBlocks replayLimits skolemized.formulas.val = .ok clauseBlocks := by\n'
    outputs = ', '.join('skolemOutput' + str(i) for i in range(len(common['blocks'])))
    decoded_blocks = ', '.join('FangScopedFof.decodeClauses block' + str(i) + '.clauses.val' for i in range(len(common['blocks'])))
    body += '  change FangOriginalReplay.replayBlocks replayLimits [' + outputs + '] = .ok [' + decoded_blocks + ']\n'
    for i in range(len(common['blocks'])):
        body += f'  apply FangEqualityKernelGenerator.replay_blocks_cons remove{i}_eq clausify{i}_eq\n'
    body += '  rfl\n'
    body += """theorem assembly_eq : FangOriginalReplay.assemble (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations) clauseBlocks = .ok ordinary := by cbv
+theorem conversion_eq : FangQuantifiedEqualityReplay.Conversion.problem reservation 256#usize ordinary = .ok prepared.problem := by
+  simp only [ordinary, prepared, FangQuantifiedEqualityReplay.Conversion.problem,
+    """.replace('\n+', '\n') + ''.join('conversion' + str(i) + '_eq, ' for i in range(len(ordinary))) + """Bind.bind, Except.bind, Pure.pure, Except.pure]
+theorem prepare_eq : FangQuantifiedEqualityReplay.prepare input replayLimits 100000#usize 256#usize = .ok prepared := by
+  have result := FangEqualityKernelGenerator.prepare_of_parts (limits := replayLimits) input_eq skolemize_eq blocks_eq assembly_eq conversion_eq
+  exact result
+""".replace('\n+', '\n')
    result['EqInstancePrepared'] = module(['EqInstanceSkolem', 'EqualityReplayKernel', 'BooleanClausifierPrimitives', 'RemovalPrimitives'] + list(clausification) + conversion_names,
                                          body, ['blocks_eq', 'assembly_eq', 'conversion_eq', 'prepare_eq'])
    checked_problem = '[' + ', '.join('[' + ', '.join(input_literal(lit, True) for lit in row) + ']' for row in w['equality']) + ']'
    result['EqInstanceChecked'] = emitters['certificate'].checked_module(certificate,
        checked_problem, str(w['skolem']['functions']),
        str([a for _, a in w['original_predicates']]))
    result['EqInstanceJoined'] = HEADER + 'import EqInstancePrepared\nimport EqInstanceChecked\n'
    result['EqInstanceCertificate'] = module(['EqInstanceJoined'], '''
theorem certificate_checked : FangQuantifiedEqualityCertificate.checkPrepared
    prepared.problem prepared.functionArities prepared.predicateArities certificateBytes = .ok () := by
  dsimp only [prepared, ''' + ', '.join('equality' + str(i) for i in range(len(ordinary))) + (', ' if ordinary else '') + '''certificateBytes]
  exact checked_bytes
#print axioms EqInstance.certificate_checked
theorem certificate_accepts : FangQuantifiedEqualityCertificate.accepts input certificateBytes replayLimits 100000#usize 256#usize = .ok () := by
  unfold FangQuantifiedEqualityCertificate.accepts
  rw [prepare_eq]
  change (FangQuantifiedEqualityCertificate.checkPrepared prepared.problem prepared.functionArities prepared.predicateArities certificateBytes).mapError FangQuantifiedEqualityCertificate.Error.prepared = .ok ()
  rw [certificate_checked]
  rfl
#print axioms EqInstance.certificate_accepts
theorem original_bytes_unsat : ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable
    (Fang.Source.Grammar.spelling input) := FangQuantifiedEqualityCertificate.accepts_original_unsat certificate_accepts
#print axioms EqInstance.original_bytes_unsat
''')
    result['EqInstanceFixedAudit'] = module(['EqInstanceCertificate'],
        'theorem actual_sealed_acceptance : FangQuantifiedEqualityCertificate.accepts ' + json.dumps(source.decode()) + ' ' + json.dumps(certificate.decode()) +
        ' replayLimits 100000#usize 256#usize = .ok () := certificate_accepts\n' +
        'theorem actual_original_bytes_unsat : ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable\n' +
        '    (Fang.Source.Grammar.spelling ' + json.dumps(source.decode()) + ') := original_bytes_unsat\n',
        ['actual_sealed_acceptance', 'actual_original_bytes_unsat'])
    phases = [input_names, list(rectification), list(preparation), list(transform), list(declarations), list(removal), list(clausification), conversion_names,
              ['EqInstancePrepared'], ['EqInstanceChecked'], ['EqInstanceJoined'], ['EqInstanceCertificate'], ['EqInstanceFixedAudit']]
    total = sum(len(code.encode()) for code in result.values())
    g.require(total <= 16 << 20 and len(result) <= 256, 'Generated size/module cap')
    return {name: code.encode() for name, code in result.items()}, [phase for phase in phases if phase]
