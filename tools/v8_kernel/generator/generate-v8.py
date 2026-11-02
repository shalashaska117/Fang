#!/usr/bin/env python3
"""Version-8 exact-instance modules for one sealed input/certificate pair (generator version 4).

The pinned version-7 recipe emits the modules for the extracted calls (Skolem,
removal, clausification, conversion) unchanged. This module replaces only the
front, where the version-8 decoder and legacyInput reach the version-7 transport
input, and the back, where V8ReplayKernel composes prepare and accepts and
the version-8 envelope check runs. Witness values remain untrusted suggestions;
Lean checks every equation on the sealed bytes.

Version 2 takes a version-8 witness: declaration names are already tagged as
legacyInput tags them, and symbol tables may repeat a name with another arity.
The version-7 recipe only needs names to be distinct lower-case spellings, so it
receives a copy with synthetic names; the Decoded module is rebuilt from the
real tables and names, which Lean then checks against the actual decoder.

Version 3 changes two version-7 recipe proofs that were only exercised on empty
tables and nonempty clauses: the original-signature equation for nonempty symbol
tables (bounded-vector facts by scalar_tac, then simp), and the clause encoding
of an empty clause (the finishing tactic has nothing to do there).

Version 4 follows two diagnostics on the accepted version-8 pairs. After the
simp calls in EqInstanceEncoded, the goals left are one equation or a
conjunction of equations between bounded literals; `repeat' constructor`
closes both shapes, where the version-7 `first | rfl | constructor` left
`constructor` unused on a single equation. The envelope check no longer runs
the lexer and parser under one cbv call, which exceeded 4 GiB on three pairs; it
follows the reviewed version-7 certificate module instead (exact string, lexer
and node equations by the pinned certificate emitter, one parser equation),
with the version-8 parser and envelope, so cbv only evaluates the signature gate
and the ordered check.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
import re

HEADER = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Untrusted observations are checked against actual calls and sealed bytes. -/\n'
INTRO = '\nopen Aeneas Aeneas.Std\nnamespace EqInstance\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
INTEGRATION = 'Fang.TptpCandidate.FullFof.Integration'
SATISFIABLE = 'Fang.TptpCandidate.FullFof.CnfBoolean.BytesSatisfiable'
MAXIMUM_BYTES = '1048576'
RECIPE_FINISH = "  all_goals (repeat' (first | rfl | constructor))\n"
FINISH = "  all_goals (repeat' constructor)\n"
SUPPORT = '''namespace FangV8CertificateKernel
theorem size_ofList (characters : List Char) :
    (String.ofList characters).utf8ByteSize = (characters.map Char.utf8Size).sum := by
  induction characters with
  | nil => rfl
  | cons c cs ih =>
    change (String.ofList ([c] ++ cs)).utf8ByteSize = _
    rw [String.ofList_append, String.utf8ByteSize_append,
      ← String.singleton_eq_ofList, String.utf8ByteSize_singleton, ih]
    rfl

theorem frontend_tokenizes (input : String) (characters : List Char)
    (tokens : List Fang.Frontend.Token) (fuel : Nat)
    (spelling : input.toList = characters)
    (ascii : characters.findIdx? (fun c => c.toNat > 127) = none)
    (length : characters.length + 1 = fuel)
    (lexed : Fang.Frontend.lexAux fuel characters 0 = .ok tokens) :
    Fang.Frontend.tokenize input = .ok tokens := by
  unfold Fang.Frontend.tokenize
  rw [spelling]
  dsimp only
  rw [ascii, length]
  exact lexed

theorem v8_decodes (input : String) (tokens : List Fang.Frontend.Token)
    (size fuel : Nat) (certificate : Fang.Equality.Ordered.Certificate) (state : Fang.Frontend.State)
    (tokenized : Fang.Frontend.tokenize input = .ok tokens)
    (bytes : input.utf8ByteSize = size) (length : tokens.length + 1 = fuel)
    (parsed : INTEGRATION.v8Certificate fuel { tokens, endOffset := size } = .ok (certificate, state)) :
    INTEGRATION.decodeV8 input = .ok certificate := by
  simp [INTEGRATION.decodeV8, tokenized, bytes, length, parsed, Bind.bind, Except.bind]
  rfl
end FangV8CertificateKernel

'''.replace('INTEGRATION', INTEGRATION)


class Rejected(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise Rejected(reason)


def module(imports, body, audits=()):
    return (HEADER + ''.join('import ' + name + '\n' for name in imports) + INTRO + body +
            ''.join('#print axioms EqInstance.' + name + '\n' for name in audits) + 'end EqInstance\n')


def unique(items):
    result = {}
    for key, value in items:
        require(key not in result, 'Duplicate witness field')
        result[key] = value
    return result


def remove_theorem(text, name):
    """Drop one generated version-7 composition theorem and its audit line."""
    lines = text.split('\n')
    starts = [i for i, line in enumerate(lines) if line.startswith('theorem ' + name + ' ')]
    require(len(starts) == 1, 'Expected one version-7 theorem ' + name)
    end = starts[0] + 1
    while end < len(lines) and lines[end].startswith(' '):
        end += 1
    del lines[starts[0]:end]
    audit = '#print axioms EqInstance.' + name
    require(lines.count(audit) == 1, 'Expected one audit for ' + name)
    lines.remove(audit)
    return '\n'.join(lines)


def endpoint(source, certificate):
    """The fixed endpoint: exact sealed bytes, the native checker's parameters, nothing generated but limits."""
    text, proof = json.dumps(source), json.dumps(certificate)
    return module(['EqInstanceCertificate'],
        'theorem actual_sealed_acceptance : ' + INTEGRATION + '.accepts ' + text + '.toUTF8.data.toList ' + MAXIMUM_BYTES +
        ' ' + proof + ' replayLimits 100000#usize 256#usize = .ok () := certificate_accepts\n'
        'theorem actual_original_bytes_unsat : ¬ ' + SATISFIABLE + '\n'
        '    ' + text + '.toUTF8.data.toList ' + MAXIMUM_BYTES + ' := original_bytes_unsat\n',
        ['actual_sealed_acceptance', 'actual_original_bytes_unsat'])


def checked_v8(cert, certificate, problem, functions, predicates):
    """The reviewed version-7 decomposition with the version-8 parser and envelope."""
    expression, steps, final = cert.certificate_constructor(certificate)
    body = cert.exact_string('proofBytes', certificate)
    body = body[:body.index('theorem exact_proofBytes_bytes :')]
    body += 'def parsedCertificate : Fang.Equality.Ordered.Certificate := ' + expression + '\n\n'
    body += ''.join(cert.lexer_parts('proofBytes', certificate, 'Frontend'))
    body += ''.join(code for _, code in cert.node_equations(certificate, steps, final))
    tokens = [(m.group(), m.start()) for m in re.finditer(r'[A-Za-z0-9_$-]+|[(),.|~]', certificate.decode('ascii'))]
    spelling = '[' + ', '.join('{ text := ' + cert.quote(word.encode()) + ', offset := ' + str(offset) + ' }'
                               for word, offset in tokens) + ']'
    size, fuel = len(certificate), len(tokens) + 1
    body += (f'theorem certificate_parses :\n    {INTEGRATION}.v8Certificate {fuel}\n'
             f'      {{ tokens := {spelling}, endOffset := {size} }} =\n'
             f'      .ok (parsedCertificate, {{ tokens := [], endOffset := {size} }}) := by cbv\n\n'
             f'@[cbv_eval] theorem exact_certificate_decodes : {INTEGRATION}.decodeV8 proofBytes = .ok parsedCertificate :=\n'
             f'  FangV8CertificateKernel.v8_decodes proofBytes _ {size} {fuel}\n'
             '    parsedCertificate _ proofBytes_tokenizes proofBytes_size (by decide +kernel) certificate_parses\n\n'
             'def checkedProblem : Fang.Equality.Problem := ' + problem + '\n'
             f'theorem checked : {INTEGRATION}.checkProblem checkedProblem {functions} {predicates} certificateBytes = .ok () := by\n'
             f'  change {INTEGRATION}.checkProblem _ _ _ proofBytes = .ok ()\n'
             f'  unfold {INTEGRATION}.checkProblem\n'
             '  rw [exact_certificate_decodes]\n'
             '  cbv\n\n'
             '#print axioms EqInstance.exact_certificate_decodes\n#print axioms EqInstance.checked\nend EqInstance\n')
    body = body.replace('FangEqualityCertificateKernel.', 'FangV8CertificateKernel.')
    return ('/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n'
            '   Untrusted observations are checked against actual calls and sealed bytes. -/\n'
            'import EqInstanceDecoded\nimport ExpandedEnvelope\n\n'
            'set_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\nset_option cbv.maxSteps 20000000\n\n'
            + SUPPORT + 'namespace EqInstance\n' + body)



def build(source, certificate, raw, emitters, recipe):
    """recipe is the pinned version-7 generator module (CNF or quantified) selected for this witness."""
    require(source.isascii() and certificate.isascii(), 'ASCII pair required')
    # Only a structural guard: the version and marker are checked by decodeV8 inside Lean.
    require(certificate.startswith(b'(fang-proof '), 'Certificate envelope required')
    try:
        witness = json.loads(raw, object_pairs_hook=unique)
    except (ValueError, RecursionError) as error:
        raise Rejected('Invalid witness JSON') from error
    require(isinstance(witness, dict) and witness.get('source_hex') == source.hex(), 'Witness detached from the source')
    # The version-7 recipe binds the certificate bytes it embeds; give it the version-8 bytes,
    # and synthetic names that satisfy its spelling rules. Names are not used by its equations.
    witness['certificate_hex'] = certificate.hex()
    real = {key: witness[key] for key in ('functions', 'original_predicates')}
    declared = [item['name'] for item in witness['source_declarations']]
    require(all(isinstance(name, str) and name.isascii() and name.isprintable() for name in declared) and
            all(isinstance(symbol, list) and len(symbol) == 2 and isinstance(symbol[0], str) and symbol[0].isascii() and
                symbol[0].isprintable() for key in real for symbol in real[key]), 'Witness names must be printable ASCII')
    sanitized = json.loads(json.dumps(witness))
    sanitized['functions'] = [['f' + str(i), arity] for i, (_, arity) in enumerate(witness['functions'])]
    sanitized['original_predicates'] = [['p' + str(i), arity] for i, (_, arity) in enumerate(witness['original_predicates'])]
    synthetic = {name: 'd' + str(i) for i, name in enumerate(declared)}
    require(len(synthetic) == len(declared), 'Duplicate declaration name')
    for item in sanitized['source_declarations'] + sanitized['declarations']:
        item['name'] = synthetic[item['name']]
    built, phases = recipe.build(source, certificate, json.dumps(sanitized).encode(), emitters)
    modules = {name: data.decode('utf-8') for name, data in built.items()}
    names = list(modules)
    for required in ('EqInstanceDecoded', 'EqInstanceEncoded', 'EqInstancePrepared', 'EqInstanceChecked',
                     'EqInstanceJoined', 'EqInstanceCertificate', 'EqInstanceFixedAudit'):
        require(required in modules, 'Version-7 recipe module missing: ' + required)
    # Front: the version-8 decoder, then legacyInput, reaches the version-7 transport input.
    decoded = re.search(r'def decoded : Fang\.QuantifiedEqualityFrontend\.Encoding\.Encoded := (\{.*?\})\ntheorem',
                        modules['EqInstanceDecoded'], re.S)
    require(decoded is not None, 'Version-7 decoded value missing')
    original_names = {value: name for name, value in synthetic.items()}
    literal, renamed = re.subn(r'\((\.(?:cnf|fof)) "(d[0-9]+)"', lambda m: '(' + m.group(1) + ' ' + json.dumps(original_names[m.group(2)]),
                               decoded.group(1))
    require(renamed == len(declared), 'Every source declaration must be renamed once')
    symbols = lambda table: '[' + ', '.join('(' + json.dumps(name) + ', ' + str(arity) + ')' for name, arity in table) + ']'
    literal, tables = re.subn(r'^  functions := .*$', lambda _: '  functions := ' + symbols(real['functions']), literal, flags=re.M)
    literal, more = re.subn(r'^  originalPredicates := .*$', lambda _: '  originalPredicates := ' + symbols(real['original_predicates']),
                            literal, flags=re.M)
    require(tables == 1 and more == 1, 'Decoded table lines differ from the version-7 shape')
    modules['EqInstanceDecoded'] = module(['ExpandedCertificate'],
        'set_option cbv.maxSteps 200000000\n'
        'def bytes : List UInt8 := ' + json.dumps(source.decode('ascii')) + '.toUTF8.data.toList\n'
        'def certificateBytes : String := ' + json.dumps(certificate.decode('ascii')) + '\n'
        'def decoded : Fang.QuantifiedEqualityFrontend.Encoding.Encoded := ' + literal + '\n'
        'theorem front_map : (' + INTEGRATION + '.decodeNumeric bytes ' + MAXIMUM_BYTES + ').map ' + INTEGRATION +
        '.legacyInput = .ok decoded := by cbv\n'
        'theorem front : ∃ numeric, ' + INTEGRATION + '.decodeNumeric bytes ' + MAXIMUM_BYTES + ' = .ok numeric ∧\n'
        '    ' + INTEGRATION + '.legacyInput numeric = decoded := by\n'
        '  have mapped := front_map\n'
        '  cases run : ' + INTEGRATION + '.decodeNumeric bytes ' + MAXIMUM_BYTES + ' with\n'
        '  | error failure => simp [run, Except.map] at mapped\n'
        '  | ok numeric => exact ⟨numeric, rfl, by simpa [run, Except.map] using mapped⟩\n',
        ['front_map', 'front']).replace('open Aeneas Aeneas.Std\n', '')
    # Nonempty symbol tables: the recipe's cbv proof stops at the bounded-vector check.
    arities = [arity for _, arity in witness['functions']] + [arity for _, arity in witness['original_predicates']]
    if arities:
        old = ('    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by cbv\n')
        require(modules['EqInstanceEncoded'].count(old) == 1, 'Version-7 signature equation shape differs')
        bounds = sorted({value for value in arities + [len(witness['functions']), len(witness['original_predicates'])]} - {0})
        facts = ''.join('  have width%d : %d \u2264 Usize.max := by scalar_tac\n' % (n, n) for n in bounds)
        widths = ''.join('width%d, ' % n for n in bounds)
        new = ('    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by\n' + facts +
               '  simp [' + widths + 'decoded, originalSignature, FangQuantifiedTransport.encodeSignature,\n'
               '    FangQuantifiedTransport.encodeArities, FangQuantifiedTransport.checkedUsize, FangQuantifiedTransport.checkedVec,\n'
               '    FangQuantifiedKernel.vector, Bind.bind, Except.bind, Pure.pure, Except.pure]\n'
               + FINISH)
        modules['EqInstanceEncoded'] = modules['EqInstanceEncoded'].replace(old, new)
    modules['EqInstanceEncoded'] = modules['EqInstanceEncoded'].replace(RECIPE_FINISH, FINISH)
    # An empty clause encodes by simp alone; the recipe's finishing rfl would only add a linter warning.
    for name in list(modules):
        if name.startswith('EqInstanceConversion') and re.search(r'^def ordinary[0-9]+ : Fang\.Clause := \[\]$',
                                                                 modules[name], re.M):
            require(modules[name].count('  all_goals rfl\n') == 1, 'Version-7 empty clause encoding shape differs')
            modules[name] = modules[name].replace('  all_goals rfl\n', '')
    # The version-7 compositions name the version-7 decoder and prepare; version 8 composes its own.
    modules['EqInstanceEncoded'] = remove_theorem(modules['EqInstanceEncoded'], 'input_eq')
    modules['EqInstancePrepared'] = remove_theorem(modules['EqInstancePrepared'], 'prepare_eq')
    functions = str(witness['skolem']['functions'])
    predicates = str([arity for _, arity in witness['original_predicates']])
    rows = []
    for row in witness['equality']:
        literals = []
        for positive, atom in row:
            require(isinstance(positive, bool) and isinstance(atom, list), 'Equality literal shape')
            if atom[0] == 'equal':
                body = '(.equal ' + emitters['input'].term(atom[1], True) + ' ' + emitters['input'].term(atom[2], True) + ')'
            else:
                body = ('(.predicate ⟨' + str(atom[1]) + ', [' +
                        ', '.join(emitters['input'].term(t, True) for t in atom[2]) + ']⟩)')
            literals.append('⟨' + str(positive).lower() + ', ' + body + '⟩')
        rows.append('[' + ', '.join(literals) + ']')
    modules['EqInstanceChecked'] = checked_v8(emitters['certificate'], certificate, '[' + ', '.join(rows) + ']',
                                              functions, predicates)
    modules['EqInstanceJoined'] = HEADER + 'import EqInstancePrepared\nimport EqInstanceChecked\nimport V8ReplayKernel\n'
    modules['EqInstanceCertificate'] = module(['EqInstanceJoined'],
        'theorem certificate_accepts : ' + INTEGRATION + '.accepts bytes ' + MAXIMUM_BYTES +
        ' certificateBytes replayLimits 100000#usize 256#usize = .ok () := by\n'
        '  obtain ⟨numeric, decodeRun, legacy⟩ := front\n'
        '  have predicates : numeric.predicates.map Prod.snd = ' + predicates + ' :=\n'
        '    congrArg (List.map Prod.snd) (congrArg Fang.QuantifiedEqualityFrontend.Encoding.Encoded.originalPredicates legacy)\n'
        '  apply FangV8KernelGenerator.accepts_of_parts (FangV8KernelGenerator.prepare_of_parts (limits := replayLimits)\n'
        '    decodeRun (FangV8KernelGenerator.transport_of_legacy legacy transport_eq) skolemize_eq blocks_eq\n'
        '    (FangV8KernelGenerator.assembly_of_legacy legacy assembly_eq) conversion_eq)\n'
        '  dsimp only\n'
        '  rw [predicates]\n'
        '  exact checked\n'
        'theorem original_bytes_unsat : ¬ ' + SATISFIABLE + ' bytes ' + MAXIMUM_BYTES + ' :=\n'
        '  ' + INTEGRATION + '.accepts_original_unsat certificate_accepts\n',
        ['certificate_accepts', 'original_bytes_unsat'])
    modules['EqInstanceFixedAudit'] = endpoint(source.decode('ascii'), certificate.decode('ascii'))
    require(list(modules) == names, 'Module order changed')
    return {name: text.encode('utf-8') for name, text in modules.items()}, phases
