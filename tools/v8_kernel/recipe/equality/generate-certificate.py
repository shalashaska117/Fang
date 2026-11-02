"""Bounded version-7 certificate witnesses; all decoding/check equations are kernel checked.

Constructor and lexer/node decomposition reuse the accepted ordered replay generator.
Only the envelope decoder and namespace are changed; no checker is replaced.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import re
MAX_CERTIFICATE_NODES = 100
def quote(data):
    text = data.decode("ascii")
    return '"' + "".join("\\u%04x" % ord(c) if ord(c) < 32 else
                         "\\" + c if c in ('"', "\\") else c for c in text) + '"'


def byte_list(data):
    return "[" + ", ".join(map(str, data)) + "]"


def characters(data):
    return "[" + ", ".join("Char.ofNat " + str(x) for x in data) + "]"


def exact_string(label, data):
    chars = characters(data)
    return f'''def {label} : String := {quote(data)}

@[cbv_eval] theorem {label}_characters : {label}.toList = {chars} := by
  exact String.toList_ofList

@[cbv_eval] theorem {label}_size : {label}.utf8ByteSize = {len(data)} := by
  change (String.ofList {chars}).utf8ByteSize = _
  rw [FangEqualityCertificateKernel.size_ofList]
  decide +kernel

theorem {label}_ascii : ({chars}).findIdx? (fun c => c.toNat > 127) = none := by
  decide +kernel

theorem exact_{label}_bytes : Fang.Source.Grammar.spelling {label} = {byte_list(data)} := by
  change Fang.Source.Grammar.spelling (String.ofList {chars}) = _
  rw [Fang.Source.Grammar.spelling_ofList_ascii _ (by decide +kernel)]
  rfl

'''


def lexer_parts(label, data, namespace):
    pattern = r"[A-Za-z0-9_$]+|!=|[(),.|~=]" if namespace == "EqualityFrontend" else r"[A-Za-z0-9_$-]+|[(),.|~]"
    text = data.decode("ascii")
    if re.sub(pattern + r"|[ \t\n\r\f\v]", "", text):
        raise ValueError("Outside this replay token vocabulary")
    tokens = [(m.group(), m.start()) for m in re.finditer(pattern, text)]

    def token_list(items):
        return "[" + ", ".join("{ text := " + quote(word.encode()) + ", offset := " + str(offset) + " }"
                              for word, offset in items) + "]"

    boundaries = sorted({0, *(offset for _, offset in tokens[::10])})
    result = []
    for number, offset in reversed(list(enumerate(boundaries))):
        steps = len(re.findall(pattern + r"|[ \t\n\r\f\v]", text[:offset]))
        end = boundaries[number + 1] if number + 1 < len(boundaries) else len(data)
        tail = f" ++ {label}_suffix_characters_{number + 1}" if end < len(data) else ""
        token_tail = f" ++ {label}_suffix_tokens_{number + 1}" if end < len(data) else ""
        # Persistent suffix definitions keep generated text linear. The exact
        # lexer equations still run through kernel-controlled reduction.
        result.append(f"def {label}_suffix_characters_{number} : List Char := "
                   + characters(data[offset:end]) + tail + "\n\n"
                   + f"def {label}_suffix_tokens_{number} : List Fang.Frontend.Token := "
                   + token_list([(word, pos) for word, pos in tokens if offset <= pos < end]) + token_tail + "\n\n"
                   + f"@[cbv_eval] theorem {label}_lex_{number} : Fang.{namespace}.lexAux "
                   + f"{len(data) + 1 - steps} {label}_suffix_characters_{number} {offset} = .ok "
                   + f"{label}_suffix_tokens_{number} := by rfl\n\n")
    parts = ["".join(result[index:index + 4]) for index in range(0, len(result), 4)]
    bridge = "equality_tokenizes" if namespace == "EqualityFrontend" else "frontend_tokenizes"
    parts.append(f"@[cbv_eval] theorem {label}_tokenizes : Fang.{namespace}.tokenize {label} = .ok "
                 + token_list(tokens) + f" :=\n  FangEqualityCertificateKernel.{bridge} {label} _ _ {len(data) + 1}\n"
                 + f"    {label}_characters {label}_ascii (by decide +kernel) {label}_lex_0\n\n")
    return parts


def certificate_constructor(data):
    """Read data only. Envelope validity and trailing tokens are left to Lean.

    This intentionally constructs witnesses for the frozen malformed-envelope
    controls too. It cannot accept a certificate: the actual decoder equation
    must still pass in Lean.
    """
    text = data.decode("ascii")
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    cursor = 0

    def expression(depth=0):
        nonlocal cursor
        if depth > 128 or cursor >= len(tokens):
            raise ValueError("Witness nesting/length limit")
        token = tokens[cursor]
        cursor += 1
        if token != "(":
            if token == ")":
                raise ValueError("Unexpected closing parenthesis")
            return token
        result = []
        while cursor < len(tokens) and tokens[cursor] != ")":
            result.append(expression(depth + 1))
        if cursor == len(tokens):
            raise ValueError("Missing closing parenthesis")
        cursor += 1
        return result

    root = expression()
    if not isinstance(root, list) or len(root) < 4 or root[0] != "fang-proof":
        raise ValueError("Expected proof data")

    def natural(value):
        if not isinstance(value, str) or not re.fullmatch(r"[0-9]+", value) or len(value) > 10:
            raise ValueError("Expected bounded natural data")
        return str(int(value))

    def sequence(values):
        return "[" + ", ".join(values) + "]"

    def term(value):
        if not isinstance(value, list) or len(value) < 2:
            raise ValueError("Expected term data")
        if value[0] == "v" and len(value) == 2:
            return "(.var " + natural(value[1]) + ")"
        if value[0] == "f":
            return "(.app " + natural(value[1]) + " " + sequence(map(term, value[2:])) + ")"
        raise ValueError("Unknown term tag")

    def literal(value):
        polarity, atom = value
        if polarity not in ("pos", "neg"):
            raise ValueError("Unknown literal polarity")
        if atom[0] == "eq" and len(atom) == 3:
            encoded = ".equal " + term(atom[1]) + " " + term(atom[2])
        elif atom[0] == "pred" and len(atom) >= 2:
            encoded = ".predicate ⟨" + natural(atom[1]) + ", " + sequence(map(term, atom[2:])) + "⟩"
        else:
            raise ValueError("Unknown atom data")
        return "⟨" + str(polarity == "pos").lower() + ", " + encoded + "⟩"

    def clause(value):
        if not isinstance(value, list) or not value or value[0] != "clause":
            raise ValueError("Expected clause data")
        return sequence(map(literal, value[1:]))

    def substitution(value):
        if not isinstance(value, list) or not value or value[0] != "subst":
            raise ValueError("Expected substitution data")
        if any(not isinstance(entry, list) or len(entry) != 2 for entry in value[1:]):
            raise ValueError("Expected substitution entry")
        return sequence("(" + natural(entry[0]) + ", " + term(entry[1]) + ")"
                        for entry in value[1:])

    steps, final = [], None
    for node in root[3:]:
        if node[0] == "input" and len(node) == 3:
            steps.append("(.input " + natural(node[2]) + ")")
        elif node[0] == "eq-resolve" and len(node) == 9:
            steps.append("(.equalityResolution " + natural(node[2]) + " "
                         + clause(node[3]) + " " + clause(node[4]) + " " + term(node[5]) + " "
                         + term(node[6]) + " " + substitution(node[7]) + " " + clause(node[8]) + ")")
        elif node[0] == "factor" and len(node) == 7:
            steps.append("(.factor " + natural(node[2]) + " " + natural(node[3]) + " "
                         + natural(node[4]) + " " + substitution(node[5]) + " " + clause(node[6]) + ")")
        elif node[0] == "resolve" and len(node) == 8:
            steps.append("(.resolution " + natural(node[2]) + " " + natural(node[3]) + " "
                         + natural(node[4]) + " " + natural(node[5]) + " "
                         + substitution(node[6]) + " " + clause(node[7]) + ")")
        elif node[0] == "paramodulate" and len(node) == 11:
            root, path, direction = node[6:9]
            if root == ["equality-left"]:
                selected_root = ".equalityLeft"
            elif root == ["equality-right"]:
                selected_root = ".equalityRight"
            elif isinstance(root, list) and len(root) == 2 and root[0] == "argument":
                selected_root = ".argument " + natural(root[1])
            else:
                raise ValueError("Unknown root data")
            if not isinstance(path, list) or not path or path[0] != "path":
                raise ValueError("Expected path data")
            if direction not in ("forward", "reverse"):
                raise ValueError("Expected direction data")
            witness = "{ sourcePivot := " + natural(node[4]) + ", targetLiteral := " + natural(node[5])
            witness += ", root := " + selected_root + ", path := " + sequence(map(natural, path[1:]))
            witness += ", reverse := " + str(direction == "reverse").lower() + ", substitution := " + substitution(node[9]) + " }"
            steps.append("(.paramodulation " + natural(node[2]) + " " + natural(node[3]) + " " + witness + " " + clause(node[10]) + ")")
        elif node[0] == "final" and len(node) == 2:
            final = natural(node[1])
        else:
            raise ValueError("Unsupported witness step")
    if final is None or len(steps) > MAX_CERTIFICATE_NODES:
        raise ValueError("Missing final or too many nodes")
    return "⟨" + sequence(steps) + ", " + final + "⟩", steps, final


def node_equations(certificate, steps, final):
    text = certificate.decode("ascii")
    tokens = [(match.group(), match.start(), match.end())
              for match in re.finditer(r"[A-Za-z0-9_$-]+|[(),.|~]", text)]
    starts = [match.start() for match in re.finditer(r"\((?:input|eq-resolve|factor|resolve|paramodulate|final)\b", text)]
    if len(starts) != len(steps) + 1:
        raise ValueError("Expected one position per certificate node")
    last = next(index for index, (_, offset, _) in enumerate(tokens) if offset == starts[-1])
    # The final parser consumes four tokens: (, final, index, ).
    remaining = tokens[last + 4:]

    def state(items):
        return "{ tokens := [" + ", ".join("{ text := " + quote(word.encode()) + ", offset := " + str(offset) + " }"
                                             for word, offset, _ in items) + "], endOffset := " + str(len(certificate)) + " }"

    modules = []
    for index in reversed(range(len(starts))):
        input_tokens = [token for token in tokens if token[1] >= starts[index]]
        output = "([" + ", ".join(steps[index:]) + "], " + final + ")"
        body = (f"@[cbv_eval] theorem certificate_nodes_{index} : Fang.EqualityOrderedCertificateInput.nodes "
                f"{len(tokens) + 1 - index} {index} " + state(input_tokens) + " = .ok ("
                + output + ", " + state(remaining) + ") := by cbv\n\n")
        modules.append(("InstanceNodes" + str(index), body))
    return modules


def checked_module(certificate, problem, functions, predicates):
    expression, steps, final = certificate_constructor(certificate)
    support = '''/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EqualityOriginalCertificateInput

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

namespace FangEqualityCertificateKernel
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

theorem certificate_decodes (input : String) (tokens : List Fang.Frontend.Token)
    (size fuel : Nat) (certificate : Fang.Equality.Ordered.Certificate) (state : Fang.Frontend.State)
    (tokenized : Fang.Frontend.tokenize input = .ok tokens)
    (bytes : input.utf8ByteSize = size) (length : tokens.length + 1 = fuel)
    (parsed : FangQuantifiedEqualityCertificate.certificate fuel { tokens, endOffset := size } =
      .ok (certificate, state)) :
    FangQuantifiedEqualityCertificate.decodeCertificate input = .ok certificate := by
  simp [FangQuantifiedEqualityCertificate.decodeCertificate, tokenized, bytes, length, parsed,
    Bind.bind, Except.bind]
  rfl
end FangEqualityCertificateKernel

namespace EqInstance
'''
    # This module remains independent of the large extracted preprocessing
    # closure. Persistent suffix definitions share the lexer data/proofs.
    body = exact_string('proofBytes', certificate)
    body += 'def parsedCertificate : Fang.Equality.Ordered.Certificate := ' + expression + '\n\n'
    body += ''.join(lexer_parts('proofBytes', certificate, 'Frontend'))
    body += ''.join(code for _, code in node_equations(certificate, steps, final))
    tokens = [(m.group(), m.start()) for m in re.finditer(r'[A-Za-z0-9_$-]+|[(),.|~]', certificate.decode('ascii'))]
    spelling = '[' + ', '.join('{ text := ' + quote(word.encode()) + ', offset := ' + str(offset) + ' }' for word, offset in tokens) + ']'
    body += f'''theorem certificate_parses :
    FangQuantifiedEqualityCertificate.certificate {len(tokens) + 1}
      {{ tokens := {spelling}, endOffset := {len(certificate)} }} =
      .ok (parsedCertificate, {{ tokens := [], endOffset := {len(certificate)} }}) := by cbv

@[cbv_eval] theorem exact_certificate_decodes :
    FangQuantifiedEqualityCertificate.decodeCertificate proofBytes = .ok parsedCertificate :=
  FangEqualityCertificateKernel.certificate_decodes proofBytes _ {len(certificate)} {len(tokens) + 1}
    parsedCertificate _ proofBytes_tokenizes proofBytes_size (by decide +kernel) certificate_parses

theorem checked_bytes : FangQuantifiedEqualityCertificate.checkPrepared
    {problem} {functions} {predicates} {quote(certificate)} = .ok () := by
  change FangQuantifiedEqualityCertificate.checkPrepared _ _ _ proofBytes = .ok ()
  unfold FangQuantifiedEqualityCertificate.checkPrepared
  rw [exact_certificate_decodes]
  cbv

#print axioms EqInstance.exact_certificate_decodes
#print axioms EqInstance.checked_bytes
end EqInstance
'''
    # spelling_ofList_ascii is outside the lightweight imported closure and
    # not needed here: the final endpoint repeats the exact proof string.
    start = body.index('theorem exact_proofBytes_bytes :')
    end = body.index('def parsedCertificate', start)
    body = body[:start] + body[end:]
    return support + body


