"""Untrusted FOF replay witnesses; Lean must check every generated equation."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
# Uses the checked-equation decomposition from ground-fof-kernel-replay v6.
from dataclasses import dataclass
import re


NAMESPACE = "Fang.FOFKernelReplay.Instance"
MODULES = ("FofInstanceData", "FofInstanceInput", "FofInstanceCertificate", "FofInstanceProof")
AUDITS = frozenset({"exact_original_bytes_unsat", "exact_input_bytes",
                   "exact_certificate_bytes", "exact_certificate_decodes", "exact_acceptance"})
MAX_INPUT_BYTES = 4096
MAX_CERTIFICATE_BYTES = 65536
MAX_CERTIFICATE_NODES = 100
MAX_GENERATED_BYTES = 16 << 20
CONSTRUCTOR_TOKEN = re.compile(
    r"\s+|Certificate\.mk|\.(?:var|app|input|factor|resolve)\b|positive\b|atom\b|pred\b|args\b|true\b|false\b|[0-9]+|:=|[\[\](){},]")
HEADER = re.compile(rb"[ \t\r\n\f\v]*\([ \t\r\n\f\v]*fang-proof[ \t\r\n\f\v]+2[ \t\r\n\f\v]+"
    rb"\([ \t\r\n\f\v]*preprocessing[ \t\r\n\f\v]+ground-fof-distributive-v1[ \t\r\n\f\v]*\)")


class ReplayLimit(ValueError):
    """This bounded replay profile cannot process the supplied data."""


@dataclass(frozen=True)
class Replay:
    modules: tuple[tuple[str, str], ...]
    input_bytes: int
    certificate_bytes: int
    certificate_nodes: int


def quote(data):
    text = data.decode("ascii")
    return '"' + "".join("\\u%04x" % ord(char) if ord(char) < 32 else
                         "\\" + char if char in ('"', "\\") else char for char in text) + '"'


def byte_list(data):
    return "[" + ", ".join(map(str, data)) + "]"


def characters(data):
    return "[" + ", ".join("Char.ofNat " + str(byte) for byte in data) + "]"


def exact_string(label, data):
    chars = characters(data)
    return f'''def {label} : String := {quote(data)}

@[cbv_eval] theorem {label}_characters : {label}.toList = {chars} := by
  exact String.toList_ofList

@[cbv_eval] theorem {label}_size : {label}.utf8ByteSize = {len(data)} := by
  change (String.ofList {chars}).utf8ByteSize = _
  rw [Fang.FOFKernelReplay.size_ofList]
  decide +kernel

theorem exact_{label}_bytes : Fang.Source.Grammar.spelling {label} = {byte_list(data)} := by
  change Fang.Source.Grammar.spelling (String.ofList {chars}) = _
  rw [Fang.Source.Grammar.spelling_ofList_ascii _ (by decide +kernel)]
  rfl

'''


def lexer_equations(label, data, namespace):
    pattern = r"[A-Za-z0-9_$-]+|=>|[(),.|~&]" if namespace == "FOFFrontend" else r"[A-Za-z0-9_$-]+|[(),.|~]"
    text = data.decode("ascii")
    if re.sub(pattern + r"|[ \t\n\r\f\v]", "", text):
        raise ValueError("Character outside the declared replay token vocabulary")
    tokens = [(match.group(), match.start()) for match in re.finditer(pattern, text)]

    def token_list(items):
        return "[" + ", ".join("{ text := " + quote(word.encode("ascii")) + ", offset := " + str(offset) + " }"
            for word, offset in items) + "]"

    boundaries = sorted({0, *(offset for _, offset in tokens[::10])})
    result = ""
    for number, offset in reversed(list(enumerate(boundaries))):
        steps = len(re.findall(pattern + r"|[ \t\n\r\f\v]", text[:offset]))
        result += (f"@[cbv_eval] theorem {label}_lex_{number} : Fang.{namespace}.lexAux "
            f"{len(data) + 1 - steps} {characters(data[offset:])} {offset} = .ok "
            + token_list([(word, pos) for word, pos in tokens if pos >= offset]) + " := by cbv\n\n")
        if len(result) > MAX_GENERATED_BYTES:
            raise ReplayLimit("Generated lexer witness exceeds the replay byte cap")
    return result + (f"@[cbv_eval] theorem {label}_tokenizes : Fang.{namespace}.tokenize {label} = .ok "
        + token_list(tokens) + " := by cbv\n\n")


def generate(source, certificate, constructor):
    """Return fixed-name Lean modules for the actual source and version-2 bytes.

    `constructor` is the pinned existing version-1 certificate AST emitter.
    Only its data expression is reused. The generated decoder equation is about
    the unchanged version-2 input, so header conversion is not a trusted proof
    step. The independent audit must be made from the captured bytes separately.
    """
    if len(source) > MAX_INPUT_BYTES or len(certificate) > MAX_CERTIFICATE_BYTES:
        raise ReplayLimit("Input or certificate exceeds this kernel replay profile's byte cap")
    source.decode("ascii")
    certificate.decode("ascii")
    header = HEADER.match(certificate)
    if header is None:
        raise ValueError("Expected version-2 ground-FOF certificate envelope")
    legacy = b"(fang-proof 1\n" + certificate[header.end():]
    try:
        expression = constructor(legacy.decode("ascii"))
    except RecursionError as error:
        raise ReplayLimit("Certificate nesting exceeds the witness generator's stack limit") from error
    cursor = 0
    while cursor < len(expression):
        token = CONSTRUCTOR_TOKEN.match(expression, cursor)
        if token is None:
            raise ValueError("Certificate emitter returned non-constructor syntax")
        cursor = token.end()
    nodes = len(re.findall(r"\.(?:input|factor|resolve)\b", expression))
    if nodes > MAX_CERTIFICATE_NODES:
        raise ReplayLimit("Certificate exceeds this kernel replay profile's node cap")
    bodies = [
        exact_string("input", source) + exact_string("certificate", certificate)
            + "def parsedCertificate : Fang.Certificate := " + expression + "\n\n",
        lexer_equations("input", source, "FOFFrontend"),
        lexer_equations("certificate", certificate, "Frontend") + '''@[cbv_eval] theorem exact_certificate_decodes :
    Fang.FOFVersioned.decodeCertificate certificate = .ok parsedCertificate := by cbv

''',
        '''theorem exact_acceptance :
    Fang.FOFVersioned.accepts input certificate = .ok true := by
  unfold Fang.FOFVersioned.accepts
  rw [exact_certificate_decodes]
  cbv

theorem exact_original_bytes_unsat :
    ¬ Fang.FOFGrammar.BytesSatisfiable ''' + byte_list(source) + ''' := by
  have proved := Fang.FOFVersioned.accepts_original_unsat exact_acceptance
  simpa only [exact_input_bytes] using proved

''',
    ]
    modules = []
    previous = "Fang.FOF.Replay"
    for name, body in zip(MODULES, bodies, strict=True):
        contents = ("import " + previous + "\n\nset_option maxRecDepth 10000\n"
            "set_option maxHeartbeats 4000000\nset_option cbv.maxSteps 20000000\n\n"
            "namespace " + NAMESPACE + "\n\n" + body + "end " + NAMESPACE + "\n")
        modules.append((name, contents))
        previous = name
    if sum(len(text.encode("utf-8")) for _, text in modules) > MAX_GENERATED_BYTES:
        raise ReplayLimit("Generated modules exceed the replay byte cap")
    return Replay(tuple(modules), len(source), len(certificate), nodes)


def audit_source(source, certificate):
    """Fixed audit bound independently to captured bytes, not emitted strings."""
    source_value = "[" + ", ".join(str(value) for value in source) + "]"
    certificate_value = "[" + ", ".join(str(value) for value in certificate) + "]"
    return ("import FofInstanceProof\n\nnamespace Fang.FOFKernelAudit\n\n"
        "theorem exact_original_bytes_unsat : ¬ Fang.FOFGrammar.BytesSatisfiable " + source_value
        + " := " + NAMESPACE + ".exact_original_bytes_unsat\n\n"
        "theorem exact_input_bytes : Fang.Source.Grammar.spelling " + NAMESPACE + ".input = "
        + source_value + " := " + NAMESPACE + ".exact_input_bytes\n\n"
        "theorem exact_certificate_bytes : Fang.Source.Grammar.spelling " + NAMESPACE + ".certificate = "
        + certificate_value + " := " + NAMESPACE + ".exact_certificate_bytes\n\n"
        "theorem exact_certificate_decodes : Fang.FOFVersioned.decodeCertificate " + NAMESPACE
        + ".certificate = .ok " + NAMESPACE + ".parsedCertificate := " + NAMESPACE + ".exact_certificate_decodes\n\n"
        "theorem exact_acceptance : Fang.FOFVersioned.accepts " + NAMESPACE + ".input " + NAMESPACE
        + ".certificate = .ok true := " + NAMESPACE + ".exact_acceptance\n\nend Fang.FOFKernelAudit\n\n"
        + "".join("#print axioms Fang.FOFKernelAudit." + name + "\n" for name in sorted(AUDITS)))
