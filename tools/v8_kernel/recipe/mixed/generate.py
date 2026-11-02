#!/usr/bin/env python3
"""Emit kernel goals from bounded, untrusted witnesses and sealed pair bytes."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat

SCHEMA = "fang-kernel-witness-2"
MAX_WITNESS = 16 << 20
MAX_SOURCE = 4096
MAX_CERTIFICATE = 65536
MAX_NODES = 4096
MAX_DEPTH = 64
LOWER = re.compile(r"[a-z][a-z0-9_]*\Z")
VARIABLE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Rejected(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


def natural(value, cap=2**32 - 1):
    require(type(value) is int and 0 <= value <= cap, "bounded natural required")
    return value


def fields(value, names):
    require(type(value) is dict and set(value) == set(names), "unexpected witness fields")


def sequence(value, cap=1024):
    require(type(value) is list and len(value) <= cap, "bounded list required")
    return value


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def validate(witness_bytes, source, certificate):
    require(len(witness_bytes) <= MAX_WITNESS, "witness byte cap")
    require(len(source) <= MAX_SOURCE and len(certificate) <= MAX_CERTIFICATE, "sealed pair byte cap")
    require(source.isascii() and certificate.isascii(), "ASCII pair required")
    try:
        witness = json.loads(witness_bytes, object_pairs_hook=no_duplicate_keys)
    except (ValueError, RecursionError) as error:
        raise Rejected("invalid witness JSON") from error
    fields(witness, ("schema", "source_hex", "certificate_hex", "functions", "predicates",
                     "source_declarations", "declarations", "standalone", "skolem", "blocks"))
    require(witness["schema"] == SCHEMA, "unknown witness schema")
    require(witness["source_hex"] == source.hex(), "source byte binding")
    require(witness["certificate_hex"] == certificate.hex(), "certificate byte binding")
    original = {}
    for key in ("functions", "predicates"):
        names, arities = [], []
        for symbol in sequence(witness[key], 256):
            require(type(symbol) is list and len(symbol) == 2, "symbol shape")
            name, arity = symbol
            require(type(name) is str and LOWER.fullmatch(name), "symbol spelling")
            names.append(name)
            arities.append(natural(arity, 256))
        require(len(names) == len(set(names)), "duplicate symbol spelling")
        original[key] = arities
    nodes = 0

    def visit(depth):
        nonlocal nodes
        nodes += 1
        require(nodes <= MAX_NODES and depth <= MAX_DEPTH, "structural witness cap")

    def term(value, functions, variables, depth):
        visit(depth)
        sequence(value, 3)
        require(value and value[0] in ("var", "fun"), "unsupported term")
        if value[0] == "var":
            require(len(value) == 2, "variable shape")
            require(natural(value[1]) < variables, "variable outside supplied table/bound")
        else:
            require(len(value) == 3, "function shape")
            symbol, args = natural(value[1]), sequence(value[2], 256)
            require(symbol < len(functions) and len(args) == functions[symbol], "function signature")
            for arg in args:
                term(arg, functions, variables, depth + 1)

    def atom(symbol, args, functions, predicates, variables, depth):
        require(natural(symbol) < len(predicates), "predicate index")
        require(len(sequence(args, 256)) == predicates[symbol], "predicate arity")
        for arg in args:
            term(arg, functions, variables, depth + 1)

    def formula(value, functions, predicates, variables, depth=0, nnf=False):
        visit(depth)
        sequence(value, 3)
        require(value, "empty formula")
        tag = value[0]
        if tag in ('truth', 'falsity'):
            require(len(value) == 1, 'constant formula shape')
        elif tag in ('conj', 'disj') or (tag == 'implies' and not nnf):
            require(len(value) == 3, 'binary formula shape')
            formula(value[1], functions, predicates, variables, depth + 1, nnf)
            formula(value[2], functions, predicates, variables, depth + 1, nnf)
        elif tag in ("all", "ex"):
            require(len(value) == 3 and natural(value[1]) < variables, "binder bound")
            formula(value[2], functions, predicates, variables, depth + 1, nnf)
        elif tag == "not" and not nnf:
            require(len(value) == 2, "negation shape")
            formula(value[1], functions, predicates, variables, depth + 1)
        elif tag == "atom" and not nnf:
            require(len(value) == 3, "atom shape")
            atom(value[1], value[2], functions, predicates, variables, depth)
        elif tag == "literal" and nnf:
            require(len(value) == 2, "literal formula shape")
            literal(value[1], functions, predicates, variables, depth)
        else:
            raise Rejected("unsupported formula constructor: " + str(tag))

    def literal(value, functions, predicates, variables, depth):
        require(type(value) is list and len(value) == 3 and type(value[0]) is bool, "literal shape")
        atom(value[1], value[2], functions, predicates, variables, depth)

    source_declarations = sequence(witness["source_declarations"], 16)
    require(source_declarations, "empty candidate")
    names, projection = [], []
    for declaration in source_declarations:
        fields(declaration, ("name", "variables", "body"))
        name = declaration["name"]
        require(type(name) is str and LOWER.fullmatch(name), "declaration spelling")
        names.append(name)
        variables = sequence(declaration["variables"], 64)
        require(all(type(name) is str and VARIABLE.fullmatch(name) for name in variables), "variable spelling")
        require(len(variables) == len(set(variables)), "duplicate variable table entry")
        body = sequence(declaration["body"], 2)
        require(len(body) == 2 and body[0] in ("cnf", "fof"), "declaration body shape")
        if body[0] == "cnf":
            for value in sequence(body[1], 256):
                literal(value, **original, variables=len(variables), depth=0)
        else:
            formula(body[1], **original, variables=len(variables))
            projection.append({"name": name, "variables": variables, "formula": body[1]})
    require(len(names) == len(set(names)), "duplicate declaration name")
    declarations = sequence(witness["declarations"], 16)
    require(declarations == projection, "FOF projection differs from ordered source declarations")
    standalone = sequence(witness["standalone"], 16)
    blocks = sequence(witness["blocks"], 16)
    require(len(declarations) == len(standalone) == len(blocks), "declaration/block counts")
    bounds = []
    for declaration, observed in zip(declarations, standalone):
        fields(declaration, ("name", "variables", "formula"))
        name = declaration["name"]
        require(type(name) is str and LOWER.fullmatch(name), "declaration spelling")
        variables = sequence(declaration["variables"], 64)
        require(all(type(name) is str and VARIABLE.fullmatch(name) for name in variables), "variable spelling")
        require(len(variables) == len(set(variables)), "duplicate variable table entry")
        formula(declaration["formula"], **original, variables=len(variables))
        fields(observed, ("validated", "rectified", "binder_count", "rectified_stats", "normalized", "normalized_stats"))
        bound = natural(observed["binder_count"], 64)
        bounds.append(bound)
        for key in ("validated", "rectified_stats", "normalized_stats"):
            require(len(sequence(observed[key], 8)) == 8, "core statistics shape")
            for value in observed[key]:
                natural(value, 5_000_000)
        formula(observed["rectified"], **original, variables=bound)
        formula(observed["normalized"], **original, variables=bound, nnf=True)
    skolem = witness["skolem"]
    fields(skolem, ("formulas", "functions", "predicates", "introduced", "statistics"))
    require(skolem["predicates"] == original["predicates"], "changed predicate table")
    functions = sequence(skolem["functions"], 320)
    for index, arity in enumerate(functions):
        natural(arity, 256 if index < len(original['functions']) else 64)
    require(functions[:len(original["functions"])] == original["functions"], "original function prefix")
    require(len(sequence(skolem["formulas"], 16)) == len(declarations), "Skolem output count")
    for value, bound in zip(skolem["formulas"], bounds):
        formula(value, functions, original["predicates"], bound, nnf=True)
    for introduced in sequence(skolem["introduced"], 64):
        require(type(introduced) is list and len(introduced) == 4, "origin shape")
        declaration, binder, function, universals = introduced
        require(natural(declaration) < len(bounds) and natural(binder) < bounds[declaration], "origin location")
        require(len(original["functions"]) <= natural(function) < len(functions), "fresh function index")
        require(len(sequence(universals, 64)) == functions[function], "Skolem arity/dependency count")
        require(all(natural(value) < bounds[declaration] for value in universals), "dependency bound")
    require(len(sequence(skolem["statistics"], 2)) == 2, "Skolem statistics")
    for value in skolem["statistics"]:
        natural(value, 5_000_000)
    for block, bound in zip(blocks, bounds):
        fields(block, ("removal_stats", "clauses", "clausifier_stats"))
        require(len(sequence(block["removal_stats"], 2)) == 2, "removal statistics")
        require(len(sequence(block["clausifier_stats"], 7)) == 7, "clausifier statistics")
        for value in block["removal_stats"] + block["clausifier_stats"]:
            natural(value, 5_000_000)
        for clause in sequence(block["clauses"], 1000):
            for value in sequence(clause, 256):
                literal(value, functions, original["predicates"], bound, 0)
    return witness


def vec(values):
    proof = "by simp; scalar_tac" if values else "by simp"
    return "(FangQuantifiedKernel.vector [" + ", ".join(values) + "] (" + proof + "))"


def term(value, numeric=False):
    tag, identifier, *args = value
    if numeric:
        return f"(.var {identifier})" if tag == "var" else f"(.app {identifier} [{', '.join(term(arg, True) for arg in args[0])}])"
    return f"(.Var {identifier}#u32)" if tag == "var" else f"(.Fun {identifier}#u32 {vec([term(arg) for arg in args[0]])})"


def formula(value, numeric=False):
    tag, *args = value
    if tag in ('truth', 'falsity'):
        return '(.' + (tag if numeric else {'truth': 'True', 'falsity': 'False'}[tag]) + ')'
    if tag in ('conj', 'disj', 'implies'):
        constructor = tag if numeric else {'conj': 'And', 'disj': 'Or', 'implies': 'Implies'}[tag]
        return '(.' + constructor + ' ' + formula(args[0], numeric) + ' ' + formula(args[1], numeric) + ')'
    if tag == "atom":
        symbol, terms = args
        return f"(.atom ⟨{symbol}, [{', '.join(term(arg, True) for arg in terms)}]⟩)" if numeric else f"(.Atom {symbol}#u32 {vec([term(arg) for arg in terms])})"
    if tag == "not":
        return f"(.{'neg' if numeric else 'Not'} {formula(args[0], numeric)})"
    binder, body = args
    constructor = {"all": "all" if numeric else "Forall", "ex": "ex" if numeric else "Exists"}[tag]
    return f"(.{constructor} {binder}{'' if numeric else '#u32'} {formula(body, numeric)})"


def source_declaration(value):
    kind, body = value['body']
    if kind == 'fof':
        return '.fof ' + formula(body, True)
    literals = ['⟨' + str(positive).lower() + ', ' + str(predicate) + ', ['
                + ', '.join(term(arg, True) for arg in args) + ']⟩'
                for positive, predicate, args in body]
    return '.cnf [' + ', '.join(literals) + ']'


def encoding_bounds(witness):
    widths = {len(witness["declarations"]), len(witness["functions"]), len(witness["predicates"])}
    identifiers = set()
    for key in ("functions", "predicates"):
        widths.update(arity for _, arity in witness[key])

    def visit(value):
        tag = value[0]
        if tag in ('truth', 'falsity'):
            return
        if tag in ('conj', 'disj', 'implies'):
            visit(value[1])
            visit(value[2])
        elif tag == "not":
            visit(value[1])
        elif tag in ("all", "ex"):
            identifiers.add(value[1])
            visit(value[2])
        elif tag == "var":
            identifiers.add(value[1])
        else:
            identifiers.add(value[1])
            widths.add(len(value[2]))
            for child in value[2]:
                visit(child)
    for declaration in witness["declarations"]:
        visit(declaration["formula"])
    return sorted(widths - {0}), sorted(identifiers - {0})


def emit(witness, source, certificate, namespace):
    require(re.fullmatch(r"[A-Z][A-Za-z0-9]*", namespace), "Lean namespace/module spelling")
    common = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Generated from untrusted witness data. Equations must be checked by Lean. -/\n"
    intro = f"\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    data = common + "import TransformPrimitives\nopen Aeneas Aeneas.Std\n" + intro
    data += "def signature : fang_skolem_core.fang_quantified_fof_core.Signature :=\n  ⟨" + vec([f"{arity}#usize" for _, arity in witness["functions"]]) + ", " + vec([f"{arity}#usize" for _, arity in witness["predicates"]]) + "⟩\n"
    for index, declaration in enumerate(witness["declarations"]):
        data += f"def formula{index} : fang_skolem_core.fang_quantified_fof_core.Formula :=\n  {formula(declaration['formula'])}\n"
    data += f"end {namespace}\n"
    modules = {namespace + "Data": data}
    decoded = common + "import QuantifiedInput\n" + intro
    decoded += "def input : String := " + json.dumps(source.decode("ascii")) + "\n"
    decoded += "def certificateBytes : String := " + json.dumps(certificate.decode("ascii")) + "\n"
    decoded += "def decoded : Fang.QuantifiedFrontend.Decoded := {\n  declarations := [" + ", ".join(source_declaration(declaration) for declaration in witness["source_declarations"]) + "]\n  state := {\n    tokens := []\n    endOffset := " + str(len(source)) + "\n    clauseNames := " + json.dumps([d["name"] for d in witness["source_declarations"]]) + "\n    «variables» := " + json.dumps(witness["source_declarations"][-1]["variables"]) + "\n"
    for key in ("functions", "predicates"):
        decoded += f"    {key} := [" + ", ".join("⟨" + json.dumps(name) + ", some " + str(arity) + "⟩" for name, arity in witness[key]) + "]\n"
    decoded += "  } }\ntheorem decode_eq : Fang.QuantifiedFrontend.decode input = .ok decoded := by cbv\n"
    decoded += f"#print axioms {namespace}.decode_eq\nend {namespace}\n"
    modules[namespace + "Decoded"] = decoded
    encoded = common + f"import OriginalInput\nimport {namespace}Data\nimport {namespace}Decoded\nopen Aeneas Aeneas.Std\n" + intro
    proof = 'by simp; scalar_tac' if witness['declarations'] else 'by simp'
    encoded += "def declarations : Slice fang_skolem_core.Declaration :=\n  Slice.from [" + ", ".join(f"⟨formula{index}, true⟩" for index in range(len(witness["declarations"]))) + "] (" + proof + ")\n"
    encoded += "def encoded : FangOriginalInput.Encoded := ⟨declarations, signature⟩\n"
    # This fixed structural simp set includes constructors absent from some inputs.
    encoded += "set_option linter.unusedSimpArgs false\n"
    encoded += "theorem encode_eq : FangOriginalInput.encodeInput decoded = .ok encoded := by\n"
    widths, identifiers = encoding_bounds(witness)
    for value in widths:
        encoded += f"  have width{value} : {value} ≤ Usize.max := by scalar_tac\n"
    for value in identifiers:
        encoded += f"  have identifier{value} : {value} ≤ U32.max := by scalar_tac\n"
    bound_names = [f"width{value}" for value in widths] + [f"identifier{value}" for value in identifiers]
    optional = bound_names + [f'formula{index}' for index in range(len(witness['declarations']))]
    encoded += "  simp [" + ''.join(name + ', ' for name in optional) + "FangOriginalInput.encodeInput, decoded, encoded, declarations, signature,\n    FangQuantifiedKernel.vector,\n    FangOriginalInput.readArities, FangOriginalInput.liftWidth, FangOriginalInput.checkedSlice,\n    FangOriginalInput.encodeAxioms, Fang.QuantifiedCertificate.formulas,\n    FangQuantifiedTransport.encodeSignature, FangQuantifiedTransport.encodeArities,\n    FangQuantifiedTransport.checkedVec, FangQuantifiedTransport.encodeDeclaration,\n    FangQuantifiedTransport.encodeFormula, FangQuantifiedTransport.encodeTerm,\n    FangQuantifiedTransport.encodeTerms, FangQuantifiedTransport.checkedU32,\n    FangQuantifiedTransport.checkedUsize, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]\n  all_goals (constructor <;> rfl)\n"
    if witness['functions'] or witness['predicates']:
        closing = "  repeat' (first | rfl | constructor)\n" if witness['declarations'] else '  rfl\n'
        encoded = encoded.replace('  all_goals (constructor <;> rfl)\n', closing)
    else:
        encoded = encoded.replace('  all_goals (constructor <;> rfl)\n', '')
    encoded += f"#print axioms {namespace}.encode_eq\nend {namespace}\n"
    modules[namespace + "Encoded"] = encoded
    for index, observed in enumerate(witness["standalone"]):
        name = namespace + "Validate" + str(index)
        theorem = f"validate{index}_eq"
        code = common + f"import {namespace}Data\nopen Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nopen fang_skolem_core.fang_quantified_fof_core\n" + intro
        code += f"theorem {theorem} : validate formula{index} signature skolemLimits.core =\n  .ok (.Ok ⟨{', '.join(str(n) + '#usize' for n in observed['validated'])}⟩) := by\n"
        code += f"  simp only [formula{index}, signature, validate, validate_with_scope, Work.new,\n    core_statistics_eq, Bindings.new, bind_ok]\n  generated_transform\n"
        code += f"#print axioms {namespace}.{theorem}\nend {namespace}\n"
        modules[name] = code
    return modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    # Each caller-supplied file is read once. The returned byte values are sealed inputs.
    source, certificate, witness_bytes = read_bounded(args.input, MAX_SOURCE), read_bounded(args.certificate, MAX_CERTIFICATE), read_bounded(args.witness, MAX_WITNESS)
    witness = validate(witness_bytes, source, certificate)
    modules = emit(witness, source, certificate, args.namespace)
    args.out.mkdir(parents=True, exist_ok=False)
    for name, code in modules.items():
        (args.out / (name + ".lean")).write_text(code, encoding="utf-8")
    report = {"status": "generated-unchecked", "scope": "prefix-literal validation equations only",
        "module_order": list(modules), "source_sha256": hashlib.sha256(source).hexdigest(),
        "certificate_sha256": hashlib.sha256(certificate).hexdigest(),
        "witness_sha256": hashlib.sha256(witness_bytes).hexdigest(),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "modules_sha256": {name: hashlib.sha256(code.encode()).hexdigest() for name, code in modules.items()}}
    (args.out / "generation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def read_bounded(path, cap):
    with path.open("rb") as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "regular input file required")
        value = stream.read(cap + 1)
    require(len(value) <= cap, "input file byte cap")
    return value


if __name__ == "__main__":
    main()
