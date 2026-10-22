#!/usr/bin/env python3
"""Untrusted source-witness generator; every semantic claim needs kernel checking."""
import argparse
import json
from pathlib import Path
import re

PUNCTUATION = {"(": "lparen", ")": "rparen", ",": "comma", ".": "period", "|": "disjoin", "~": "negate"}
LOWER = re.compile(r"[a-z][a-z0-9_]*\Z")
VARIABLE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
WORD = re.compile(r"[A-Za-z0-9_$-]+")

def quote(value):
    # Lean accepts Unicode escapes, but not JSON's short form-feed/backspace escapes.
    return '"' + "".join("\\u000c" if char == "\f" else "\\u0008" if char == "\b"
                         else json.dumps(char, ensure_ascii=True)[1:-1] for char in value) + '"'

def lean_list(items):
    return "[" + ", ".join(items) + "]"

def cons_proof(items):
    result = ".nil"
    for item in reversed(items):
        result = "(.cons (" + item + ") " + result + ")"
    return result

class Parser:
    def __init__(self, source):
        self.source = source
        self.tokens = []
        self.lexical = []
        self.functions = {}
        self.predicates = {}
        self.clauses = []
        self.position = 0
        offset = 0
        while offset < len(source):
            char = source[offset]
            if char in " \t\n\r\f\v":
                self.lexical.append(("space", char))
                offset += 1
            elif char in PUNCTUATION:
                self.tokens.append(char)
                self.lexical.append(("punctuation", char))
                offset += 1
            else:
                match = WORD.match(source, offset)
                if not match:
                    raise ValueError(f"Unsupported byte at {offset}")
                word = match.group()
                self.tokens.append(word)
                self.lexical.append(("word", word))
                offset = match.end()

    def peek(self):
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def take(self, expected=None):
        value = self.peek()
        if value is None or expected is not None and value != expected:
            raise ValueError(f"Expected {expected}, found {value} at token {self.position}")
        self.position += 1
        return value

    def symbol(self, table, name):
        if name not in table:
            table[name] = [len(table), None]

    def arity(self, table, name, arity):
        if table[name][1] is not None and table[name][1] != arity:
            raise ValueError("Inconsistent arity")
        table[name][1] = arity

    def arguments(self, variables):
        if self.peek() != "(":
            return []
        self.take("(")
        arguments = [self.term(variables)]
        while self.peek() == ",":
            self.take(",")
            arguments.append(self.term(variables))
        self.take(")")
        return arguments

    def term(self, variables):
        name = self.take()
        if VARIABLE.fullmatch(name):
            if name not in variables:
                variables[name] = len(variables)
            return (True, name, [])
        if not LOWER.fullmatch(name):
            raise ValueError("Invalid term name")
        self.symbol(self.functions, name)
        arguments = self.arguments(variables)
        self.arity(self.functions, name, len(arguments))
        return (False, name, arguments)

    def literal(self, variables):
        positive = self.peek() != "~"
        if not positive:
            self.take("~")
        name = self.take()
        if not LOWER.fullmatch(name):
            raise ValueError("Invalid predicate name")
        self.symbol(self.predicates, name)
        arguments = self.arguments(variables)
        self.arity(self.predicates, name, len(arguments))
        return (positive, name, arguments)

    def parse(self):
        names = set()
        while self.peek() is not None:
            self.take("cnf"); self.take("(")
            name = self.take()
            if not LOWER.fullmatch(name) or name in names:
                raise ValueError("Invalid or duplicate statement name")
            names.add(name)
            self.take(","); self.take("axiom"); self.take(","); self.take("(")
            variables = {}
            if self.peek() == "$false":
                self.take("$false")
                literals = []
            else:
                literals = [self.literal(variables)]
                while self.peek() == "|":
                    self.take("|")
                    literals.append(self.literal(variables))
            self.take(")"); self.take(")"); self.take(".")
            self.clauses.append((name, variables, literals))
        return self

def named_term(term):
    variable, name, arguments = term
    if variable:
        return "(.var " + quote(name) + ")"
    return "(.app " + quote(name) + " " + lean_list([named_term(term) for term in arguments]) + ")"

def numeric_term(term, functions, variables):
    variable, name, arguments = term
    if variable:
        return f"(.var {variables[name]})"
    return f"(.app {functions[name][0]} " + lean_list([numeric_term(term, functions, variables) for term in arguments]) + ")"

def argument_grammar(arguments):
    result = "(.last " + term_grammar(arguments[-1]) + ")"
    for term in reversed(arguments[:-1]):
        result = "(.more " + term_grammar(term) + " " + result + ")"
    return result

def term_grammar(term):
    variable, name, arguments = term
    if variable:
        return "(.variableTerm " + quote(name) + " _)"
    if not arguments:
        return "(.constant " + quote(name) + " _ (by decide))"
    return "(.application " + quote(name) + " " + argument_grammar(arguments) + ")"

def literal_grammar(literal):
    positive, name, arguments = literal
    return "(." + ("positive" if positive else "negative") + " " + term_grammar((False, name, arguments)) + ")"

def statement_grammar(clause):
    name, _, literals = clause
    if not literals:
        body = "(.falsity _)"
    else:
        body = "(.last " + literal_grammar(literals[-1]) + ")"
        for literal in reversed(literals[:-1]):
            body = "(.more " + literal_grammar(literal) + " " + body + ")"
        body = "(.disjunction " + body + ")"
    return "(.statement " + quote(name) + " " + body + ")"

def id_function(table):
    if not table:
        return "fun _ => 0"
    result = "0"
    for name, value in reversed(list(table.items())):
        index = value[0] if isinstance(value, list) else value
        result = "if name == " + quote(name) + f" then {index} else " + result
    return "fun name => " + result

def name_function(table):
    if not table:
        return "fun _ => \"\""
    clauses = []
    for name, value in table.items():
        index = value[0] if isinstance(value, list) else value
        clauses.append(f"| {index} => " + quote(name))
    return "fun id => match id with " + " ".join(clauses) + " | _ => \"\""

def arity_function(table):
    if not table:
        return "fun _ => none"
    result = "none"
    for name, (_, arity) in reversed(list(table.items())):
        result = "if name == " + quote(name) + f" then some {arity} else " + result
    return "fun name => " + result

def term_encoding(term, functions, variables):
    variable, name, arguments = term
    if variable:
        return "(.var " + quote(name) + " (by decide))"
    return ("(.app " + quote(name) + " " + lean_list([named_term(term) for term in arguments])
            + " " + lean_list([numeric_term(term, functions, variables) for term in arguments])
            + " (by decide) (by decide) "
            + cons_proof([term_encoding(term, functions, variables) for term in arguments]) + ")")

def literal_encoding(literal, functions, variables):
    return "⟨by decide, by decide, by decide, by decide, " + cons_proof([
        term_encoding(term, functions, variables) for term in literal[2]]) + "⟩"

def byte_list(text):
    return lean_list([str(byte) for byte in text.encode("ascii")])

def lexical_witness(items):
    result = ".empty"
    for index in range(len(items) - 1, -1, -1):
        kind, text = items[index]
        if kind == "space":
            first = ".whitespace (by simp [IsSpace])"
        elif kind == "punctuation":
            first = ".token (.punctuation ." + PUNCTUATION[text] + ")"
        else:
            boundary = ("by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]"
                        if index + 1 < len(items) else "by intro byte tail impossible; cases impossible")
            if text == "$false":
                spelled = "(.falsity rfl)"
            else:
                lower = bool(LOWER.fullmatch(text))
                valid = ("⟨" + str(ord(text[0])) + ", " + byte_list(text[1:]) + ", rfl, by simp ["
                         + ("IsLower" if lower else "IsUpper") + "], by simp [IsLower, IsUpper, IsDigit]⟩")
                spelled = "(." + ("lower" if lower else "variableWord") + " " + quote(text) + " rfl " + valid + ")"
            first = (".token (.word (front := " + byte_list(text) + ") rfl "
                     + "⟨by simp [IsWord, IsLower, IsUpper, IsDigit], " + boundary + "⟩ " + spelled + ")")
        result = "(" + first + "\n  " + result + ")"
    return result

def certificate_source(text):
    words = re.findall(r"\(|\)|[^\s()]+", text)
    position = 0
    def expression():
        nonlocal position
        if position >= len(words):
            raise ValueError("Truncated certificate")
        value = words[position]
        position += 1
        if value == "(":
            values = []
            while position < len(words) and words[position] != ")":
                values.append(expression())
            if position >= len(words):
                raise ValueError("Unterminated certificate list")
            position += 1
            return values
        if value == ")":
            raise ValueError("Unexpected certificate closing delimiter")
        return value
    def natural(value):
        if not isinstance(value, str) or not re.fullmatch(r"[0-9]+", value):
            raise ValueError("Expected certificate natural number")
        return str(int(value))
    def term(value):
        if isinstance(value, list) and len(value) == 2 and value[0] == "v":
            return "(.var " + natural(value[1]) + ")"
        if isinstance(value, list) and len(value) >= 2 and value[0] == "f":
            return "(.app " + natural(value[1]) + " " + lean_list([term(child) for child in value[2:]]) + ")"
        raise ValueError("Invalid certificate term")
    def substitution(value):
        if not isinstance(value, list) or not value or value[0] != "subst":
            raise ValueError("Invalid substitution")
        bindings = []
        for entry in value[1:]:
            if not isinstance(entry, list) or len(entry) != 2:
                raise ValueError("Invalid binding")
            bindings.append("(" + natural(entry[0]) + ", " + term(entry[1]) + ")")
        return lean_list(bindings)
    def clause(value):
        if not isinstance(value, list) or not value or value[0] != "clause":
            raise ValueError("Invalid clause")
        result = []
        for literal in value[1:]:
            if not isinstance(literal, list) or len(literal) < 2 or literal[0] not in ("pos", "neg"):
                raise ValueError("Invalid certificate literal")
            result.append("{ positive := " + str(literal[0] == "pos").lower() + ", atom := { pred := "
                          + natural(literal[1]) + ", args := " + lean_list([term(child) for child in literal[2:]]) + " } }")
        return lean_list(result)
    parsed = expression()
    if position != len(words) or not isinstance(parsed, list) or parsed[:2] != ["fang-proof", "1"]:
        raise ValueError("Invalid certificate header or trailing input")
    steps = []
    final = None
    for node_index, node in enumerate(parsed[2:], start=2):
        if not isinstance(node, list) or len(node) < 2:
            raise ValueError("Invalid certificate node")
        if node[0] == "final":
            if len(node) != 2 or node_index != len(parsed) - 1:
                raise ValueError("Invalid final node")
            final = natural(node[1])
            continue
        if int(natural(node[1])) != len(steps):
            raise ValueError("Non-sequential node ID")
        if node[0] == "input" and len(node) == 3:
            steps.append(".input " + natural(node[2]))
        elif node[0] == "factor" and len(node) == 7:
            steps.append(".factor " + " ".join(natural(value) for value in node[2:5]) + " "
                         + substitution(node[5]) + " " + clause(node[6]))
        elif node[0] == "resolve" and len(node) == 8:
            steps.append(".resolve " + " ".join(natural(value) for value in node[2:6]) + " "
                         + substitution(node[6]) + " " + clause(node[7]))
        else:
            raise ValueError("Unsupported certificate node")
    if final is None:
        raise ValueError("Missing final node")
    return "Certificate.mk " + lean_list(["(" + step + ")" for step in steps]) + " " + final

def generate(case_directory):
    raw = (case_directory / "input.p").read_bytes()
    certificate_bytes = (case_directory / "proof.fang").read_bytes()
    source = raw.decode("ascii")
    parser = Parser(source).parse()
    output = """/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Generated witnesses are checked against an independent declarative byte grammar.
The theorem covers the embedded original input bytes. General executable decoder
correctness remains a separate open obligation. The certificate AST is checked
directly; certificate text decoding is a separate replay path.
-/
import Fang.SourceLexing

namespace Fang.SourceInstance
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

"""
    output += "def originalInput : String := " + quote(source) + "\n\n"
    output += "def originalCertificate : String := " + quote(certificate_bytes.decode("ascii")) + "\n\n"
    numeric_clauses = []
    for _, variables, literals in parser.clauses:
        numeric_clauses.append(lean_list(["{ positive := " + str(positive).lower()
            + ", atom := { pred := " + str(parser.predicates[predicate][0]) + ", args := "
            + lean_list([numeric_term(term, parser.functions, variables) for term in arguments]) + " } }"
            for positive, predicate, arguments in literals]))
    output += "def problem : Problem := " + lean_list(numeric_clauses) + "\n\n"
    output += "def certificate : Certificate := " + certificate_source(certificate_bytes.decode("ascii")) + "\n\n"
    output += "open Fang.Source Fang.Source.Grammar\n\n"
    output += "def originalBytes : Bytes := spelling originalInput\n\n"
    output += "def signature : Source.Signature := ⟨" + arity_function(parser.functions) + ", " + arity_function(parser.predicates) + "⟩\n\n"
    output += "def symbols : Source.Symbols := ⟨" + ", ".join([id_function(parser.functions), name_function(parser.functions), id_function(parser.predicates), name_function(parser.predicates)]) + "⟩\n\n"
    named_clauses = []
    encoded_clauses = []
    for index, (name, variables, literals) in enumerate(parser.clauses):
        output += f"def variables{index} : Source.Variables := ⟨" + id_function(variables) + ", " + name_function(variables) + "⟩\n\n"
        named_literals = ["⟨" + str(positive).lower() + ", " + quote(predicate) + ", "
                          + lean_list([named_term(term) for term in arguments]) + "⟩"
                          for positive, predicate, arguments in literals]
        named_clauses.append("⟨" + quote(name) + ", " + lean_list(named_literals) + "⟩")
        encoded_clauses.append(f"⟨variables{index}, " + cons_proof([
            literal_encoding(literal, parser.functions, variables) for literal in literals]) + "⟩")
    output += "def namedProblem : Source.Problem := " + lean_list(named_clauses) + "\n\n"
    token_values = []
    for token in parser.tokens:
        if token in PUNCTUATION:
            token_values.append("." + PUNCTUATION[token])
        elif token == "$false":
            token_values.append(".falseLiteral")
        else:
            token_values.append("(." + ("lower" if LOWER.fullmatch(token) else "variable") + " " + quote(token) + ")")
    output += "def sourceTokens : List Source.Grammar.Token := " + lean_list(token_values) + "\n\n"
    output += "theorem tokenizes : Tokenization originalBytes sourceTokens := by\n  exact " + lexical_witness(parser.lexical) + "\n\n"
    parsed = ".empty"
    for clause in reversed(parser.clauses):
        parsed = "(.statement " + statement_grammar(clause) + " " + parsed + ")"
    output += "theorem syntax_parses : ProblemTokens sourceTokens namedProblem := by\n  exact " + parsed + "\n\n"
    output += "theorem encoding : ProblemEncoding signature symbols namedProblem problem := by\n  exact ⟨by decide, " + cons_proof(encoded_clauses) + "⟩\n\n"
    output += """theorem accepted : check (preprocess problem) certificate = true := by decide +kernel

theorem original_input_unsat : ¬ BytesSatisfiable originalBytes :=
  original_bytes_unsat_of_witness ⟨sourceTokens, tokenizes, syntax_parses⟩ encoding certificate accepted

#print axioms tokenizes
#print axioms syntax_parses
#print axioms encoding
#print axioms original_input_unsat

end Fang.SourceInstance
"""
    return output

if __name__ == "__main__":
    cli = argparse.ArgumentParser()
    cli.add_argument("case_directory", type=Path, help="Directory containing input.p and proof.fang")
    cli.add_argument("--out", required=True, type=Path)
    arguments = cli.parse_args()
    arguments.out.write_text(generate(arguments.case_directory), encoding="utf-8")
