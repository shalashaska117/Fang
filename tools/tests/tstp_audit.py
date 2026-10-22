"""Test-side semantic audit of Fang's emitted CNF derivation subset.

This is a dynamic independent check, not a production verifier or a Lean proof.
It operates on printed clauses, checks each inference and its dependency graph,
and compares the printed witness with the original internal certificate.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import re


def tokens(text):
    result, offset = [], 0
    while offset < len(text):
        char = text[offset]
        if char in " \t\r\n\v\f":
            offset += 1
        elif char == "'":
            offset += 1
            value = ""
            while offset < len(text) and text[offset] != "'":
                if text[offset] == "\\":
                    offset += 1
                    if offset >= len(text) or text[offset] not in "\\'":
                        raise ValueError("invalid quoted escape")
                if not 32 <= ord(text[offset]) <= 126:
                    raise ValueError("invalid quoted byte")
                value += text[offset]
                offset += 1
            if offset == len(text):
                raise ValueError("unclosed quote")
            result.append(value)
            offset += 1
        elif char in "(),[].|~":
            result.append(char)
            offset += 1
        else:
            match = re.match(r"[A-Za-z_$][A-Za-z0-9_$]*|[0-9]+", text[offset:])
            if not match:
                raise ValueError("unexpected token")
            value = match.group()
            result.append(int(value) if value.isdigit() else value)
            offset += len(value)
    return result


class Parser:
    def __init__(self, text):
        self.items = tokens(text)
        self.index = 0

    def peek(self):
        return self.items[self.index] if self.index < len(self.items) else None

    def take(self, wanted=None):
        value = self.peek()
        if value is None or wanted is not None and wanted != value:
            raise ValueError(f"expected {wanted!r}, got {value!r}")
        self.index += 1
        return value

    def general(self):
        if self.peek() == "[":
            self.take("[")
            values = []
            while self.peek() != "]":
                values.append(self.general())
                if self.peek() != "]":
                    self.take(",")
            self.take("]")
            return values
        name = self.take()
        if self.peek() != "(":
            return name
        self.take("(")
        args = [self.general()]
        while self.peek() == ",":
            self.take(",")
            args.append(self.general())
        self.take(")")
        return name, tuple(args)

    def term(self):
        name = self.take()
        if not isinstance(name, str):
            raise ValueError("numeric object outside the supported fragment")
        if name[0].isupper():
            return "var", name
        args = []
        if self.peek() == "(":
            self.take("(")
            args.append(self.term())
            while self.peek() == ",":
                self.take(",")
                args.append(self.term())
            self.take(")")
        return "fun", name, tuple(args)

    def clause(self):
        if self.peek() == "$false":
            self.take()
            return []
        values = []
        while True:
            positive = self.peek() != "~"
            if not positive:
                self.take()
            _, name, args = self.term()
            values.append((positive, name, args))
            if self.peek() != "|":
                return values
            self.take()

    def records(self):
        rows = []
        while self.peek() is not None:
            self.take("cnf")
            self.take("(")
            name = self.take()
            self.take(",")
            role = self.take()
            self.take(",")
            self.take("(")
            clause = self.clause()
            self.take(")")
            source = None
            if self.peek() == ",":
                self.take()
                source = self.general()
            self.take(")")
            self.take(".")
            rows.append({"name": name, "role": role, "clause": clause, "source": source})
        return rows


def map_term(term, variable):
    if term[0] == "var":
        return variable(term[1])
    return "fun", term[1], tuple(map_term(child, variable) for child in term[2])


def map_clause(clause, variable):
    return [(positive, name, tuple(map_term(term, variable) for term in args))
            for positive, name, args in clause]


def canonical(clause):
    names = {}
    def variable(name):
        if name not in names:
            names[name] = "X" + str(len(names))
        return "var", names[name]
    return map_clause(clause, variable)


def node_data(info):
    if len(info) < 2 or info[0] != ("status", ("thm",)):
        raise ValueError("missing or misplaced status(thm)")
    if sum(isinstance(item, tuple) and item[0] == "status" for item in info) != 1:
        raise ValueError("duplicate status")
    name, fields = info[1]
    if name != "fang_node" or len(fields) != 1 or not isinstance(fields[0], int):
        raise ValueError("missing node witness")
    return fields[0]


def witness_term(value):
    name, fields = value
    if name == "var" and len(fields) == 1 and isinstance(fields[0], int):
        return "var", "X" + str(fields[0])
    if name == "fun" and len(fields) == 2 and isinstance(fields[1], list):
        return "fun", fields[0], tuple(witness_term(term) for term in fields[1])
    raise ValueError("malformed substitution term")


def substitution(value):
    name, fields = value
    if name != "fang_substitution" or len(fields) != 1 or not isinstance(fields[0], list):
        raise ValueError("malformed substitution")
    result = {}
    for binding in fields[0]:
        name, fields = binding
        if name != "binding" or len(fields) != 2 or not isinstance(fields[0], int):
            raise ValueError("malformed binding")
        key = "X" + str(fields[0])
        if key in result:
            raise ValueError("duplicate binding")
        result[key] = witness_term(fields[1])
    return result


def certificate(text):
    items = re.findall(r"\(|\)|[^\s()]+", text)
    def read(index):
        if items[index] != "(":
            atom = items[index]
            return (int(atom) if atom.isdigit() else atom), index + 1
        values, index = [], index + 1
        while index < len(items) and items[index] != ")":
            value, index = read(index)
            values.append(value)
        if index == len(items):
            raise ValueError("unclosed internal certificate")
        return values, index + 1
    result, end = read(0)
    if end != len(items) or result[:2] != ["fang-proof", 1]:
        raise ValueError("invalid internal certificate")
    return result[2:-1], result[-1][1]


def audit(source_text, proof_text, output_text, file_label):
    original = Parser(source_text).records()
    original_map = {row["name"]: row for row in original}
    steps, final_id = certificate(proof_text)
    functions, predicates = [], []
    def visit(term):
        if term[0] == "fun":
            if term[1] not in functions:
                functions.append(term[1])
            for child in term[2]:
                visit(child)
    for row in original:
        for _, pred, args in row["clause"]:
            if pred not in predicates:
                predicates.append(pred)
            for term in args:
                visit(term)
    def internal_term(term):
        if term[0] == "v":
            return "var", "X" + str(term[1])
        if term[0] != "f":
            raise ValueError("unknown certificate term")
        return "fun", functions[term[1]], tuple(internal_term(child) for child in term[2:])
    rows, checked, dependencies = Parser(output_text).records(), {}, {}
    node_labels = {}
    for row in rows:
        name, body, origin = row["name"], row["clause"], row["source"]
        if name in checked:
            raise ValueError("duplicate output label")
        if origin is None:
            raise ValueError("missing source")
        tag, data = origin
        if tag == "file":
            if row["role"] != "axiom" or len(data) != 2 or data[0] != file_label:
                raise ValueError("incorrect file reference")
            source_name = data[1]
            if name != source_name or source_name not in original_map:
                raise ValueError("incorrect source name")
            if canonical(body) != canonical(original_map[source_name]["clause"]):
                raise ValueError("leaf is not the ordered alpha-equivalent source clause")
            dependencies[name] = []
            source_index = [r["name"] for r in original].index(source_name)
            for step in steps:
                if step[0] == "input" and step[2] == source_index:
                    node_labels[step[1]] = name
        elif tag == "inference":
            if row["role"] != "plain" or len(data) != 3:
                raise ValueError("incorrect inference record")
            rule, info, parents = data
            node_id = node_data(info)
            if any(parent not in checked for parent in parents):
                raise ValueError("missing or forward parent")
            step = steps[node_id]
            if step[1] != node_id:
                raise ValueError("internal node ID differs")
            if rule != "fang_standardize_apart" and name != f"fang:step:{node_id}":
                raise ValueError("generated node label differs")
            clauses = [checked[parent] for parent in parents]
            if rule == "fang_deduplicate":
                if len(clauses) != 1 or len(info) != 2 or step[0] != "input":
                    raise ValueError("invalid deduplication metadata")
                expected = list(dict.fromkeys(clauses[0]))
                if parents[0] != original[step[2]]["name"]:
                    raise ValueError("deduplication source differs")
                node_labels[node_id] = name
            elif rule == "fang_standardize_apart":
                if len(clauses) != 1 or len(info) != 3 or step[0] != "resolve":
                    raise ValueError("invalid renaming metadata")
                side = info[2]
                if side not in [("renaming", ("even",)), ("renaming", ("odd",))]:
                    raise ValueError("invalid parity map")
                right = int(side[1][0] == "odd")
                if parents != [node_labels[step[4] if right else step[2]]]:
                    raise ValueError("renaming parent differs")
                expected = map_clause(clauses[0], lambda v: ("var", "X" + str(2 * int(v[1:]) + right)))
                if name != f"fang:{'right' if right else 'left'}:{node_id}":
                    raise ValueError("renaming ID differs")
            else:
                if len(info) != 4 or info[2][0] != "pivots":
                    raise ValueError("missing inference witness")
                i, j = info[2][1]
                sigma = substitution(info[3])
                actual_sigma = {"X" + str(binding[0]): internal_term(binding[1])
                                for binding in step[-2][1:]}
                if list(sigma.items()) != list(actual_sigma.items()):
                    raise ValueError("printed substitution differs from certificate")
                apply = lambda c: map_clause(c, lambda v: sigma.get(v, ("var", v)))
                if rule == "fang_factoring":
                    if step[0] != "factor" or [i, j] != step[3:5] or parents != [node_labels[step[2]]]:
                        raise ValueError("factoring witness differs")
                    if len(clauses) != 1 or i == j or apply([clauses[0][i]]) != apply([clauses[0][j]]):
                        raise ValueError("invalid factoring")
                    expected = apply(clauses[0][:j] + clauses[0][j + 1:])
                elif rule == "fang_resolution":
                    if step[0] != "resolve" or [i, j] != [step[3], step[5]]:
                        raise ValueError("resolution witness differs")
                    if parents != [f"fang:left:{node_id}", f"fang:right:{node_id}"] or len(clauses) != 2:
                        raise ValueError("resolution parents differ")
                    left, right = apply([clauses[0][i]])[0], apply([clauses[1][j]])[0]
                    if left[0] == right[0] or left[1:] != right[1:]:
                        raise ValueError("invalid resolution")
                    expected = apply(clauses[0][:i] + clauses[0][i + 1:] + clauses[1][:j] + clauses[1][j + 1:])
                else:
                    raise ValueError("unknown inference")
                claimed = [(literal[0] == "pos", predicates[literal[1]],
                            tuple(internal_term(term) for term in literal[2:])) for literal in step[-1][1:]]
                if body != claimed:
                    raise ValueError("printed clause differs from internal claimed clause")
                node_labels[node_id] = name
            if body != expected:
                raise ValueError("printed result differs from inference")
            dependencies[name] = parents
        else:
            raise ValueError("unknown source kind")
        checked[name] = body
    if not rows or rows[-1]["clause"] or node_labels.get(final_id) != rows[-1]["name"]:
        raise ValueError("final clause is not the internal false root")
    reachable, pending = set(), [rows[-1]["name"]]
    while pending:
        name = pending.pop()
        if name not in reachable:
            reachable.add(name)
            pending.extend(dependencies[name])
    if reachable != set(checked):
        raise ValueError("irrelevant output node")
    return {"rows": len(rows), "leaves": sum(row["role"] == "axiom" for row in rows),
            "final_name": rows[-1]["name"]}
