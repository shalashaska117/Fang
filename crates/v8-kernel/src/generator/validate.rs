// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `validate` of recipe/mixed/generate.py: bounded shape checks on the untrusted witness,
//! in revision 7's order and with its messages. Every refusal here is a ValueError in Python,
//! so `Rejected`. On success the witness is returned typed.

use fang_json::{Number, Object, Value};

use super::py;
use super::witness::{
    Block, Body, Declaration, Formula, Literal, Origin, Skolem, SourceDeclaration, Standalone,
    Symbol, Term, Witness,
};
use super::{Outcome, json_dumps, rejected, require};

pub(crate) const SCHEMA: &str = "fang-kernel-witness-2";
const MAX_WITNESS: usize = 16 << 20;
const MAX_SOURCE: usize = 4096;
const MAX_CERTIFICATE: usize = 65536;
const MAX_NODES: u64 = 4096;
const MAX_DEPTH: u64 = 64;
const NATURAL: u64 = (1 << 32) - 1;

/// `natural(value, cap)`: an int (not a bool) in 0..=cap.
fn natural(value: &Value, cap: u64) -> Outcome<u64> {
    match value {
        Value::Number(Number::Integer(integer)) => match integer.as_u64() {
            Some(number) if number <= cap => Ok(number),
            _ => Err(rejected("bounded natural required")),
        },
        _ => Err(rejected("bounded natural required")),
    }
}

/// `fields(value, names)`: a dict with exactly these keys.
pub(crate) fn fields<'a>(value: &'a Value, names: &[&str], message: &str) -> Outcome<&'a Object> {
    match value {
        Value::Object(object)
            if object.len() == names.len()
                && names.iter().all(|name| object.contains_key(name)) =>
        {
            Ok(object)
        }
        _ => Err(rejected(message)),
    }
}

/// `sequence(value, cap)`: a list of at most cap items.
fn sequence(value: &Value, cap: usize) -> Outcome<&Vec<Value>> {
    match value {
        Value::Array(items) if items.len() <= cap => Ok(items),
        _ => Err(rejected("bounded list required")),
    }
}

static NULL: Value = Value::Null;

fn field<'a>(object: &'a Object, name: &str) -> &'a Value {
    // Only called after `fields` has checked the key set.
    object.get(name).unwrap_or(&NULL)
}

/// LOWER: `[a-z][a-z0-9_]*`, the whole string.
fn lower_spelling(value: &Value) -> Option<&str> {
    let Value::String(text) = value else {
        return None;
    };
    let mut bytes = text.bytes();
    let first = bytes.next().is_some_and(|byte| byte.is_ascii_lowercase());
    (first && bytes.all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_'))
        .then_some(text)
}

/// VARIABLE: `[A-Z][A-Za-z0-9_]*`, the whole string.
fn variable_spelling(value: &Value) -> Option<&str> {
    let Value::String(text) = value else {
        return None;
    };
    let mut bytes = text.bytes();
    let first = bytes.next().is_some_and(|byte| byte.is_ascii_uppercase());
    (first && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')).then_some(text)
}

fn tag_is(value: &Value, tags: &[&str]) -> bool {
    tags.iter().any(|tag| py::is_text(value, tag))
}

fn index(value: u64) -> usize {
    usize::try_from(value).unwrap_or(usize::MAX)
}

/// The variables table of a declaration: distinct VARIABLE spellings.
fn variables(value: &Value) -> Outcome<Vec<String>> {
    let items = sequence(value, 64)?;
    let mut names = Vec::new();
    for item in items {
        match variable_spelling(item) {
            Some(name) => names.push(name.to_owned()),
            None => return Err(rejected("variable spelling")),
        }
    }
    let mut sorted = names.clone();
    sorted.sort();
    sorted.dedup();
    require(
        sorted.len() == names.len(),
        "duplicate variable table entry",
    )?;
    Ok(names)
}

struct Validator<'a> {
    nodes: u64,
    functions: &'a [u64],
    predicates: &'a [u64],
}

impl Validator<'_> {
    fn visit(&mut self, depth: u64) -> Outcome<()> {
        self.nodes += 1;
        require(
            self.nodes <= MAX_NODES && depth <= MAX_DEPTH,
            "structural witness cap",
        )
    }

    fn term(
        &mut self,
        value: &Value,
        functions: &[u64],
        variables: u64,
        depth: u64,
    ) -> Outcome<Term> {
        self.visit(depth)?;
        let items = sequence(value, 3)?;
        require(
            items
                .first()
                .is_some_and(|tag| tag_is(tag, &["var", "fun"])),
            "unsupported term",
        )?;
        if py::is_text(&items[0], "var") {
            require(items.len() == 2, "variable shape")?;
            let variable = natural(&items[1], NATURAL)?;
            require(
                variable < variables,
                "variable outside supplied table/bound",
            )?;
            return Ok(Term::Var(variable));
        }
        require(items.len() == 3, "function shape")?;
        let symbol = natural(&items[1], NATURAL)?;
        let arguments = sequence(&items[2], 256)?;
        let signature = functions.get(index(symbol));
        require(
            signature.is_some_and(|&arity| arguments.len() as u64 == arity),
            "function signature",
        )?;
        let mut terms = Vec::new();
        for argument in arguments {
            terms.push(self.term(argument, functions, variables, depth + 1)?);
        }
        Ok(Term::Fun(symbol, terms))
    }

    #[allow(clippy::too_many_arguments)]
    fn atom(
        &mut self,
        symbol: &Value,
        arguments: &Value,
        functions: &[u64],
        predicates: &[u64],
        variables: u64,
        depth: u64,
    ) -> Outcome<(u64, Vec<Term>)> {
        let symbol = natural(symbol, NATURAL)?;
        require(index(symbol) < predicates.len(), "predicate index")?;
        let arguments = sequence(arguments, 256)?;
        require(
            arguments.len() as u64 == predicates[index(symbol)],
            "predicate arity",
        )?;
        let mut terms = Vec::new();
        for argument in arguments {
            terms.push(self.term(argument, functions, variables, depth + 1)?);
        }
        Ok((symbol, terms))
    }

    fn literal(
        &mut self,
        value: &Value,
        functions: &[u64],
        predicates: &[u64],
        variables: u64,
        depth: u64,
    ) -> Outcome<Literal> {
        let shape = match value {
            Value::Array(items) if items.len() == 3 => match items[0] {
                Value::Bool(positive) => Some((positive, &items[1], &items[2])),
                _ => None,
            },
            _ => None,
        };
        let Some((positive, symbol, arguments)) = shape else {
            return Err(rejected("literal shape"));
        };
        let (predicate, arguments) =
            self.atom(symbol, arguments, functions, predicates, variables, depth)?;
        Ok(Literal {
            positive,
            predicate,
            arguments,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn formula(
        &mut self,
        value: &Value,
        functions: &[u64],
        predicates: &[u64],
        variables: u64,
        depth: u64,
        nnf: bool,
    ) -> Outcome<Formula> {
        self.visit(depth)?;
        let items = sequence(value, 3)?;
        require(!items.is_empty(), "empty formula")?;
        let tag = &items[0];
        if tag_is(tag, &["truth", "falsity"]) {
            require(items.len() == 1, "constant formula shape")?;
            return Ok(if py::is_text(tag, "truth") {
                Formula::Truth
            } else {
                Formula::Falsity
            });
        }
        if tag_is(tag, &["conj", "disj"]) || (py::is_text(tag, "implies") && !nnf) {
            require(items.len() == 3, "binary formula shape")?;
            let left = Box::new(self.formula(
                &items[1],
                functions,
                predicates,
                variables,
                depth + 1,
                nnf,
            )?);
            let right = Box::new(self.formula(
                &items[2],
                functions,
                predicates,
                variables,
                depth + 1,
                nnf,
            )?);
            return Ok(if py::is_text(tag, "conj") {
                Formula::Conj(left, right)
            } else if py::is_text(tag, "disj") {
                Formula::Disj(left, right)
            } else {
                Formula::Implies(left, right)
            });
        }
        if tag_is(tag, &["all", "ex"]) {
            require(items.len() == 3, "binder bound")?;
            let binder = natural(&items[1], NATURAL)?;
            require(binder < variables, "binder bound")?;
            let body = Box::new(self.formula(
                &items[2],
                functions,
                predicates,
                variables,
                depth + 1,
                nnf,
            )?);
            return Ok(if py::is_text(tag, "all") {
                Formula::All(binder, body)
            } else {
                Formula::Ex(binder, body)
            });
        }
        if py::is_text(tag, "not") && !nnf {
            require(items.len() == 2, "negation shape")?;
            let body = self.formula(
                &items[1],
                functions,
                predicates,
                variables,
                depth + 1,
                false,
            )?;
            return Ok(Formula::Not(Box::new(body)));
        }
        if py::is_text(tag, "atom") && !nnf {
            require(items.len() == 3, "atom shape")?;
            let (symbol, terms) = self.atom(
                &items[1], &items[2], functions, predicates, variables, depth,
            )?;
            return Ok(Formula::Atom(symbol, terms));
        }
        if py::is_text(tag, "literal") && nnf {
            require(items.len() == 2, "literal formula shape")?;
            return Ok(Formula::Literal(
                self.literal(&items[1], functions, predicates, variables, depth)?,
            ));
        }
        Err(rejected(format!(
            "unsupported formula constructor: {}",
            py::text(tag)
        )))
    }

    /// A formula over the original tables.
    fn original_formula(&mut self, value: &Value, variables: u64, nnf: bool) -> Outcome<Formula> {
        let (functions, predicates) = (self.functions, self.predicates);
        self.formula(value, functions, predicates, variables, 0, nnf)
    }
}

/// Statistics: a list of `length` naturals of at most `cap`.
fn statistics(
    value: &Value,
    cap_items: usize,
    length: usize,
    cap: u64,
    message: &str,
) -> Outcome<Vec<u64>> {
    let items = sequence(value, cap_items)?;
    require(items.len() == length, message)?;
    items.iter().map(|item| natural(item, cap)).collect()
}

/// `validate(json.dumps(witness).encode(), source, certificate)`.
pub(crate) fn validate(witness: &Value, source: &[u8], certificate: &[u8]) -> Outcome<Witness> {
    require(
        json_dumps(witness)?.len() <= MAX_WITNESS,
        "witness byte cap",
    )?;
    require(
        source.len() <= MAX_SOURCE && certificate.len() <= MAX_CERTIFICATE,
        "sealed pair byte cap",
    )?;
    require(
        source.is_ascii() && certificate.is_ascii(),
        "ASCII pair required",
    )?;
    let names = [
        "schema",
        "source_hex",
        "certificate_hex",
        "functions",
        "predicates",
        "source_declarations",
        "declarations",
        "standalone",
        "skolem",
        "blocks",
    ];
    let object = fields(witness, &names, "unexpected witness fields")?;
    require(
        py::is_text(field(object, "schema"), SCHEMA),
        "unknown witness schema",
    )?;
    require(
        py::is_text(field(object, "source_hex"), &hex(source)),
        "source byte binding",
    )?;
    require(
        py::is_text(field(object, "certificate_hex"), &hex(certificate)),
        "certificate byte binding",
    )?;
    let mut tables: Vec<Vec<Symbol>> = Vec::new();
    for key in ["functions", "predicates"] {
        let mut symbols: Vec<Symbol> = Vec::new();
        for symbol in sequence(field(object, key), 256)? {
            let pair = match symbol {
                Value::Array(items) if items.len() == 2 => Some((&items[0], &items[1])),
                _ => None,
            };
            let Some((name, arity)) = pair else {
                return Err(rejected("symbol shape"));
            };
            let Some(name) = lower_spelling(name) else {
                return Err(rejected("symbol spelling"));
            };
            symbols.push(Symbol {
                name: name.to_owned(),
                arity: natural(arity, 256)?,
            });
        }
        let mut spellings: Vec<&str> = symbols.iter().map(|symbol| symbol.name.as_str()).collect();
        spellings.sort_unstable();
        spellings.dedup();
        require(
            spellings.len() == symbols.len(),
            "duplicate symbol spelling",
        )?;
        tables.push(symbols);
    }
    let predicates_table = tables.pop().unwrap_or_default();
    let functions_table = tables.pop().unwrap_or_default();
    let original_functions: Vec<u64> = functions_table.iter().map(|symbol| symbol.arity).collect();
    let original_predicates: Vec<u64> =
        predicates_table.iter().map(|symbol| symbol.arity).collect();
    let mut validator = Validator {
        nodes: 0,
        functions: &original_functions,
        predicates: &original_predicates,
    };

    let source_items = sequence(field(object, "source_declarations"), 16)?;
    require(!source_items.is_empty(), "empty candidate")?;
    let mut source_declarations = Vec::new();
    let mut projection: Vec<Object> = Vec::new();
    for declaration in source_items {
        let entry = fields(
            declaration,
            &["name", "variables", "body"],
            "unexpected witness fields",
        )?;
        let Some(name) = lower_spelling(field(entry, "name")) else {
            return Err(rejected("declaration spelling"));
        };
        let variable_names = variables(field(entry, "variables"))?;
        let body = sequence(field(entry, "body"), 2)?;
        require(
            body.len() == 2 && tag_is(&body[0], &["cnf", "fof"]),
            "declaration body shape",
        )?;
        let count = variable_names.len() as u64;
        let typed = if py::is_text(&body[0], "cnf") {
            let mut literals = Vec::new();
            for value in sequence(&body[1], 256)? {
                literals.push(validator.literal(
                    value,
                    &original_functions,
                    &original_predicates,
                    count,
                    0,
                )?);
            }
            Body::Cnf(literals)
        } else {
            let formula = validator.original_formula(&body[1], count, false)?;
            let mut item = Object::new();
            item.set("name", name);
            item.set("variables", field(entry, "variables").clone());
            item.set("formula", body[1].clone());
            projection.push(item);
            Body::Fof(formula)
        };
        source_declarations.push(SourceDeclaration {
            name: name.to_owned(),
            variables: variable_names,
            body: typed,
        });
    }
    let mut declaration_names: Vec<&str> = source_declarations
        .iter()
        .map(|item| item.name.as_str())
        .collect();
    declaration_names.sort_unstable();
    declaration_names.dedup();
    require(
        declaration_names.len() == source_declarations.len(),
        "duplicate declaration name",
    )?;

    let declaration_items = sequence(field(object, "declarations"), 16)?;
    let projected = declaration_items.len() == projection.len()
        && declaration_items
            .iter()
            .zip(&projection)
            .all(|(item, expected)| py::equals(item, &Value::Object(expected.clone())));
    require(
        projected,
        "FOF projection differs from ordered source declarations",
    )?;
    let standalone_items = sequence(field(object, "standalone"), 16)?;
    let block_items = sequence(field(object, "blocks"), 16)?;
    require(
        declaration_items.len() == standalone_items.len()
            && standalone_items.len() == block_items.len(),
        "declaration/block counts",
    )?;
    let mut bounds: Vec<u64> = Vec::new();
    let mut declarations = Vec::new();
    let mut standalone = Vec::new();
    for (declaration, observed) in declaration_items.iter().zip(standalone_items) {
        let entry = fields(
            declaration,
            &["name", "variables", "formula"],
            "unexpected witness fields",
        )?;
        let Some(name) = lower_spelling(field(entry, "name")) else {
            return Err(rejected("declaration spelling"));
        };
        let variable_names = variables(field(entry, "variables"))?;
        let formula = validator.original_formula(
            field(entry, "formula"),
            variable_names.len() as u64,
            false,
        )?;
        let keys = [
            "validated",
            "rectified",
            "binder_count",
            "rectified_stats",
            "normalized",
            "normalized_stats",
        ];
        let observation = fields(observed, &keys, "unexpected witness fields")?;
        let bound = natural(field(observation, "binder_count"), 64)?;
        bounds.push(bound);
        let mut stats = Vec::new();
        for key in ["validated", "rectified_stats", "normalized_stats"] {
            stats.push(statistics(
                field(observation, key),
                8,
                8,
                5_000_000,
                "core statistics shape",
            )?);
        }
        let rectified =
            validator.original_formula(field(observation, "rectified"), bound, false)?;
        let normalized =
            validator.original_formula(field(observation, "normalized"), bound, true)?;
        let normalized_stats = stats.pop().unwrap_or_default();
        let rectified_stats = stats.pop().unwrap_or_default();
        let validated = stats.pop().unwrap_or_default();
        declarations.push(Declaration {
            name: name.to_owned(),
            variables: variable_names,
            formula,
        });
        standalone.push(Standalone {
            validated,
            rectified,
            binder_count: bound,
            rectified_stats,
            normalized,
            normalized_stats,
        });
    }

    let skolem_object = fields(
        field(object, "skolem"),
        &[
            "formulas",
            "functions",
            "predicates",
            "introduced",
            "statistics",
        ],
        "unexpected witness fields",
    )?;
    let predicates_value = Value::Array(
        original_predicates
            .iter()
            .map(|&arity| super::witness::natural_value(arity))
            .collect(),
    );
    require(
        py::equals(field(skolem_object, "predicates"), &predicates_value),
        "changed predicate table",
    )?;
    let skolem_predicates = match field(skolem_object, "predicates") {
        Value::Array(items) => items.clone(),
        _ => Vec::new(),
    };
    let function_items = sequence(field(skolem_object, "functions"), 320)?;
    let mut functions = Vec::new();
    for (position, arity) in function_items.iter().enumerate() {
        functions.push(natural(
            arity,
            if position < original_functions.len() {
                256
            } else {
                64
            },
        )?);
    }
    require(
        functions.len() >= original_functions.len()
            && functions[..original_functions.len()] == original_functions[..],
        "original function prefix",
    )?;
    let formula_items = sequence(field(skolem_object, "formulas"), 16)?;
    require(
        formula_items.len() == declarations.len(),
        "Skolem output count",
    )?;
    let mut skolem_formulas = Vec::new();
    for (value, &bound) in formula_items.iter().zip(&bounds) {
        skolem_formulas.push(validator.formula(
            value,
            &functions,
            &original_predicates,
            bound,
            0,
            true,
        )?);
    }
    let mut introduced = Vec::new();
    for origin in sequence(field(skolem_object, "introduced"), 64)? {
        let parts = match origin {
            Value::Array(items) if items.len() == 4 => Some(items),
            _ => None,
        };
        let Some(parts) = parts else {
            return Err(rejected("origin shape"));
        };
        let declaration = natural(&parts[0], NATURAL)?;
        require(index(declaration) < bounds.len(), "origin location")?;
        let binder = natural(&parts[1], NATURAL)?;
        let bound = bounds[index(declaration)];
        require(binder < bound, "origin location")?;
        let function = natural(&parts[2], NATURAL)?;
        require(
            original_functions.len() <= index(function) && index(function) < functions.len(),
            "fresh function index",
        )?;
        let universal_items = sequence(&parts[3], 64)?;
        require(
            universal_items.len() as u64 == functions[index(function)],
            "Skolem arity/dependency count",
        )?;
        let mut universals = Vec::new();
        for value in universal_items {
            let universal = natural(value, NATURAL)?;
            require(universal < bound, "dependency bound")?;
            universals.push(universal);
        }
        introduced.push(Origin {
            declaration,
            binder,
            function,
            universals,
        });
    }
    let skolem_statistics = statistics(
        field(skolem_object, "statistics"),
        2,
        2,
        5_000_000,
        "Skolem statistics",
    )?;

    let mut blocks = Vec::new();
    for (block, &bound) in block_items.iter().zip(&bounds) {
        let entry = fields(
            block,
            &["removal_stats", "clauses", "clausifier_stats"],
            "unexpected witness fields",
        )?;
        let removal = sequence(field(entry, "removal_stats"), 2)?;
        require(removal.len() == 2, "removal statistics")?;
        let clausifier = sequence(field(entry, "clausifier_stats"), 7)?;
        require(clausifier.len() == 7, "clausifier statistics")?;
        let mut removal_stats = Vec::new();
        for value in removal {
            removal_stats.push(natural(value, 5_000_000)?);
        }
        let mut clausifier_stats = Vec::new();
        for value in clausifier {
            clausifier_stats.push(natural(value, 5_000_000)?);
        }
        let mut clauses = Vec::new();
        for clause in sequence(field(entry, "clauses"), 1000)? {
            let mut literals = Vec::new();
            for value in sequence(clause, 256)? {
                literals.push(validator.literal(
                    value,
                    &functions,
                    &original_predicates,
                    bound,
                    0,
                )?);
            }
            clauses.push(literals);
        }
        blocks.push(Block {
            removal_stats,
            clauses,
            clausifier_stats,
        });
    }
    Ok(Witness {
        functions: functions_table,
        predicates: predicates_table,
        source_declarations,
        declarations,
        standalone,
        skolem: Skolem {
            formulas: skolem_formulas,
            functions,
            predicates: skolem_predicates,
            introduced,
            statistics: skolem_statistics,
        },
        blocks,
    })
}

/// `bytes.hex()`.
pub(crate) fn hex(data: &[u8]) -> String {
    let mut text = String::with_capacity(data.len() * 2);
    for byte in data {
        text.push_str(&format!("{byte:02x}"));
    }
    text
}
