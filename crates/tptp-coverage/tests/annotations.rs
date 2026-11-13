// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Annotations are parsed and retained and never change formula meaning.

use fang::ErrorKind;
use fang_tptp_coverage_candidate::{
    Bundle, Expanded, GeneralTerm, Limits, NameKind, Reason, Source, SourceClass, expand,
};

fn run(text: &str) -> Expanded {
    expand(
        &Bundle::single(text.as_bytes().to_vec()),
        &Limits::default(),
    )
    .unwrap()
}

fn annotation(value: &Expanded) -> &fang_tptp_coverage_candidate::Annotation {
    let Source::File {
        annotation: Some(annotation),
        ..
    } = &value.sources[0]
    else {
        panic!("no annotation");
    };
    annotation
}

const FORMS: [&str; 16] = [
    "file('x.p')",
    "file('x.p',name)",
    "file(x,7)",
    "inference(resolution,[status(thm)],[a,b])",
    "introduced(definition,[],[])",
    "source_name",
    "42",
    "[file(a),inference(r,[],[c:bind(X,$fof(p(X)))])]",
    "foo:bar:baz",
    "f(X,-3,1/2,-1.5e+3,0.25,7E2,\"obj\",'q w')",
    "unknown,[]",
    "file(x),[description('d'),iquote(\"i\"),[1,[2]]]",
    "a,[$cnf(p | ~q),$fot(f(X)),$tff(p),$thf((p))]",
    "x,[$fof(! [X] : (p(X) & \"d\" = a))]",
    "[]",
    "f(g(h(i(j))))",
];

#[test]
fn every_supported_form_parses_and_is_retained() {
    let plain = run("fof(a,axiom,![X]:(p(X) => X = b)).");
    for form in FORMS {
        let text = format!("fof(a,axiom,![X]:(p(X) => X = b),{form}).");
        let value = run(&text);
        let retained = annotation(&value);
        assert_eq!(&text.as_bytes()[retained.bytes.clone()], form.as_bytes());
        assert_eq!(value.parsed.functions, plain.parsed.functions, "{form}");
        assert_eq!(value.parsed.predicates, plain.parsed.predicates);
        assert_eq!(
            value.parsed.declarations[0].body,
            plain.parsed.declarations[0].body
        );
        assert_eq!(
            value.parsed.declarations[0].variables,
            plain.parsed.declarations[0].variables
        );
        assert_eq!(
            value.parsed.declarations[0].body_bytes,
            plain.parsed.declarations[0].body_bytes
        );
        assert!(value.distinct_objects.is_empty(), "{form}");
    }
}

#[test]
fn source_classes_and_useful_info() {
    let value = run("cnf(a,axiom,p,file('x.p',n),[status(thm)]).");
    let retained = annotation(&value);
    assert_eq!(
        retained.class,
        SourceClass::File {
            file: "x.p".into(),
            name: Some((NameKind::Atom, "n".into()))
        }
    );
    let (items, bytes) = retained.useful_info.clone().unwrap();
    assert_eq!(bytes, 28..41);
    assert_eq!(
        items,
        [GeneralTerm::Function(
            "status".into(),
            vec![GeneralTerm::Word("thm".into())]
        )]
    );
    for (form, class) in [
        ("inference(r,[],[])", SourceClass::Inference),
        ("introduced(definition,[],[])", SourceClass::Introduced),
        ("7", SourceClass::Name(NameKind::Integer, "7".into())),
        ("[a]", SourceClass::List),
        ("a:b", SourceClass::Other),
        ("inference(r)", SourceClass::Other),
    ] {
        let value = run(&format!("cnf(a,axiom,p,{form})."));
        assert_eq!(annotation(&value).class, class, "{form}");
    }
}

#[test]
fn deleting_annotations_gives_the_same_problem() {
    let annotated = "fof(a,axiom,p(\"x\"),file(f,a),[\"y\",z(\"x\")]). cnf(b,axiom,q(W) | W = \"w\",inference(r,[],[a])). fof(c,axiom,r,\"only_here\").";
    let plain = "fof(a,axiom,p(\"x\")). cnf(b,axiom,q(W) | W = \"w\"). fof(c,axiom,r).";
    let (a, b) = (run(annotated), run(plain));
    assert_eq!(a.parsed.functions, b.parsed.functions);
    assert_eq!(a.parsed.predicates, b.parsed.predicates);
    assert_eq!(a.distinct_objects, b.distinct_objects);
    assert_eq!(a.distinct_objects.len(), 2);
    for (left, right) in a.parsed.declarations.iter().zip(&b.parsed.declarations) {
        assert_eq!(left.body, right.body);
        assert_eq!(left.variables, right.variables);
        assert_eq!(left.name, right.name);
    }
    assert_eq!(a.parsed.declarations.len(), b.parsed.declarations.len());
}

#[test]
fn malformed_annotations_are_input_errors() {
    for form in [
        "", "a,b,c", "a,b", "f()", "[a,]", "f(]", "a:", "$foo", "$$sys", "$fof(p", "$fof(p]",
        "$fof", "(a)", "a,[b],", "\"\"", "\"open", "[a", "`X", "1.",
    ] {
        let text = format!("fof(a,axiom,p,{form}).");
        let error = expand(&Bundle::single(text.into_bytes()), &Limits::default()).unwrap_err();
        assert_eq!(error.kind, ErrorKind::InvalidInput, "{form}: {error:?}");
    }
}

#[test]
fn annotation_depth_and_node_caps_are_resource_errors() {
    let deep = format!("fof(a,axiom,p,{}a{}).", "[".repeat(70), "]".repeat(70));
    let error = expand(&Bundle::single(deep.into_bytes()), &Limits::default()).unwrap_err();
    assert_eq!(
        (error.kind, error.reason),
        (ErrorKind::ResourceLimit, Reason::Limit)
    );
    let wide = format!("fof(a,axiom,p,[{}]).", vec!["a"; 50].join(","));
    let limits = Limits {
        max_annotation_nodes: 40,
        ..Limits::default()
    };
    assert_eq!(
        expand(&Bundle::single(wide.clone().into_bytes()), &limits)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    assert!(expand(&Bundle::single(wide.into_bytes()), &Limits::default()).is_ok());
    let deep_data = format!(
        "fof(a,axiom,p,$fof({}p{})).",
        "(".repeat(70),
        ")".repeat(70)
    );
    assert_eq!(
        expand(&Bundle::single(deep_data.into_bytes()), &Limits::default())
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn inference_records_in_input_are_metadata_only() {
    let value = run("cnf(c,axiom,$false,inference(refutation,[status(thm)],[a,b])).");
    assert_eq!(value.parsed.declarations.len(), 1);
    assert_eq!(annotation(&value).class, SourceClass::Inference);
    let value = run("cnf(c,axiom,p,inference(refutation,[status(thm)],[$cnf($false)])).");
    assert!(value.parsed.functions.is_empty());
    assert_eq!(value.parsed.predicates.len(), 1);
}
