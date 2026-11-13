// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Include capture and expansion over real directory trees.

use fang::ErrorKind;
use fang_tptp_coverage_candidate::{
    Bundle, Expanded, Key, Limits, NameKind, Reason, Root, Source, capture, expand,
};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A fresh tree with `base/` and `tptp/`, removed on drop.
struct Tree(PathBuf);

impl Tree {
    fn new(files: &[(&str, &str)]) -> Self {
        let root = std::env::temp_dir().join(format!(
            "fang-coverage-includes-{}-{}",
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        for (path, text) in files {
            let target = root.join(path);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, text).unwrap();
        }
        std::fs::create_dir_all(root.join("base")).unwrap();
        std::fs::create_dir_all(root.join("tptp")).unwrap();
        Tree(root)
    }
    fn run(&self, limits: &Limits) -> Result<Expanded, fang_tptp_coverage_candidate::Error> {
        capture(
            &self.0.join("base/top.p"),
            Some(&self.0.join("tptp")),
            limits,
        )
    }
    fn ok(&self) -> Expanded {
        self.run(&Limits::default()).unwrap()
    }
    fn reason(&self) -> (ErrorKind, Reason) {
        let error = self.run(&Limits::default()).unwrap_err();
        (error.kind, error.reason)
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn names(value: &Expanded) -> Vec<String> {
    value
        .parsed
        .declarations
        .iter()
        .map(|d| d.name.clone())
        .collect()
}

fn origin(value: &Expanded, index: usize) -> (Key, &[u8]) {
    let Source::File { file, .. } = &value.sources[index] else {
        panic!("generated source");
    };
    let bundle_file = &value.bundle.files[*file];
    let bytes = &bundle_file.bytes[value.parsed.declarations[index].bytes.clone()];
    (bundle_file.key.clone(), bytes)
}

const AX: &str = "fof(x,axiom,p). fof(y,axiom,~p). fof(z,axiom,q(a)).";

#[test]
fn include_is_replaced_in_place_with_source_identity() {
    let tree = Tree::new(&[
        (
            "base/top.p",
            "fof(t,axiom,r(b)). include('ax.ax'). fof(u,axiom,s).",
        ),
        ("base/ax.ax", AX),
    ]);
    let value = tree.ok();
    assert_eq!(names(&value), ["t", "x", "y", "z", "u"]);
    let (key, bytes) = origin(&value, 2);
    assert_eq!(
        key,
        Key {
            root: Root::Base,
            path: vec!["ax.ax".into()]
        }
    );
    assert_eq!(bytes, b"fof(y,axiom,~p).");
    // Function and predicate IDs follow first occurrence in expanded order.
    let predicates: Vec<_> = value
        .parsed
        .predicates
        .iter()
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(predicates, ["r", "p", "q", "s"]);
    let functions: Vec<_> = value
        .parsed
        .functions
        .iter()
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(functions, ["b", "a"]);
    assert_eq!(value.bundle.files.len(), 2);
    let again = expand(&value.bundle, &Limits::default()).unwrap();
    assert_eq!(
        format!("{:?}", again.parsed.declarations),
        format!("{:?}", value.parsed.declarations)
    );
    assert_eq!(again.sources, value.sources);
}

#[test]
fn selections_follow_the_problem_library_rule() {
    let cases = [
        ("include('ax.ax',[y,x]).", Some(vec!["x", "y"])),
        ("include('ax.ax',['x']).", Some(vec!["x"])),
        ("include('ax.ax',[x,x]).", Some(vec!["x"])),
        ("include('ax.ax',*).", Some(vec!["x", "y", "z"])),
        ("include(ax_ax).", None),
    ];
    for (top, expected) in cases {
        let tree = Tree::new(&[
            ("base/top.p", top),
            ("base/ax.ax", AX),
            ("base/ax_ax", "fof(w,axiom,p)."),
        ]);
        match expected {
            Some(expected) => assert_eq!(names(&tree.ok()), expected, "{top}"),
            None => assert_eq!(names(&tree.ok()), ["w"]),
        }
    }
    let missing = Tree::new(&[
        ("base/top.p", "include('ax.ax',[x,nope])."),
        ("base/ax.ax", AX),
    ]);
    assert_eq!(
        missing.reason(),
        (ErrorKind::InvalidInput, Reason::SelectionMissing)
    );
    let integer = Tree::new(&[
        ("base/top.p", "include('i.ax',[1])."),
        ("base/i.ax", "fof(1,axiom,p). fof('1',axiom,q)."),
    ]);
    let value = integer.ok();
    assert_eq!(value.parsed.declarations.len(), 1);
    assert_eq!(value.parsed.declarations[0].name_kind, NameKind::Integer);
    for top in [
        "include('ax.ax',[]).",
        "include('ax.ax',all).",
        "include('ax.ax',[x]",
        "include('ax.ax'),[x]).",
        "include(\"ax.ax\").",
        "include('ax.ax',[1.5]).",
    ] {
        let tree = Tree::new(&[("base/top.p", top), ("base/ax.ax", AX)]);
        assert_eq!(tree.reason().0, ErrorKind::InvalidInput, "{top}");
    }
    let namespace = Tree::new(&[
        ("base/top.p", "include('ax.ax',*,space)."),
        ("base/ax.ax", AX),
    ]);
    assert_eq!(
        namespace.reason(),
        (ErrorKind::Unsupported, Reason::Namespace)
    );
}

#[test]
fn selections_filter_nested_includes_and_detect_ambiguity() {
    let nested = Tree::new(&[
        ("base/top.p", "include('n.ax',[n,y])."),
        ("base/n.ax", "include('ax.ax'). fof(n,axiom,r)."),
        ("base/ax.ax", AX),
    ]);
    assert_eq!(names(&nested.ok()), ["y", "n"]);
    let ambiguous = Tree::new(&[
        ("base/top.p", "include('n.ax',[x])."),
        ("base/n.ax", "include('ax.ax'). fof(x,axiom,r)."),
        ("base/ax.ax", AX),
    ]);
    assert_eq!(
        ambiguous.reason(),
        (ErrorKind::InvalidInput, Reason::SelectionAmbiguous)
    );
    // An unselected name repeated across files is allowed.
    let repeated = Tree::new(&[
        ("base/top.p", "include('n.ax',[n])."),
        (
            "base/n.ax",
            "include('ax.ax'). fof(n,axiom,r). fof(z,axiom,r).",
        ),
        ("base/ax.ax", AX),
    ]);
    assert_eq!(names(&repeated.ok()), ["n"]);
    let across = Tree::new(&[
        ("base/top.p", "fof(x,axiom,q). include('ax.ax',[y])."),
        ("base/ax.ax", AX),
    ]);
    assert_eq!(names(&across.ok()), ["x", "y"]);
    let same_file = Tree::new(&[("base/top.p", "fof(x,axiom,q). fof(x,axiom,~q).")]);
    assert_eq!(same_file.reason().0, ErrorKind::InvalidInput);
}

#[test]
fn unselected_formulas_are_checked_but_leave_no_symbols() {
    let tree = Tree::new(&[
        ("base/top.p", "include('ax.ax',[x])."),
        ("base/ax.ax", "fof(x,axiom,p). fof(y,axiom,hidden(c))."),
    ]);
    let value = tree.ok();
    assert_eq!(value.parsed.predicates.len(), 1);
    assert!(value.parsed.functions.is_empty());
    for bad in [
        "fof(x,axiom,p). fof(y,axiom,(q).",
        "fof(x,axiom,p). fof(y,axiom,$less(1,2)).",
        "fof(x,axiom,p). fof(y,conjecture,q).",
    ] {
        let tree = Tree::new(&[("base/top.p", "include('ax.ax',[x])."), ("base/ax.ax", bad)]);
        let error = tree.run(&Limits::default()).unwrap_err();
        assert_eq!(error.file, Some(1), "{bad}");
    }
}

#[test]
fn resolution_prefers_the_including_directory_then_the_tptp_root() {
    let tree = Tree::new(&[
        ("base/top.p", "include('Axioms/a.ax'). include('sub/s.ax')."),
        ("tptp/Axioms/a.ax", "fof(from_tptp,axiom,p)."),
        ("base/sub/s.ax", "include('t.ax'). include('Axioms/a.ax')."),
        ("base/sub/t.ax", "fof(from_sub,axiom,q)."),
        ("base/sub/Axioms/a.ax", "fof(shadow,axiom,r)."),
    ]);
    let value = tree.ok();
    assert_eq!(names(&value), ["from_tptp", "from_sub", "shadow"]);
    let keys: Vec<_> = value.bundle.files.iter().map(|f| f.key.clone()).collect();
    assert_eq!(keys[1].root, Root::Tptp);
    assert_eq!(keys[4].path, ["sub", "Axioms", "a.ax"]);
    // Without a TPTP root the first include is missing.
    let error = capture(&tree.0.join("base/top.p"), None, &Limits::default()).unwrap_err();
    assert_eq!(error.reason, Reason::Missing);
    // A nested TPTP file resolves its own includes relative to its directory.
    let nested = Tree::new(&[
        ("base/top.p", "include('Axioms/a.ax')."),
        ("tptp/Axioms/a.ax", "include('Axioms/b.ax')."),
        ("tptp/Axioms/b.ax", "fof(b,axiom,p)."),
    ]);
    assert_eq!(names(&nested.ok()), ["b"]);
}

#[test]
fn path_policy_rejects_escapes_and_odd_components() {
    for path in [
        "/etc/passwd",
        "../other.ax",
        "sub/../ax.ax",
        "./ax.ax",
        "sub//ax.ax",
        "sub\\\\ax.ax",
        "C:ax.ax",
        "ax.ax/",
    ] {
        let tree = Tree::new(&[
            ("base/top.p", &format!("include('{path}').")),
            ("base/ax.ax", AX),
            ("other.ax", AX),
        ]);
        assert_eq!(
            tree.reason(),
            (ErrorKind::InvalidInput, Reason::PathSyntax),
            "{path}"
        );
    }
    let long = "a/".repeat(64) + "b";
    let tree = Tree::new(&[("base/top.p", &format!("include('{long}')."))]);
    assert_eq!(tree.reason().1, Reason::PathSyntax);
    let back = Tree::new(&[("base/top.p", "include(`X).")]);
    assert_eq!(back.reason(), (ErrorKind::Unsupported, Reason::BackQuoted));
    let directory = Tree::new(&[("base/top.p", "include('sub')."), ("base/sub/x", "")]);
    assert_eq!(
        directory.reason(),
        (ErrorKind::InvalidInput, Reason::NotRegular)
    );
}

#[cfg(unix)]
#[test]
fn symbolic_links_are_rejected_anywhere_below_the_root() {
    let tree = Tree::new(&[("base/top.p", "include('link.ax')."), ("real/ax.ax", AX)]);
    std::os::unix::fs::symlink(tree.0.join("real/ax.ax"), tree.0.join("base/link.ax")).unwrap();
    assert_eq!(tree.reason(), (ErrorKind::InvalidInput, Reason::Symlink));
    let directory_link = Tree::new(&[("base/top.p", "include('d/ax.ax')."), ("real/ax.ax", AX)]);
    std::os::unix::fs::symlink(
        directory_link.0.join("real"),
        directory_link.0.join("base/d"),
    )
    .unwrap();
    assert_eq!(directory_link.reason().1, Reason::Symlink);
    let top = Tree::new(&[("real/top.p", "fof(a,axiom,p).")]);
    std::os::unix::fs::symlink(top.0.join("real/top.p"), top.0.join("base/top.p")).unwrap();
    assert_eq!(top.reason().1, Reason::Symlink);
}

#[test]
fn cycles_are_typed_errors() {
    let selfie = Tree::new(&[("base/top.p", "include('top.p').")]);
    assert_eq!(selfie.reason(), (ErrorKind::InvalidInput, Reason::Cycle));
    let three = Tree::new(&[
        ("base/top.p", "include('a.ax')."),
        ("base/a.ax", "include('b.ax'). fof(a,axiom,p)."),
        ("base/b.ax", "fof(b,axiom,p). include('a.ax')."),
    ]);
    let error = three.run(&Limits::default()).unwrap_err();
    assert_eq!((error.reason, error.file), (Reason::Cycle, Some(2)));
}

#[test]
fn repeats_expand_again_and_keep_one_copy_per_source_identity() {
    let tree = Tree::new(&[
        (
            "base/top.p",
            "include('ax.ax',[x]). include('ax.ax',[y]). include('ax.ax'). include('d.ax').",
        ),
        ("base/ax.ax", AX),
        ("base/d.ax", "include('ax.ax',[z]). fof(d,axiom,p)."),
    ]);
    let value = tree.ok();
    assert_eq!(names(&value), ["x", "y", "z", "d"]);
    assert_eq!(value.bundle.files.len(), 3);
}

#[test]
fn depth_file_directive_and_byte_caps_are_resource_errors() {
    let mut files = vec![("base/top.p".to_owned(), "include('f1.ax').".to_owned())];
    for level in 1..=17 {
        files.push((
            format!("base/f{level}.ax"),
            if level == 17 {
                "fof(deep,axiom,p).".to_owned()
            } else {
                format!("include('f{}.ax').", level + 1)
            },
        ));
    }
    let borrowed: Vec<(&str, &str)> = files
        .iter()
        .map(|(a, b)| (a.as_str(), b.as_str()))
        .collect();
    let tree = Tree::new(&borrowed);
    assert_eq!(tree.reason(), (ErrorKind::ResourceLimit, Reason::Limit));
    let limits = Limits {
        max_include_depth: 17,
        ..Limits::default()
    };
    assert_eq!(names(&tree.run(&limits).unwrap()), ["deep"]);
    let limits = Limits {
        max_include_depth: 17,
        max_files: 17,
        ..Limits::default()
    };
    assert_eq!(
        tree.run(&limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    // Diamonds re-expand; the directive cap bounds the work.
    let mut diamond = vec![("base/top.p".to_owned(), String::new())];
    for level in 0..12 {
        diamond.push((
            format!("base/d{level}.ax"),
            format!("include('d{0}.ax'). include('d{0}.ax').", level + 1),
        ));
    }
    diamond[0].1 = "include('d0.ax').".into();
    diamond.push(("base/d12.ax".into(), "fof(leaf,axiom,p).".into()));
    let borrowed: Vec<(&str, &str)> = diamond
        .iter()
        .map(|(a, b)| (a.as_str(), b.as_str()))
        .collect();
    let tree = Tree::new(&borrowed);
    assert_eq!(tree.reason().0, ErrorKind::ResourceLimit);
    let limits = Limits {
        max_include_directives: 1 << 14,
        ..Limits::default()
    };
    assert_eq!(names(&tree.run(&limits).unwrap()), ["leaf"]);
    let big = Tree::new(&[
        ("base/top.p", "include('a.ax')."),
        ("base/a.ax", "fof(a,axiom,p). % padding"),
    ]);
    let limits = Limits {
        max_bundle_bytes: 30,
        ..Limits::default()
    };
    assert_eq!(big.run(&limits).unwrap_err().kind, ErrorKind::ResourceLimit);
}

#[test]
fn sealed_bundles_must_have_the_reached_shape() {
    let tree = Tree::new(&[
        ("base/top.p", "include('a.ax'). include('b.ax')."),
        ("base/a.ax", "fof(a,axiom,p)."),
        ("base/b.ax", "fof(b,axiom,q)."),
    ]);
    let value = tree.ok();
    let digest = value.bundle.digest();
    let mut swapped = value.bundle.clone();
    swapped.files.swap(1, 2);
    assert_ne!(swapped.digest(), digest);
    assert_eq!(
        expand(&swapped, &Limits::default()).unwrap_err().reason,
        Reason::BundleShape
    );
    let mut extra = value.bundle.clone();
    extra.files.push(fang_tptp_coverage_candidate::BundleFile {
        key: Key {
            root: Root::Base,
            path: vec!["unused.ax".into()],
        },
        bytes: b"fof(u,axiom,p).".to_vec(),
    });
    assert_eq!(
        expand(&extra, &Limits::default()).unwrap_err().reason,
        Reason::BundleShape
    );
    let mut duplicate = value.bundle.clone();
    duplicate.files[2].key = duplicate.files[1].key.clone();
    assert_eq!(
        expand(&duplicate, &Limits::default()).unwrap_err().reason,
        Reason::BundleShape
    );
    let mut changed = value.bundle.clone();
    changed.files[1].bytes = b"fof(a,axiom,~q).".to_vec();
    assert_ne!(changed.digest(), digest);
    let refuted = expand(&changed, &Limits::default()).unwrap();
    assert_eq!(names(&refuted), ["a", "b"]);
    assert_eq!(Bundle::single(Vec::new()).files.len(), 1);
}

#[test]
fn in_memory_parse_has_no_filesystem() {
    let error = fang_tptp_coverage_candidate::parse(
        format!("include('{}').", Path::new("/etc/hostname").display()).as_bytes(),
        &Limits::default(),
    )
    .unwrap_err();
    assert_eq!(error.reason, Reason::PathSyntax);
    let error =
        fang_tptp_coverage_candidate::parse(b"include('input').", &Limits::default()).unwrap_err();
    assert_eq!(error.reason, Reason::Cycle);
    let error =
        fang_tptp_coverage_candidate::parse(b"include('x.ax').", &Limits::default()).unwrap_err();
    assert_eq!(error.reason, Reason::Missing);
}
