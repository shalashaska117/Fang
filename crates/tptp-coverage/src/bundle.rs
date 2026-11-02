// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Include resolution over a sealed bundle of files. Only `capture` reads the
//! filesystem; `expand` is a function of the bundle bytes and the limits.

use crate::{
    Annotation, Body, CnfLiteral, Declaration, Error, Limits, NameKind, Parsed, Parser, Reason,
    Statement, Statistics, Token, lex, sha256,
};
use fang::ErrorKind;
use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Literal};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::ops::Range;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Root {
    /// Directory of the top-level file.
    Base,
    /// The explicit TPTP root.
    Tptp,
}

/// File identity: a root and normalized relative path components.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key {
    pub root: Root,
    pub path: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundleFile {
    pub key: Key,
    pub bytes: Vec<u8>,
}

/// Files in first-reach order; file 0 is the top-level file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bundle {
    pub files: Vec<BundleFile>,
}

impl Bundle {
    /// One in-memory top-level file named `input`.
    pub fn single(bytes: Vec<u8>) -> Self {
        Self {
            files: vec![BundleFile {
                key: Key {
                    root: Root::Base,
                    path: vec!["input".into()],
                },
                bytes,
            }],
        }
    }

    /// SHA-256 over a length-prefixed serialization of every key and file.
    pub fn digest(&self) -> [u8; 32] {
        let mut data = b"fang-tptp-bundle-v1\0".to_vec();
        let length = |data: &mut Vec<u8>, value: usize| {
            data.extend_from_slice(&(value as u64).to_be_bytes());
        };
        length(&mut data, self.files.len());
        for file in &self.files {
            data.push(match file.key.root {
                Root::Base => 0,
                Root::Tptp => 1,
            });
            length(&mut data, file.key.path.len());
            for component in &file.key.path {
                length(&mut data, component.len());
                data.extend_from_slice(component.as_bytes());
            }
            length(&mut data, file.bytes.len());
            data.extend_from_slice(&file.bytes);
        }
        sha256(&data)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Selection {
    /// No selection argument.
    Absent,
    /// `*`.
    Star,
    /// Formula names; repeated names count once.
    Names(Vec<(NameKind, String)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Include {
    /// Decoded `<file_name>`.
    pub path: String,
    pub path_offset: usize,
    pub selection: Selection,
    pub bytes: Range<usize>,
}

/// Where an expanded declaration came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    File {
        /// Index into `Bundle::files`.
        file: usize,
        /// Index of the statement in that file, include directives included.
        statement: usize,
        annotation: Option<Annotation>,
    },
    /// Generated `objects[left] != objects[right]`, with `left < right`.
    DistinctPair { left: usize, right: usize },
}

#[derive(Debug)]
pub struct Expanded {
    pub bundle: Bundle,
    /// Selected declarations in expanded order, then the generated axioms.
    pub parsed: Parsed,
    /// Parallel to `parsed.declarations`.
    pub sources: Vec<Source>,
    /// Distinct-object function IDs and contents in first-occurrence order.
    pub distinct_objects: Vec<(u32, String)>,
}

struct Framed {
    tokens: Vec<Token>,
    statements: Vec<(Range<usize>, Statement)>,
}

fn fail(kind: ErrorKind, reason: Reason, file: usize, offset: usize, message: &str) -> Error {
    Error::typed(kind, reason, offset, message).in_file(file)
}

/// Split and check an include path. Rejects absolute paths, `.` and `..`,
/// empty components, backslashes, colons and NUL.
fn components(path: &str, file: usize, offset: usize) -> Result<Vec<String>, Error> {
    let bad = |message| {
        fail(
            ErrorKind::InvalidInput,
            Reason::PathSyntax,
            file,
            offset,
            message,
        )
    };
    if path.is_empty() || path.len() > 4_096 {
        return Err(bad("include path must have 1 to 4096 bytes"));
    }
    if path.starts_with('/') {
        return Err(bad("absolute include paths are rejected"));
    }
    if path.bytes().any(|byte| matches!(byte, b'\\' | b':' | 0)) {
        return Err(bad(
            "backslash, colon and NUL are rejected in include paths",
        ));
    }
    let parts: Vec<String> = path.split('/').map(str::to_owned).collect();
    if parts.len() > 64 {
        return Err(bad("include path has more than 64 components"));
    }
    if parts
        .iter()
        .any(|part| part.is_empty() || part == "." || part == "..")
    {
        return Err(bad(
            "empty, '.' and '..' include path components are rejected",
        ));
    }
    Ok(parts)
}

/// Access to bundle files by key. Lookups happen in expansion order.
trait Files {
    fn lookup(&mut self, key: &Key, file: usize, offset: usize) -> Result<Option<usize>, Error>;
    fn get(&self, index: usize) -> &BundleFile;
}

struct Sealed<'b> {
    bundle: &'b Bundle,
    index: BTreeMap<Key, usize>,
    reached: Vec<usize>,
}

impl Files for Sealed<'_> {
    fn lookup(&mut self, key: &Key, _: usize, _: usize) -> Result<Option<usize>, Error> {
        let found = self.index.get(key).copied();
        if let Some(index) = found
            && !self.reached.contains(&index)
        {
            self.reached.push(index);
        }
        Ok(found)
    }
    fn get(&self, index: usize) -> &BundleFile {
        &self.bundle.files[index]
    }
}

struct Disk<'l> {
    base: PathBuf,
    tptp: Option<PathBuf>,
    limits: &'l Limits,
    bundle: Bundle,
    index: BTreeMap<Key, usize>,
    total: usize,
}

impl Disk<'_> {
    fn read(&mut self, path: &Path, key: Key, file: usize, offset: usize) -> Result<usize, Error> {
        let io = |message: &str| fail(ErrorKind::InvalidInput, Reason::Io, file, offset, message);
        if self.bundle.files.len() >= self.limits.max_files {
            return Err(Error::resource("bundle file limit exceeded").in_file(file));
        }
        let mut handle = std::fs::File::open(path).map_err(|_| io("cannot open include file"))?;
        let metadata = handle
            .metadata()
            .map_err(|_| io("cannot inspect include file"))?;
        if !metadata.is_file() {
            return Err(fail(
                ErrorKind::InvalidInput,
                Reason::NotRegular,
                file,
                offset,
                "include target is not a regular file",
            ));
        }
        let cap = self.limits.input.max_input_bytes;
        let mut bytes = Vec::new();
        (&mut handle)
            .take(cap as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| io("cannot read include file"))?;
        if bytes.len() > cap {
            return Err(Error::resource("input byte limit exceeded").in_file(file));
        }
        self.total += bytes.len();
        if self.total > self.limits.max_bundle_bytes {
            return Err(Error::resource("bundle byte limit exceeded").in_file(file));
        }
        let index = self.bundle.files.len();
        self.index.insert(key.clone(), index);
        self.bundle.files.push(BundleFile { key, bytes });
        Ok(index)
    }
}

impl Files for Disk<'_> {
    fn lookup(&mut self, key: &Key, file: usize, offset: usize) -> Result<Option<usize>, Error> {
        if let Some(index) = self.index.get(key) {
            return Ok(Some(*index));
        }
        let Some(mut path) = (match key.root {
            Root::Base => Some(self.base.clone()),
            Root::Tptp => self.tptp.clone(),
        }) else {
            return Ok(None);
        };
        for (position, component) in key.path.iter().enumerate() {
            path.push(component);
            let metadata = match std::fs::symlink_metadata(&path) {
                Ok(value) => value,
                Err(error)
                    if matches!(
                        error.kind(),
                        std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
                    ) =>
                {
                    return Ok(None);
                }
                Err(_) => {
                    return Err(fail(
                        ErrorKind::InvalidInput,
                        Reason::Io,
                        file,
                        offset,
                        "cannot inspect include path",
                    ));
                }
            };
            if metadata.file_type().is_symlink() {
                return Err(fail(
                    ErrorKind::InvalidInput,
                    Reason::Symlink,
                    file,
                    offset,
                    "symbolic links are rejected in include paths",
                ));
            }
            let last = position + 1 == key.path.len();
            if !last && !metadata.is_dir() {
                return Ok(None);
            }
            if last && !metadata.is_file() {
                return Err(fail(
                    ErrorKind::InvalidInput,
                    Reason::NotRegular,
                    file,
                    offset,
                    "include target is not a regular file",
                ));
            }
        }
        self.read(&path, key.clone(), file, offset).map(Some)
    }
    fn get(&self, index: usize) -> &BundleFile {
        &self.bundle.files[index]
    }
}

struct Expander<'l, F> {
    files: F,
    limits: &'l Limits,
    framed: BTreeMap<usize, Framed>,
    /// Lexing work of every framed file, carried into the final parse.
    lexed: Statistics,
    framing: Statistics,
    stack: Vec<usize>,
    directives: usize,
    /// Expansion bookkeeping, bounded by `max_operations` on its own.
    work: usize,
}

type Item = (usize, usize);

impl<F: Files> Expander<'_, F> {
    fn frame(&mut self, index: usize) -> Result<(), Error> {
        if self.framed.contains_key(&index) {
            return Ok(());
        }
        let bytes = self.files.get(index).bytes.clone();
        let mut lexing = Statistics {
            operations: self.framing.operations,
            ..Statistics::default()
        };
        let tokens = lex(&bytes, self.limits, &mut lexing).map_err(|e| e.in_file(index))?;
        self.lexed.operations += lexing.operations - self.framing.operations;
        let mut parser = Parser::new(
            tokens,
            bytes.len(),
            self.limits,
            Statistics {
                operations: lexing.operations,
                ..self.framing
            },
        );
        // Unselected formulas are checked here too; only the final pass
        // counts distinct objects against their cap.
        parser.distinct_cap = usize::MAX;
        let mut names = BTreeSet::new();
        let mut statements = Vec::new();
        let mut formulas = 0;
        while parser.peek().is_some() {
            // The checker's per-file limit: the statement after max_clauses formulas is refused,
            // whether it is a formula or an include directive.
            if formulas >= self.limits.input.max_clauses {
                return Err(Error::resource("input declaration limit exceeded").in_file(index));
            }
            let start = parser.cursor;
            let statement = parser
                .statement(Some(&mut names))
                .map_err(|e| e.in_file(index))?;
            formulas += usize::from(matches!(statement, Statement::Formula(..)));
            statements.push((start..parser.cursor, statement));
        }
        self.framing = parser.statistics;
        self.framed.insert(
            index,
            Framed {
                tokens: parser.tokens,
                statements,
            },
        );
        Ok(())
    }

    fn resolve(&mut self, including: usize, include: &Include) -> Result<usize, Error> {
        let parts = components(&include.path, including, include.path_offset)?;
        let key = &self.files.get(including).key;
        let mut local = key.path[..key.path.len() - 1].to_vec();
        local.extend(parts.iter().cloned());
        let candidates = [
            Key {
                root: key.root,
                path: local,
            },
            Key {
                root: crate::Root::Tptp,
                path: parts,
            },
        ];
        for candidate in candidates {
            if candidate.path.len() > 64 {
                return Err(fail(
                    ErrorKind::InvalidInput,
                    Reason::PathSyntax,
                    including,
                    include.path_offset,
                    "resolved include path has more than 64 components",
                ));
            }
            if let Some(index) = self
                .files
                .lookup(&candidate, including, include.path_offset)?
            {
                return Ok(index);
            }
        }
        Err(fail(
            ErrorKind::InvalidInput,
            Reason::Missing,
            including,
            include.path_offset,
            "included file not found",
        ))
    }

    fn tick(&mut self) -> Result<(), Error> {
        if self.work >= self.limits.input.max_operations {
            return Err(Error::resource("include expansion work limit exceeded"));
        }
        self.work += 1;
        Ok(())
    }

    /// Complete expansion of one file: its formulas and, recursively, the
    /// selected formulas of its includes, each source identity once.
    fn closure(&mut self, index: usize) -> Result<Vec<Item>, Error> {
        self.frame(index)?;
        let count = self.framed[&index].statements.len();
        let mut output = Vec::new();
        let mut seen = BTreeSet::new();
        for statement in 0..count {
            let include = match &self.framed[&index].statements[statement].1 {
                Statement::Formula(..) => {
                    self.tick()?;
                    if seen.insert((index, statement)) {
                        output.push((index, statement));
                    }
                    continue;
                }
                Statement::Include(include) => include.clone(),
            };
            self.directives += 1;
            if self.directives > self.limits.max_include_directives {
                return Err(Error::resource("include directive limit exceeded").in_file(index));
            }
            if self.stack.len() > self.limits.max_include_depth {
                return Err(Error::resource("include depth limit exceeded").in_file(index));
            }
            let child = self.resolve(index, &include)?;
            if self.stack.contains(&child) {
                return Err(fail(
                    ErrorKind::InvalidInput,
                    Reason::Cycle,
                    index,
                    include.path_offset,
                    "include cycle",
                ));
            }
            self.stack.push(child);
            let items = self.closure(child);
            self.stack.pop();
            for item in self.select(items?, &include, index)? {
                self.tick()?;
                if seen.insert(item) {
                    output.push(item);
                }
            }
        }
        Ok(output)
    }

    fn name(&self, item: Item) -> (NameKind, &str) {
        match &self.framed[&item.0].statements[item.1].1 {
            Statement::Formula(formula) => {
                let declaration = &formula.0;
                (declaration.name_kind, declaration.name.as_str())
            }
            Statement::Include(_) => unreachable!("closures hold formulas only"),
        }
    }

    /// The problem library rule: every listed name matches exactly one
    /// formula of the included file's complete expansion.
    fn select(
        &mut self,
        items: Vec<Item>,
        include: &Include,
        index: usize,
    ) -> Result<Vec<Item>, Error> {
        let Selection::Names(names) = &include.selection else {
            return Ok(items);
        };
        let wanted: BTreeSet<(NameKind, &str)> = names
            .iter()
            .map(|(kind, name)| (*kind, name.as_str()))
            .collect();
        let mut counts: BTreeMap<(NameKind, &str), usize> = BTreeMap::new();
        let mut kept = Vec::new();
        for item in &items {
            let name = self.name(*item);
            if wanted.contains(&name) {
                *counts.entry(name).or_default() += 1;
                kept.push(*item);
            }
        }
        // Report the first failing name in list order.
        for (kind, name) in names {
            match counts.get(&(*kind, name.as_str())).copied().unwrap_or(0) {
                0 => {
                    return Err(fail(
                        ErrorKind::InvalidInput,
                        Reason::SelectionMissing,
                        index,
                        include.path_offset,
                        "selected formula name not found",
                    ));
                }
                1 => {}
                _ => {
                    return Err(fail(
                        ErrorKind::InvalidInput,
                        Reason::SelectionAmbiguous,
                        index,
                        include.path_offset,
                        "selected formula name occurs more than once",
                    ));
                }
            }
        }
        Ok(kept)
    }
}

/// Recompute the expanded problem from a sealed bundle. The bundle must hold
/// exactly the files that resolution reaches, in first-reach order.
pub fn expand(bundle: &Bundle, limits: &Limits) -> Result<Expanded, Error> {
    let total = bundle
        .files
        .iter()
        .try_fold(0usize, |sum, file| sum.checked_add(file.bytes.len()));
    if total.is_none_or(|value| value > limits.max_bundle_bytes) {
        return Err(Error::resource("bundle byte limit exceeded"));
    }
    if bundle.files.is_empty() || bundle.files.len() > limits.max_files {
        return Err(shape("a bundle needs 1 to max_files files"));
    }
    let mut index = BTreeMap::new();
    for (position, file) in bundle.files.iter().enumerate() {
        if index.insert(file.key.clone(), position).is_some() {
            return Err(shape("duplicate bundle key"));
        }
    }
    let mut expander = Expander {
        files: Sealed {
            bundle,
            index,
            reached: vec![0],
        },
        limits,
        framed: BTreeMap::new(),
        lexed: Statistics::default(),
        framing: Statistics::default(),
        stack: vec![0],
        directives: 0,
        work: 0,
    };
    let items = expander.closure(0)?;
    if expander.files.reached != (0..bundle.files.len()).collect::<Vec<_>>() {
        return Err(shape(
            "bundle files are not exactly the reached files in order",
        ));
    }
    finish(
        bundle.clone(),
        &expander.framed,
        expander.lexed,
        items,
        limits,
    )
}

fn shape(message: &str) -> Error {
    Error {
        kind: ErrorKind::InvalidInput,
        reason: Reason::BundleShape,
        file: None,
        offset: None,
        message: message.into(),
    }
}

/// Read the top-level file and every reached include, then expand the
/// resulting bundle. The returned problem depends only on that bundle.
pub fn capture(top: &Path, tptp_root: Option<&Path>, limits: &Limits) -> Result<Expanded, Error> {
    let top_error = |reason, message| Error {
        kind: ErrorKind::InvalidInput,
        reason,
        file: Some(0),
        offset: None,
        message: String::from(message),
    };
    let name = top
        .file_name()
        .and_then(|value| value.to_str())
        .ok_or_else(|| top_error(Reason::PathSyntax, "top-level path needs a UTF-8 file name"))?;
    let base = match top.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
        _ => PathBuf::from("."),
    };
    let metadata = std::fs::symlink_metadata(top)
        .map_err(|_| top_error(Reason::Missing, "cannot inspect the top-level file"))?;
    if metadata.file_type().is_symlink() {
        return Err(top_error(
            Reason::Symlink,
            "the top-level file is a symbolic link",
        ));
    }
    let mut disk = Disk {
        base,
        tptp: tptp_root.map(Path::to_path_buf),
        limits,
        bundle: Bundle { files: Vec::new() },
        index: BTreeMap::new(),
        total: 0,
    };
    let key = Key {
        root: Root::Base,
        path: vec![name.to_owned()],
    };
    disk.read(top, key, 0, 0)?;
    let mut expander = Expander {
        files: disk,
        limits,
        framed: BTreeMap::new(),
        lexed: Statistics::default(),
        framing: Statistics::default(),
        stack: vec![0],
        directives: 0,
        work: 0,
    };
    expander.closure(0)?;
    expand(&expander.files.bundle, limits)
}

fn finish(
    bundle: Bundle,
    framed: &BTreeMap<usize, Framed>,
    lexed: Statistics,
    items: Vec<Item>,
    limits: &Limits,
) -> Result<Expanded, Error> {
    let mut parser = Parser::new(Vec::new(), 0, limits, lexed);
    let mut declarations = Vec::new();
    let mut sources = Vec::new();
    // Each item is a distinct (file, statement) pair, so the per-file limit times the number of
    // files bounds the expansion; the checker has no other count of expanded declarations.
    let expanded = limits.input.max_clauses.saturating_mul(bundle.files.len());
    for (file, statement) in items {
        if declarations.len() >= expanded {
            return Err(Error::resource("input declaration limit exceeded"));
        }
        let framed_file = &framed[&file];
        let range = framed_file.statements[statement].0.clone();
        parser.tokens = framed_file.tokens[range].to_vec();
        parser.cursor = 0;
        parser.input_len = bundle.files[file].bytes.len();
        let Statement::Formula(formula) = parser.statement(None).map_err(|e| e.in_file(file))?
        else {
            unreachable!("expanded items are formulas");
        };
        let (declaration, annotation) = *formula;
        declarations.push(declaration);
        sources.push(Source::File {
            file,
            statement,
            annotation,
        });
    }
    // The distinct-object cap bounds the generated clauses, n(n-1)/2 for n objects; they are not
    // counted as expanded declarations, as the checker adds them in a row of their own.
    let objects = std::mem::take(&mut parser.distinct);
    for left in 0..objects.len() {
        for right in left + 1..objects.len() {
            let constant = |position: usize| Term::Fun(objects[position].0, Vec::new());
            declarations.push(Declaration {
                name: String::new(),
                name_kind: NameKind::Atom,
                bytes: 0..0,
                variables: Vec::new(),
                body_bytes: 0..0,
                body: Body::Cnf(vec![CnfLiteral::Ordinary(Literal {
                    positive: false,
                    atom: Atom::Equal(constant(left), constant(right)),
                })]),
            });
            sources.push(Source::DistinctPair { left, right });
        }
    }
    Ok(Expanded {
        bundle,
        parsed: Parsed {
            functions: parser.functions.finish(),
            predicates: parser.predicates.finish(),
            declarations,
            statistics: parser.statistics,
        },
        sources,
        distinct_objects: objects,
    })
}
