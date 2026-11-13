// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The version-8 profile end to end on synthetic binaries: the status block, the exit code, the run record and
//! the stages that ran. The binaries are shell scripts that follow each contract. These are contract controls,
//! not proof acceptance evidence.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use fang_json::{Object, ParseLimits, Value};
use fang_launcher::capability;
use fang_launcher::v8::run::{
    OBJECT_TSTP_SCOPE, SIGNED_TSTP_SCOPE, STATEMENT_LIMIT_NOTE, exit_code,
};
use fang_launcher::v8::{bundle, protocol, signed};

const SOURCE: &[u8] = b"cnf(a,axiom,($false)).";
const SINGLE_SIGNED: &[u8] = b"fof(a,axiom,p). fof(g,conjecture,p).";
const KERNEL_FLAGS: [&str; 8] = [
    "--check",
    "kernel",
    "--wall-seconds",
    "600",
    "--memory-mib",
    "4096",
    "--max-artifact-bytes",
    "1073741824",
];
const NONE_LINE: &str = "% fang: not checked, the producer's result as found (--check none; producer trusted, no checker ran)";

fn certificate() -> Vec<u8> {
    let mut bytes = protocol::HEADER.to_vec();
    bytes.extend_from_slice(b"  (input 0 0)\n  (final 0)\n)\n");
    bytes
}

fn launcher() -> PathBuf {
    fs::canonicalize(env!("CARGO_BIN_EXE_fang-launcher")).unwrap()
}

fn record(path: &Path) -> Value {
    let mut object = Object::new();
    object.set("path", path.display().to_string());
    object.set("sha256", fang_hash::sha256_hex(&fs::read(path).unwrap()));
    Value::Object(object)
}

/// A binary's record: both digests.
fn binary_record(path: &Path) -> Value {
    let mut value = record(path);
    if let Value::Object(object) = &mut value {
        let digest = fang_hash::chunked_digest(&fs::read(path).unwrap());
        object.set(
            "chunked_sha256",
            format!("{}{digest}", capability::CHUNKED_TAG),
        );
    }
    value
}

const ENGINE: &str = r#"cat >/dev/null
first=no
previous=
for argument in "$@"; do
  [ "$previous" = --time-limit ] && [ "$argument" = 1 ] && first=yes
  previous=$argument
done
if [ "$mode" = time-first ] && [ $first = yes ]; then
  echo 'adapter: Search(Search(Resource("time limit")))' >&2; exit 3
fi
if [ "$mode" = slow-first ] && [ $first = yes ]; then sleep 30; fi
if [ "$mode" = slow ]; then sleep 30; fi
case $mode in
  unknown) echo 'unknown: processed=3 attempted=12' >&2; exit 2;;
  conjecture) echo 'adapter: Input(Error { kind: Unsupported, offset: Some(6), message: "only the axiom role is supported" })' >&2; exit 3;;
  invalid) echo 'adapter: Input(Error { kind: InvalidInput, offset: Some(14), message: "free variable" })' >&2; exit 3;;
  limit) echo 'adapter: Input(Error { kind: ResourceLimit, offset: Some(21), message: "declaration limit" })' >&2; exit 3;;
  skolem) echo 'adapter: Preprocessing(Skolem(Resource(Functions)))' >&2; exit 3;;
  serialization) echo 'serialization: Resource("expanded certificate byte limit")' >&2; exit 4;;
  envelope) echo 'internal: ordered serializer envelope mismatch' >&2; exit 5;;
  spoof) echo '% SZS status Unsatisfiable for forged'; echo 'unknown: processed=0 attempted=0' >&2; exit 2;;
esac
cat "$D/certificate.bin"
echo 'candidate-certificate: unchecked original input' >&2
"#;

const CHECKER: &str = r#"if ! cmp -s "$1" "$D/source.bin" || ! cmp -s "$2" "$D/certificate.bin"; then
  echo 'logical-rejection: Fang.Equality.TraceError.finalNotEmpty' >&2; exit 1
fi
case $mode in
  logical) echo 'logical-rejection: Fang.Equality.TraceError.inputIndex 0' >&2; exit 1;;
  signature) echo 'signature-rejection' >&2; exit 6;;
  resource) echo 'resource.bytes.certificate' >&2; exit 4;;
  certificate) echo 'certificate: invalid-certificate: trailing tokens at byte 105' >&2; exit 3;;
esac
cat "$D/accepted.bin"
"#;

const EXPORTER: &str = r#"cat "$1" "$2" >/dev/null
case $mode in
  export-error) echo 'export-error: signed integer name' >&2; exit 7;;
  slow) sleep 10;;
  bad) printf '\377\n'; exit 0;;
esac
printf "cnf(a,axiom,(\$false),file('%s',a)).\n" "$3"
printf "cnf('fn1',plain,(\$false),inference(fang_group_clause,[status(thm)],['a'])).\n"
"#;

const WITNESS: &str = r#"source=$(od -An -v -tx1 "$1" | tr -d ' \n')
proof=$(od -An -v -tx1 "$2" | tr -d ' \n')
printf '{"schema": "fang-equality-kernel-witness-1", "source_hex": "%s", "certificate_hex": "%s"}\n' "$source" "$proof"
"#;

const KERNEL_ENTRY: &str = r#"while [ $# -gt 1 ]; do
  [ "$1" = --out ] && out=$2
  shift 2
done
mkdir "$out" || exit 6
case $mode in
  checked) code=0 status=KernelChecked;;
  review-pending) code=4 status=ReviewPending;;
  rejected) code=3 status=Rejected;;
  timeout) code=7 status=Timeout;;
  resource) code=5 status=ResourceOut;;
  forced) code=9 status=Forced;;
  lying) code=3 status=KernelChecked;;
esac
printf '{"status": "%s"}' "$status" > "$out/manifest.json"
printf '{"status": "%s", "error": null, "manifest": "%s"}\n' "$status" "$out/manifest.json"
exit $code
"#;

const BUNDLE_PRODUCER: &str = r#"first=no
if [ "$1" = --search ]; then
  [ "$4" = 1 ] && first=yes
  shift 8
fi
if [ "$mode" = time-first ] && [ $first = yes ]; then
  echo 'adapter: Search(Search(Resource("time limit")))' >&2; exit 3
fi
top=$1
root=
[ "$2" = --tptp-root ] && root=$3
case $mode in
  missing) echo 'capture: InvalidInput Missing file=Some(0) offset=Some(8)' >&2; exit 3;;
  limit) echo 'capture: ResourceLimit Limit file=Some(0) offset=None' >&2; exit 3;;
esac
cat "${top%/*}/ax.ax" >/dev/null || exit 9
files="[\"base\", \"${top##*/}\"], [\"base\", \"ax.ax\"]"
if [ -n "$root" ]; then
  cat "$root/Axioms/eq.ax" >/dev/null || exit 9
  files="$files, [\"tptp\", \"Axioms/eq.ax\"]"
fi
echo "{\"bundle_sha256\": \"0000000000000000000000000000000000000000000000000000000000000000\", \"files\": [$files], \"declarations\": 2, \"objects\": 1}" >&2
cat "$D/certificate.bin"
echo 'candidate-certificate: unchecked bundle input' >&2
"#;

/// The checks the bundle checker and exporter share: the certificate and the first two files' names.
const BUNDLE_SHAPE: &str = r#"shape() { echo 'bundle.shape' >&2; exit 2; }
cmp -s "$1" "$D/certificate.bin" || shape
shift
[ "$1 $2" = "base problem.p" ] && [ "$4 $5" = "base ax.ax" ] || shape
"#;

const BUNDLE_CHECKER: &str = r#"if [ "$mode" = reject ]; then
  echo 'logical-rejection: Fang.Equality.TraceError.finalNotEmpty' >&2; exit 1
fi
index=0
while [ $# -gt 0 ]; do
  cmp -s "$3" "$D/bundle-expected-$index.bin" || shape
  index=$((index + 1))
  shift 3
done
[ -e "$D/bundle-expected-$index.bin" ] && shape
cat "$D/bundle-accepted.bin"
"#;

const BUNDLE_EXPORTER: &str = r#"if [ "$mode" = export-error ]; then
  echo 'export-error: bundle document' >&2; exit 7
fi
echo "fof(b,axiom,\$false,file('ax.ax',b))."
"#;

const SIGNED_PRODUCER: &str = r#"first=no
if [ "$1" = --search ]; then
  [ "$4" = 1 ] && first=yes
  shift 8
fi
if [ "$1" = --inputs ]; then task=inputs; else task="goal-$2"; fi
if [ "$mode" = unknown ] || { [ "$mode" = unknown-goal-1 ] && [ $task = goal-1 ]; }; then
  echo 'unknown: processed=3 attempted=4' >&2; exit 2
fi
if [ "$mode" = time-first ] && [ $first = yes ]; then
  echo 'error: internal Search(Search(Resource("time limit")))' >&2; exit 1
fi
cat "$D/certificate.bin"
printf '%% %s\n' "$task"
echo 'candidate-certificate: unchecked signed bundle task' >&2
"#;

const SIGNED_CHECKER: &str = r#"shape() { echo 'bundle.shape' >&2; exit 2; }
case $mode in
  no-goals) count=0;;
  one-goal) count=1;;
  *) count=2;;
esac
item() { case $1 in 0) echo '0 1';; 1) echo '1 0';; esac; }
kind=$1
case $kind in
  --goals) shift;;
  --inputs) proof=$2; task=inputs; shift 2;;
  *) index=$2; proof=$3; task="goal-$2"; shift 3;;
esac
line=0
while [ $# -gt 0 ]; do
  line=$((line + 1))
  [ "$1 $2" = "$(sed -n "${line}p" "$D/signed-order.txt")" ] || shape
  cmp -s "$3" "$D/signed-expected-$((line - 1)).bin" || shape
  shift 3
done
[ "$line" -eq "$(wc -l < "$D/signed-order.txt")" ] || shape
if [ "$mode" = unsupported ]; then echo 'bundle.frame.unsupported:12' >&2; exit 2; fi
if [ "$kind" = --goals ]; then
  echo "goals $count"
  goal=0
  while [ $goal -lt $count ]; do echo "goal $goal item $(item $goal)"; goal=$((goal + 1)); done
  exit 0
fi
if ! { cat "$D/certificate.bin"; printf '%% %s\n' "$task"; } | cmp -s - "$proof"; then
  echo 'logical-rejection: Fang.Equality.TraceError.finalNotEmpty' >&2; exit 1
fi
if [ $task = inputs ]; then
  if [ $count -gt 0 ]; then echo 'task.goals-present' >&2; exit 2; fi
  echo 'accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)'; exit 0
fi
set -- $(item $index)
file=$1
if [ "$mode" = wrong-item ] && [ $index = 1 ]; then file=7; fi
echo "accepted-goal $index item $file $2 (native checker; compiler/runtime trusted)"
"#;

#[test]
fn named_signed_single_uses_stdin_and_its_own_pinned_producer() {
    for (mode, expected) in [("one-goal", "Theorem"), ("no-goals", "Unsatisfiable")] {
        let mut fixture = Fixture::new();
        fixture.write_signed("candidate", mode, true);
        let body = format!(
            "cmp -s - \"$D/signed-expected-0.bin\" || exit 64\n[ $# -eq 10 ] || [ $# -eq 9 ] || exit 64\n{}",
            SIGNED_PRODUCER.replace("unchecked signed bundle task", "unchecked signed task")
        );
        let named = fixture.script("signed-single-producer", &body, "candidate");
        fixture.section("signed").set("single_producer", named);
        fixture.save();
        let run = fixture.invoke(expected, &COMPILED, "run-named");
        assert!(verified(run.manifest()).contains(&fixture.named("signed-single-producer")));
        assert!(!verified(run.manifest()).contains(&fixture.named("signed-producer")));
        fs::write(fixture.path("signed-single-producer"), b"changed").unwrap();
        let refused = fixture.invoke("Error", &COMPILED, "run-changed");
        assert!(!stages(refused.manifest()).contains(&"produce-goal-0".to_string()));
        assert!(!stages(refused.manifest()).contains(&"produce-inputs".to_string()));
    }
}

#[test]
fn cited_bundle_keeps_the_premise_line_inside_the_checked_certificate_and_byte_cap() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "two-goals", false);
    let named = fixture.script("signed-single-producer", "exit 64\n", "");
    fixture.section("signed").set("single_producer", named);
    fixture.save();
    let proof = fs::read(fixture.path("certificate.bin")).unwrap();
    let cited = [b"(premises (item 1 1))\n".as_slice(), &proof].concat();
    fs::write(fixture.path("certificate.bin"), &cited).unwrap();
    let run = fixture.invoke("Theorem", &COMPILED, "run-cited");
    assert!(!verified(run.manifest()).contains(&fixture.named("signed-single-producer")));
    assert!(
        fs::read(fixture.path("run-cited/proof-goal-0.fang"))
            .unwrap()
            .starts_with(&cited)
    );
    let cap = proof.len().to_string();
    fixture.invoke(
        "ResourceOut",
        &["--check", "compiled", "--max-certificate-bytes", &cap],
        "run-capped",
    );
    fs::write(fixture.path("certificate.bin"), &proof).unwrap();
    let refused = fixture.invoke("Error", &COMPILED, "run-missing-prefix");
    assert!(!stages(refused.manifest()).contains(&"check-goal-0".to_string()));
}

const GOAL_EXPORTER: &str = r#"if ! cmp -s "$1" "$D/goal-source.bin" || ! { cat "$D/certificate.bin"; printf '%% goal-%s\n' "$3"; } | cmp -s - "$2" || [ "$4" != problem.p ]; then
  echo 'goal.shape' >&2; exit 2
fi
if [ "$mode" = export-error ]; then echo 'export-error: the goal task is not accepted' >&2; exit 7; fi
echo "fof(g$3,negated_conjecture,~p,inference(negate,[status(cth)],[g]))."
"#;

const INPUTS_EXPORTER: &str = r#"if [ "$1" != --inputs ] || ! cmp -s "$2" "$D/goal-source.bin" || [ "$4" != problem.p ]; then
  echo 'inputs.shape' >&2; exit 2
fi
if ! { cat "$D/certificate.bin"; printf '%% inputs\n'; } | cmp -s - "$3"; then echo 'inputs.shape' >&2; exit 2; fi
echo "fof(a,axiom,p,file('problem.p',a))."
"#;

const MODEL_FIND: &str = r#"line=
stop=no
resumed=no
for argument in "$@"; do
  [ "$argument" = --memory-mib ] && stop=yes
  [ $stop = no ] && line="$line${line:+ }$argument"
  [ "$argument" = --from-domain ] && resumed=yes
done
[ $resumed = yes ] && line="$line resume"
echo "$line" >> "$D/model-calls.log"
if [ "$mode" = candidate ] || { [ "$mode" = second ] && [ $resumed = yes ]; }; then
  printf 'fang-model 1\n(model)\n'; printf 'candidate-model: unchecked domain 2\n' >&2; exit 0
fi
if [ "$mode" = refused ]; then printf 'refused: unsupported input\n' >&2; exit 3; fi
printf 'no-model: no model up to domain 3\n' >&2
exit 2
"#;

const MODEL_CHECK: &str = r#"trusted=' (native checker; compiler/runtime trusted)'
if [ "$mode" = reject ]; then printf 'model-rejection: the formula a is false\n' >&2; exit 1; fi
if [ "$1" = --goal ]; then
  item='0 1'
  [ "$mode" = wrong-item ] && item='7 0'
  echo "accepted-countermodel-goal $2 item $item$trusted"
else
  echo "accepted-model-${1#--}$trusted"
fi
"#;

/// One synthetic installation in a fresh directory.
struct Fixture {
    root: PathBuf,
    input: PathBuf,
    capability: PathBuf,
    config: Object,
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// One finished command.
struct Run {
    output: Output,
    lines: Vec<String>,
    manifest: Option<Object>,
}

impl Run {
    fn manifest(&self) -> &Object {
        self.manifest.as_ref().expect("the run wrote its record")
    }

    fn stdout(&self) -> String {
        String::from_utf8_lossy(&self.output.stdout).into_owned()
    }

    fn stderr(&self) -> String {
        String::from_utf8_lossy(&self.output.stderr).into_owned()
    }
}

fn at<'a>(value: &'a Object, path: &[&str]) -> &'a Value {
    let mut current = value
        .get(path[0])
        .unwrap_or_else(|| panic!("no {}", path[0]));
    for key in &path[1..] {
        current = current.get(key).unwrap_or_else(|| panic!("no {key}"));
    }
    current
}

fn text<'a>(value: &'a Object, path: &[&str]) -> &'a str {
    at(value, path).as_str().unwrap()
}

fn rows<'a>(value: &'a Object, path: &[&str]) -> &'a [Value] {
    at(value, path).as_array().unwrap()
}

fn stages(manifest: &Object) -> Vec<String> {
    rows(manifest, &["processes"])
        .iter()
        .map(|row| row.get("stage").unwrap().as_str().unwrap().to_string())
        .collect()
}

fn column(manifest: &Object, path: &[&str], key: &str) -> Vec<String> {
    rows(manifest, path)
        .iter()
        .map(|row| row.get(key).unwrap().as_str().unwrap().to_string())
        .collect()
}

fn verified(manifest: &Object) -> Vec<String> {
    rows(manifest, &["verified_before_run"])
        .iter()
        .map(|row| row.as_str().unwrap().to_string())
        .collect()
}

fn passes(manifest: &Object) -> Vec<(i64, String)> {
    rows(manifest, &["refutation_passes"])
        .iter()
        .map(|row| {
            (
                row.get("pass").unwrap().as_i64().unwrap(),
                row.get("status").unwrap().as_str().unwrap().to_string(),
            )
        })
        .collect()
}

fn time_limit(row: &Value) -> i64 {
    let command: Vec<&str> = row
        .get("command")
        .unwrap()
        .as_array()
        .unwrap()
        .iter()
        .map(|part| part.as_str().unwrap())
        .collect();
    let at = command
        .iter()
        .position(|part| *part == "--time-limit")
        .unwrap();
    command[at + 1].parse().unwrap()
}

impl Fixture {
    fn new() -> Fixture {
        static COUNT: AtomicUsize = AtomicUsize::new(0);
        let name = format!(
            "fang-v8-control-{}-{}",
            std::process::id(),
            COUNT.fetch_add(1, Ordering::SeqCst)
        );
        let root = std::env::temp_dir().join(name);
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("certificate.bin"), certificate()).unwrap();
        fs::write(root.join("accepted.bin"), protocol::ACCEPTED).unwrap();
        fs::write(root.join("bundle-accepted.bin"), bundle::ACCEPTED).unwrap();
        fs::write(
            root.join("receipt.json"),
            "{\"scope\": \"synthetic control\"}\n",
        )
        .unwrap();
        let input = root.join("problem.p");
        let capability = root.join("capability.json");
        let mut fixture = Fixture {
            root,
            input,
            capability,
            config: Object::new(),
        };
        fixture.set_source(SOURCE);
        fixture.write_binaries("candidate", "accept");
        fixture
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }

    fn named(&self, name: &str) -> String {
        self.path(name).display().to_string()
    }

    /// The input file and the bytes the single-file checker expects.
    fn set_source(&self, data: &[u8]) {
        fs::write(&self.input, data).unwrap();
        fs::write(self.path("source.bin"), data).unwrap();
    }

    fn script(&self, name: &str, body: &str, mode: &str) -> Value {
        let path = self.path(name);
        let text = format!(
            "#!/bin/sh\nmode='{mode}'\nD='{}'\n{body}",
            self.root.display()
        );
        fs::write(&path, text).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        binary_record(&path)
    }

    fn save(&self) {
        let text = fang_json::dumps_manifest(&Value::Object(self.config.clone())).unwrap();
        fs::write(&self.capability, text).unwrap();
    }

    fn section(&mut self, name: &str) -> &mut Object {
        if !matches!(self.config.get(name), Some(Value::Object(_))) {
            self.config.set(name, Value::Object(Object::new()));
        }
        match self.config.get_mut(name) {
            Some(Value::Object(section)) => section,
            _ => unreachable!(),
        }
    }

    fn write_binaries(&mut self, engine_mode: &str, checker_mode: &str) {
        let engine = self.script("engine", ENGINE, engine_mode);
        let checker = self.script("checker", CHECKER, checker_mode);
        if self.config.is_empty() {
            let mut config = Object::new();
            config.set("schema", capability::SCHEMA);
            config.set("language", capability::LANGUAGE);
            config.set("certificate_version", Value::from(8u64));
            config.set("max_input_bytes", Value::from(capability::MAX_BYTES));
            config.set(
                "max_certificate_bytes",
                Value::from(capability::MAX_CERTIFICATE_BYTES),
            );
            config.set("launcher", binary_record(&launcher()));
            config.set(
                "provenance",
                Value::Array(vec![record(&self.path("receipt.json"))]),
            );
            for name in [
                "bundle",
                "signed",
                "kernel",
                "tstp",
                "model",
                "cnf",
                "ground_fof",
            ] {
                config.set(name, Value::Null);
            }
            config.set("per_run_verification", capability::per_run_value());
            config.set("default_check", capability::DEFAULT_CHECK);
            self.config = config;
        }
        self.config.set("engine", engine);
        self.config.set("checker", checker);
        self.save();
    }

    fn write_exporter(&mut self, mode: &str) {
        let exporter = self.script("exporter", EXPORTER, mode);
        let mut tstp = Object::new();
        tstp.set("exporter", exporter);
        self.config.set("tstp", Value::Object(tstp));
        self.save();
    }

    fn write_models(&mut self, find: &str, check: &str) {
        let producer = self.script("model-find", MODEL_FIND, find);
        let checker = self.script("model-check", MODEL_CHECK, check);
        let mut model = Object::new();
        model.set("producer", producer);
        model.set("checker", checker);
        self.config.set("model", Value::Object(model));
        self.save();
    }

    fn model_calls(&self) -> Vec<String> {
        fs::read_to_string(self.path("model-calls.log"))
            .map(|text| text.lines().map(str::to_string).collect())
            .unwrap_or_default()
    }

    fn write_kernel(&mut self, mode: &str) {
        let witness = self.script("witness", WITNESS, "");
        let entry = self.script("kernel-entry", KERNEL_ENTRY, mode);
        fs::write(
            self.path("installation.json"),
            "{\"scope\": \"synthetic kernel installation\"}\n",
        )
        .unwrap();
        let installation = record(&self.path("installation.json"));
        let _ = fs::create_dir(self.path("kernel-runs"));
        let output_root = self.named("kernel-runs");
        let kernel = self.section("kernel");
        kernel.set("witness", witness);
        kernel.set("entry", entry);
        kernel.set("installation", installation);
        kernel.set("output_root", output_root);
        self.save();
    }

    fn write_bundle(&mut self, producer: &str, checker: &str, tptp: bool) -> Vec<Vec<u8>> {
        let top = b"include('ax.ax'). fof(a,axiom,\"x\" = \"y\").".to_vec();
        self.set_source(&top);
        fs::write(self.path("ax.ax"), b"fof(b,axiom,$false).").unwrap();
        let mut contents = vec![top, b"fof(b,axiom,$false).".to_vec()];
        if tptp {
            fs::create_dir_all(self.path("tptp/Axioms")).unwrap();
            fs::write(
                self.path("tptp/Axioms/eq.ax"),
                b"fof(e,axiom,![X]:(X = X)).",
            )
            .unwrap();
            contents.push(b"fof(e,axiom,![X]:(X = X)).".to_vec());
        }
        for index in 0..4 {
            let _ = fs::remove_file(self.path(&format!("bundle-expected-{index}.bin")));
        }
        for (index, data) in contents.iter().enumerate() {
            fs::write(self.path(&format!("bundle-expected-{index}.bin")), data).unwrap();
        }
        let producer = self.script("bundle-producer", BUNDLE_PRODUCER, producer);
        let checker = self.script(
            "bundle-checker",
            &format!("{BUNDLE_SHAPE}{BUNDLE_CHECKER}"),
            checker,
        );
        let section = self.section("bundle");
        section.set("producer", producer);
        section.set("checker", checker);
        self.save();
        contents
    }

    fn write_bundle_exporter(&mut self, mode: &str) {
        self.write_exporter("document");
        let exporter = self.script(
            "bundle-exporter",
            &format!("{BUNDLE_SHAPE}{BUNDLE_EXPORTER}"),
            mode,
        );
        self.section("tstp").set("bundle_exporter", exporter);
        self.save();
    }

    /// The signed binaries over `files` (path relative to the fixture, bytes), the first being the input.
    fn write_signed_files(&mut self, producer: &str, checker: &str, files: &[(&str, &[u8])]) {
        let mut order = String::new();
        for index in 0..4 {
            let _ = fs::remove_file(self.path(&format!("signed-expected-{index}.bin")));
        }
        for (index, (name, data)) in files.iter().enumerate() {
            if index == 0 {
                self.set_source(data);
            } else {
                if let Some(parent) = self.path(name).parent() {
                    fs::create_dir_all(parent).unwrap();
                }
                fs::write(self.path(name), data).unwrap();
            }
            fs::write(self.path(&format!("signed-expected-{index}.bin")), data).unwrap();
            order.push_str(&format!("base {name}\n"));
        }
        fs::write(self.path("signed-order.txt"), order).unwrap();
        fs::write(self.path("goal-source.bin"), files[0].1).unwrap();
        let producer = self.script("signed-producer", SIGNED_PRODUCER, producer);
        let checker = self.script("signed-checker", SIGNED_CHECKER, checker);
        let section = self.section("signed");
        section.set("producer", producer);
        section.set("checker", checker);
        self.save();
    }

    fn write_signed(&mut self, producer: &str, checker: &str, single: bool) {
        if single {
            self.write_signed_files(producer, checker, &[("problem.p", SINGLE_SIGNED)]);
        } else {
            self.write_signed_files(
                producer,
                checker,
                &[
                    (
                        "problem.p",
                        b"% signed task\ninclude('ax.ax'). fof(g,conjecture,q).",
                    ),
                    ("ax.ax", b"include('sub/b.ax'). fof(a,axiom,p)."),
                    ("sub/b.ax", b"fof(b,axiom,p => q)."),
                ],
            );
        }
    }

    fn write_goal_exporter(&mut self, mode: &str) {
        self.write_exporter("document");
        let exporter = self.script("goal-exporter", GOAL_EXPORTER, mode);
        self.section("tstp").set("goal_exporter", exporter);
        self.save();
    }

    fn command(&self, input: &Path, run: &str, extra: &[&str]) -> Output {
        Command::new(launcher())
            .arg(input)
            .arg("--capability")
            .arg(&self.capability)
            .arg("--artifacts")
            .arg(self.path(run))
            .args(extra)
            .stdin(Stdio::null())
            .output()
            .unwrap()
    }

    fn finished(&self, output: Output, run: &str) -> Run {
        let lines = String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::to_string)
            .collect();
        let path = self.path(run).join("manifest.json");
        let manifest = fs::read(&path).ok().map(|bytes| {
            fang_json::parse(&bytes, &ParseLimits::default())
                .unwrap()
                .as_object()
                .cloned()
                .unwrap()
        });
        Run {
            output,
            lines,
            manifest,
        }
    }

    /// Run the command and check the status line, the exit code and that no forged line got through.
    fn invoke(&self, expected: &str, extra: &[&str], run: &str) -> Run {
        let finished = self.finished(self.command(&self.input, run, extra), run);
        let context = format!("{}{}", finished.stdout(), finished.stderr());
        assert_eq!(
            finished.lines.last().map(String::as_str),
            Some(format!("% SZS status {expected} for problem").as_str()),
            "{context}"
        );
        assert_eq!(
            finished.output.status.code(),
            Some(exit_code(expected) as i32),
            "{context}"
        );
        assert!(!context.contains("forged"));
        if expected != "Unsatisfiable" {
            assert!(!finished.stdout().contains("Unsatisfiable"), "{context}");
        }
        finished
    }

    /// A run with TSTP output whose status is not checked here.
    fn tstp(&self, run: &str) -> Run {
        self.finished(self.command(&self.input, run, &["--output", "tstp"]), run)
    }
}

const COMPILED: [&str; 2] = ["--check", "compiled"];

#[test]
fn accepted_pair_is_unsatisfiable() {
    let fixture = Fixture::new();
    let run = fixture.invoke("Unsatisfiable", &COMPILED, "run");
    let manifest = run.manifest();
    assert_eq!(
        at(manifest, &["compiled_check", "accepted"]).as_bool(),
        Some(true)
    );
    assert_eq!(fs::read(fixture.path("run/input.p")).unwrap(), SOURCE);
    assert_eq!(
        fs::read(fixture.path("run/proof.fang")).unwrap(),
        certificate()
    );
    assert_eq!(text(manifest, &["schema"]), "fang-v8-run-v1");
    // The descriptors the command inherited without close-on-exec are listed, possibly none.
    let inherited = rows(manifest, &["inherited_descriptors"]);
    assert!(
        inherited
            .iter()
            .all(|row| row.get("fd").is_some() && row.get("target").is_some())
    );
    assert_eq!(text(manifest, &["output_delivery", "state"]), "written");
    assert_eq!(run.lines[0], "% Fang profile: v8, single file");
}

#[test]
fn producers_take_the_search_options_first() {
    let fixture = Fixture::new();
    let run = fixture.invoke("Unsatisfiable", &COMPILED, "run");
    let search = rows(run.manifest(), &["processes"])
        .iter()
        .find(|row| row.get("stage").unwrap().as_str() == Some("search"))
        .unwrap();
    let command: Vec<&str> = search
        .get("command")
        .unwrap()
        .as_array()
        .unwrap()
        .iter()
        .map(|part| part.as_str().unwrap())
        .collect();
    // The engine reads the sealed input on standard input; the options follow its path directly.
    assert_eq!(command[0], fixture.named("engine"));
    assert_eq!(&command[1..3], ["--search", "v3"]);
    assert_eq!(
        (command[3], command[5], command[7]),
        ("--time-limit", "--memory-mib", "--set")
    );
    assert!(command[4].parse::<i64>().unwrap() <= 60 - 5);
    assert!(
        command[8].starts_with("portfolio=") && command[8].matches(';').count() == 8,
        "{}",
        command[8]
    );
}

#[test]
fn producer_outcomes() {
    for (mode, expected) in [
        ("unknown", "GaveUp"),
        ("conjecture", "Inappropriate"),
        ("invalid", "InputError"),
        ("limit", "ResourceOut"),
        ("skolem", "ResourceOut"),
        ("serialization", "ResourceOut"),
        ("envelope", "Error"),
        ("spoof", "Error"),
    ] {
        let mut fixture = Fixture::new();
        fixture.write_binaries(mode, "accept");
        let run = fixture.invoke(expected, &COMPILED, &format!("run-{mode}"));
        assert!(
            !fixture.path(&format!("run-{mode}/checker")).exists(),
            "{mode}"
        );
        assert!(run.manifest().get("compiled_check").is_none(), "{mode}");
    }
}

#[test]
fn checker_rejection_is_an_error_not_a_result() {
    for (mode, expected) in [
        ("logical", "Error"),
        ("signature", "Error"),
        ("certificate", "Error"),
        ("resource", "ResourceOut"),
    ] {
        let mut fixture = Fixture::new();
        fixture.write_binaries("candidate", mode);
        let run = fixture.invoke(expected, &COMPILED, &format!("run-{mode}"));
        assert_eq!(
            at(run.manifest(), &["compiled_check", "accepted"]).as_bool(),
            Some(false),
            "{mode}"
        );
    }
}

#[test]
fn modes_are_named_on_every_status() {
    let mut fixture = Fixture::new();
    let run = fixture.invoke("Unsatisfiable", &[], "run-default");
    assert_eq!(
        run.lines[1],
        "% fang: checked by the compiled Lean checker (default mode; compiler and runtime trusted)"
    );
    assert_eq!(
        (
            text(run.manifest(), &["check"]),
            text(run.manifest(), &["check_source"])
        ),
        ("compiled", "default")
    );
    let run = fixture.invoke("Unsatisfiable", &COMPILED, "run-explicit");
    assert_eq!(
        run.lines[1],
        "% fang: checked by the compiled Lean checker (--check compiled; compiler and runtime trusted)"
    );
    assert_eq!(text(run.manifest(), &["check_source"]), "explicit");
    fixture.write_binaries("unknown", "accept");
    let run = fixture.invoke("GaveUp", &[], "run-unknown");
    assert!(run.lines[1].starts_with("% fang: checked by the compiled Lean checker (default mode"));
}

#[test]
fn check_none_reports_the_producer_result_unchecked() {
    let mut fixture = Fixture::new();
    // The checker would reject this pair; with --check none it never runs.
    fixture.write_binaries("candidate", "logical");
    let run = fixture.invoke("Unsatisfiable", &["--check", "none"], "run-none");
    let manifest = run.manifest();
    assert_eq!(run.lines[1], NONE_LINE);
    assert_eq!(
        (
            text(manifest, &["check"]),
            text(manifest, &["check_source"])
        ),
        ("none", "explicit")
    );
    assert!(manifest.get("compiled_check").is_none());
    assert!(!fixture.path("run-none/checker").exists());
    assert!(text(manifest, &["reason"]).contains("No checker ran"));
    assert_eq!(text(manifest, &["unchecked", "trust"]), "the producer");
    assert_eq!(
        at(manifest, &["certificate", "accepted"]).as_bool(),
        Some(false)
    );
    assert!(!verified(manifest).contains(&fixture.named("checker")));
    assert!(verified(manifest).contains(&fixture.named("engine")));
    fixture.write_binaries("unknown", "accept");
    let run = fixture.invoke("GaveUp", &["--check", "none"], "run-none-unknown");
    assert_eq!(run.lines[1], NONE_LINE);
}

#[test]
fn check_none_refuses_tstp() {
    let mut fixture = Fixture::new();
    fixture.write_exporter("document");
    let run = fixture.invoke(
        "Inappropriate",
        &["--check", "none", "--output", "tstp"],
        "run-none-tstp",
    );
    assert!(run.stdout().contains("not available with --check none"));
    assert!(!fixture.path("run-none-tstp/search").exists());
}

#[test]
fn check_none_on_bundle_and_signed_paths() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("candidate", "reject", false);
    let run = fixture.invoke("Unsatisfiable", &["--check", "none"], "run-none-bundle");
    assert_eq!(run.lines[1], NONE_LINE);
    assert!(!stages(run.manifest()).contains(&"checker".to_string()));
    assert!(!verified(run.manifest()).contains(&fixture.named("bundle-checker")));
    fixture.write_signed("candidate", "two-goals", false);
    let run = fixture.invoke("Theorem", &["--check", "none"], "run-none-signed");
    assert_eq!(run.lines[1], NONE_LINE);
    let names = stages(run.manifest());
    assert!(names.contains(&"goals".to_string()));
    assert!(!names.iter().any(|stage| stage.starts_with("check-")));
    assert_eq!(
        column(run.manifest(), &["signed", "tasks"], "checker"),
        ["not run (--check none)"; 2]
    );
}

#[test]
fn model_checker_acceptance_is_satisfiable() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_models("candidate", "accept");
    let run = fixture.invoke("Satisfiable", &[], "run-model");
    let manifest = run.manifest();
    assert_eq!(
        run.lines[1],
        "% fang: checked by the compiled Lean model checker (default mode; compiler and runtime trusted)"
    );
    assert_eq!(
        at(manifest, &["model_check", "accepted"]).as_bool(),
        Some(true)
    );
    assert_eq!(
        stages(manifest),
        ["search", "model-find-single-a", "model-check-single-a"]
    );
    assert!(verified(manifest).contains(&fixture.named("model-find")));
    assert!(fixture.model_calls()[0].starts_with("--single --seconds 3"));
}

#[test]
fn proof_in_pass_one_ends_the_run_before_any_model_step() {
    let mut fixture = Fixture::new();
    fixture.write_models("candidate", "accept");
    let run = fixture.invoke("Unsatisfiable", &[], "run-pass-one");
    let manifest = run.manifest();
    assert!(fixture.model_calls().is_empty());
    assert_eq!(stages(manifest), ["search", "checker"]);
    assert_eq!(time_limit(&rows(manifest, &["processes"])[0]), 1);
    assert_eq!(passes(manifest), [(1, "Unsatisfiable".to_string())]);
    assert_eq!(text(manifest, &["certificate", "file"]), "proof.fang");
    assert!(!verified(manifest).contains(&fixture.named("model-find")));
}

#[test]
fn no_model_is_never_a_result_and_the_steps_keep_their_order() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_models("none", "accept");
    let run = fixture.invoke("GaveUp", &[], "run-model-none");
    let manifest = run.manifest();
    let processes = rows(manifest, &["processes"]);
    assert_eq!(
        stages(manifest),
        [
            "search",
            "model-find-single-a",
            "search-pass2",
            "model-find-single-b"
        ]
    );
    assert_eq!(column(manifest, &["model"], "producer"), ["none", "none"]);
    let calls = fixture.model_calls();
    assert!(
        calls[0].starts_with("--single --seconds 3") && !calls[0].ends_with("resume"),
        "{calls:?}"
    );
    assert!(calls[1].ends_with("resume"), "{calls:?}");
    assert_eq!(time_limit(&processes[0]), 1);
    // Round two: pass 2 runs until 80 percent of the 60 s budget, less the checker reserve.
    let second = time_limit(&processes[2]);
    assert!((30..=48 - 5).contains(&second), "{second}");
    assert_eq!(
        passes(manifest),
        [(1, "GaveUp".to_string()), (2, "GaveUp".to_string())]
    );
    assert!(manifest.get("model_check").is_none());
}

#[test]
fn pass_two_starts_from_scratch_after_a_pass_one_stop() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("time-first", "accept");
    fixture.write_models("none", "accept");
    let run = fixture.invoke("Unsatisfiable", &[], "run-pass-two");
    let manifest = run.manifest();
    assert_eq!(
        stages(manifest),
        [
            "search",
            "model-find-single-a",
            "search-pass2",
            "checker-pass2"
        ]
    );
    assert_eq!(
        passes(manifest),
        [
            (1, "ResourceOut".to_string()),
            (2, "Unsatisfiable".to_string())
        ]
    );
    assert_eq!(text(manifest, &["certificate", "file"]), "proof-pass2.fang");
    assert_eq!(
        fs::read(fixture.path("run-pass-two/proof-pass2.fang")).unwrap(),
        certificate()
    );
    assert!(!fixture.path("run-pass-two/proof.fang").exists());
    assert_eq!(
        at(manifest, &["compiled_check", "accepted"]).as_bool(),
        Some(true)
    );
}

#[test]
fn pass_one_deadline_is_its_time_limit_and_the_checker_reserve() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("slow-first", "accept");
    fixture.write_models("none", "accept");
    let started = Instant::now();
    let run = fixture.invoke("Unsatisfiable", &[], "run-pass-one-slow");
    let manifest = run.manifest();
    let first = &rows(manifest, &["processes"])[0];
    assert_eq!(first.get("stage").unwrap().as_str(), Some("search"));
    assert_eq!(
        first.get("classification").unwrap().as_str(),
        Some("Timeout")
    );
    let elapsed = first.get("elapsed_seconds").unwrap().as_f64().unwrap();
    assert!((5.5..=7.5).contains(&elapsed), "{elapsed}");
    assert_eq!(
        passes(manifest),
        [
            (1, "ResourceOut".to_string()),
            (2, "Unsatisfiable".to_string())
        ]
    );
    assert!(started.elapsed() < Duration::from_secs(25));
}

#[test]
fn rejected_model_is_an_error_and_ends_the_run() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_models("candidate", "reject");
    let run = fixture.invoke("Error", &[], "run-model-rejected");
    assert!(text(run.manifest(), &["reason"]).contains("rejected a candidate model"));
    assert_eq!(
        stages(run.manifest()),
        ["search", "model-find-single-a", "model-check-single-a"]
    );
}

#[test]
fn model_slice_b_after_the_search_gives_up() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_models("second", "accept");
    let run = fixture.invoke("Satisfiable", &[], "run-model-second");
    let calls = fixture.model_calls();
    assert_eq!(calls.len(), 2);
    assert!(calls[1].ends_with("resume"));
    assert_eq!(
        stages(run.manifest()),
        [
            "search",
            "model-find-single-a",
            "search-pass2",
            "model-find-single-b",
            "model-check-single-b"
        ]
    );
}

#[test]
fn bundle_and_signed_pass_two_name_their_artifacts_apart() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("time-first", "accept", false);
    fixture.write_models("none", "accept");
    let run = fixture.invoke("Unsatisfiable", &[], "run-bundle-pass-two");
    assert_eq!(
        stages(run.manifest()),
        [
            "search",
            "model-find-bundle-a",
            "search-pass2",
            "checker-pass2"
        ]
    );
    assert!(
        fixture
            .path("run-bundle-pass-two/bundle-pass2-1.p")
            .is_file()
    );
    assert_eq!(
        text(run.manifest(), &["certificate", "file"]),
        "proof-pass2.fang"
    );
    fixture.write_signed("time-first", "one-goal", true);
    fixture.write_goal_exporter("document");
    let run = fixture.tstp("run-signed-pass-two");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.lines[2].starts_with("% SZS status Theorem for problem"));
    assert_eq!(run.lines[3], "% SZS output start CNFRefutation for problem");
    let manifest = run.manifest();
    assert_eq!(
        column(manifest, &["signed", "tasks"], "task"),
        ["goal-0", "goal-0-pass2"]
    );
    assert_eq!(
        column(manifest, &["signed", "tasks"], "producer"),
        ["ResourceOut", "candidate"]
    );
    assert_eq!(
        stages(manifest),
        [
            "goals",
            "produce-goal-0",
            "model-find-goal-0-a",
            "produce-goal-0-pass2",
            "check-goal-0-pass2",
            "export-goal-0-pass2"
        ]
    );
    assert_eq!(text(manifest, &["export", "state"]), "documents");
}

#[test]
fn model_stages_skipped_with_check_none() {
    let mut fixture = Fixture::new();
    fixture.write_models("candidate", "accept");
    let run = fixture.invoke("Unsatisfiable", &["--check", "none"], "run-model-unchecked");
    assert!(fixture.model_calls().is_empty());
    assert!(!verified(run.manifest()).contains(&fixture.named("model-find")));
}

#[test]
fn countermodel_needs_the_listed_item() {
    let mut fixture = Fixture::new();
    fixture.write_signed("unknown", "two-goals", false);
    fixture.write_models("candidate", "accept");
    let run = fixture.invoke("CounterSatisfiable", &[], "run-countermodel");
    assert_eq!(text(run.manifest(), &["model_check", "task"]), "goal-0");
    assert!(stages(run.manifest()).contains(&"goals".to_string()));
    fixture.write_models("candidate", "wrong-item");
    let run = fixture.invoke("Error", &[], "run-countermodel-wrong");
    assert!(text(run.manifest(), &["reason"]).contains("another listed item"));
}

#[test]
fn model_result_with_tstp_prints_no_document_without_a_model_exporter() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_exporter("document");
    fixture.write_models("candidate", "accept");
    let run = fixture.tstp("run-model-tstp");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(
        run.stdout()
            .contains("% SZS status Satisfiable for problem")
    );
    assert!(!run.stdout().contains("SZS output start"));
    assert_eq!(
        run.stderr(),
        "fang: TSTP output prints a refutation; a model result prints no document\n"
    );
}

#[test]
fn model_result_with_tstp_prints_the_finite_model() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_exporter("document");
    fixture.write_models("candidate", "accept");
    for (mode, body) in [
        (
            "document",
            "echo 'fof(fang_domain,fi_domain,! [X] : X = \"e0\").'\n",
        ),
        ("refuse", "echo 'resource.export.cells' >&2; exit 4\n"),
    ] {
        let exporter = fixture.script(&format!("model-export-{mode}"), body, mode);
        fixture.section("model").set("exporter", exporter);
        fixture.save();
        let run = fixture.tstp(&format!("run-model-export-{mode}"));
        assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
        assert!(
            run.stdout()
                .contains("% SZS status Satisfiable for problem")
        );
        assert!(!run.stdout().contains("CNFRefutation"));
        if mode == "document" {
            assert!(
                run.stdout()
                    .contains("% SZS output start FiniteModel for problem")
            );
            assert!(run.stdout().contains("fi_domain"));
            assert_eq!(run.stderr(), "");
        } else {
            assert!(!run.stdout().contains("SZS output start"));
            assert!(
                run.stderr().starts_with("fang: TSTP export failed (exit 4"),
                "{}",
                run.stderr()
            );
        }
    }
}

#[test]
fn problem_name_is_the_file_stem() {
    let fixture = Fixture::new();
    for (name, expected) in [
        ("PUZ001+1.p", "PUZ001+1"),
        ("problem", "problem"),
        ("set.ax", "set.ax"),
    ] {
        let source = fixture.path(name);
        fs::write(&source, SOURCE).unwrap();
        let output = fixture.command(&source, &format!("run-name-{expected}"), &COMPILED);
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            stdout.lines().last(),
            Some(format!("% SZS status Unsatisfiable for {expected}").as_str()),
            "{stdout}"
        );
    }
}

#[test]
fn kernel_below_minimums_is_refused_naming_them() {
    let fixture = Fixture::new();
    let flags = KERNEL_FLAGS[2..].to_vec();
    let mut cases: Vec<Vec<&str>> = vec![vec![], flags[..2].to_vec(), flags[..4].to_vec()];
    let mut short = flags[..4].to_vec();
    short.extend(["--max-artifact-bytes", "1073741823"]);
    cases.push(short);
    for (index, extra) in cases.iter().enumerate() {
        let mut arguments = vec!["--check", "kernel"];
        arguments.extend(extra);
        let run = fixture.invoke("Inappropriate", &arguments, &format!("run-k{index}"));
        assert!(run.stdout().contains(
            "needs at least --wall-seconds 600 --memory-mib 4096 --max-artifact-bytes 1073741824"
        ));
        assert!(run.lines[1].contains("kernel replay requested (--check kernel"));
        assert!(run.manifest.is_none());
        assert!(!fixture.path(&format!("run-k{index}")).exists());
    }
}

#[test]
fn kernel_at_minimums_is_not_installed() {
    let fixture = Fixture::new();
    let run = fixture.invoke("Inappropriate", &KERNEL_FLAGS, "run");
    assert!(run.stdout().contains("Kernel replay is not installed"));
    assert!(run.manifest.is_none());
    assert!(!fixture.path("run").exists());
}

#[test]
fn kernel_checked_is_the_only_kernel_result() {
    let mut fixture = Fixture::new();
    fixture.write_kernel("checked");
    let run = fixture.invoke("Unsatisfiable", &KERNEL_FLAGS, "run-kernel");
    let manifest = run.manifest();
    assert!(run.lines[1].contains("kernel replay requested (--check kernel"));
    assert_eq!(
        at(manifest, &["kernel_check", "accepted"]).as_bool(),
        Some(true)
    );
    assert!(manifest.get("compiled_check").is_none());
    assert!(!fixture.path("run-kernel/checker").exists());
    let hashed = verified(manifest);
    for name in ["witness", "kernel-entry", "installation.json", "engine"] {
        assert!(hashed.contains(&fixture.named(name)), "{name}");
    }
    assert!(!hashed.contains(&fixture.named("checker")));
}

#[test]
fn named_engine_uses_a_separate_pinned_unnamed_producer_for_kernel_replay() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("unknown", "accept");
    fixture.write_kernel("checked");
    fixture.config.set("engine_preparation", "named");
    let producer = fixture.script("kernel-producer", ENGINE, "candidate");
    fixture.section("kernel").set("producer", producer);
    fixture.save();
    let run = fixture.invoke("Unsatisfiable", &KERNEL_FLAGS, "run-kernel-original");
    assert!(verified(run.manifest()).contains(&fixture.named("kernel-producer")));
    assert!(!verified(run.manifest()).contains(&fixture.named("engine")));
    let compiled = fixture.invoke("GaveUp", &COMPILED, "run-named-compiled");
    assert!(verified(compiled.manifest()).contains(&fixture.named("engine")));
    assert!(!verified(compiled.manifest()).contains(&fixture.named("kernel-producer")));
    fs::write(fixture.path("kernel-producer"), b"changed").unwrap();
    let changed = fixture.invoke("Error", &KERNEL_FLAGS, "run-kernel-changed");
    assert!(!stages(changed.manifest()).contains(&"search".to_string()));
    fixture.section("kernel").remove("producer");
    fixture.save();
    let missing = fixture.invoke("Inappropriate", &KERNEL_FLAGS, "run-kernel-missing");
    assert!(stages(missing.manifest()).is_empty());
    assert!(text(missing.manifest(), &["reason"]).contains("pinned unnamed producer"));
}

#[test]
fn kernel_runs_with_the_same_run_name() {
    let mut fixture = Fixture::new();
    fixture.write_kernel("checked");
    let mut outs = Vec::new();
    for parent in ["first", "second"] {
        fs::create_dir(fixture.path(parent)).unwrap();
        let run = fixture.invoke("Unsatisfiable", &KERNEL_FLAGS, &format!("{parent}/run"));
        outs.push(PathBuf::from(text(
            run.manifest(),
            &["kernel_check", "out"],
        )));
    }
    assert_ne!(outs[0], outs[1]);
    assert!(
        outs.iter()
            .all(|out| out.parent() == Some(fixture.path("kernel-runs").as_path()))
    );
}

#[test]
fn kernel_non_results() {
    for (mode, expected) in [
        ("review-pending", "Error"),
        ("rejected", "Error"),
        ("timeout", "Timeout"),
        ("resource", "ResourceOut"),
        ("forced", "Error"),
        ("lying", "Error"),
    ] {
        let mut fixture = Fixture::new();
        fixture.write_kernel(mode);
        let run = fixture.invoke(expected, &KERNEL_FLAGS, &format!("run-kernel-{mode}"));
        assert!(
            at(run.manifest(), &["kernel_check"])
                .get("accepted")
                .is_none(),
            "{mode}"
        );
    }
}

#[test]
fn kernel_refuses_bundles_and_tstp() {
    let mut fixture = Fixture::new();
    fixture.write_kernel("checked");
    let mut arguments = KERNEL_FLAGS.to_vec();
    arguments.extend(["--output", "tstp"]);
    let run = fixture.invoke("Inappropriate", &arguments, "run-kernel-tstp");
    assert!(run.stdout().contains("not available with --check kernel"));
    fixture.write_bundle("candidate", "accept", false);
    let run = fixture.invoke("Inappropriate", &KERNEL_FLAGS, "run-kernel-bundle");
    assert!(run.stdout().contains("Kernel replay covers single-file"));
}

#[test]
fn help_states_default_and_trust() {
    let output = Command::new(launcher()).arg("--help").output().unwrap();
    assert_eq!(output.status.code(), Some(0));
    let text = String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert!(text.contains("default: compiled, which trusts the Lean compiler and runtime"));
    assert!(text.contains("the default check is compiled"));
    assert!(!text.contains("fang-internal"));
}

#[test]
fn tstp_rejected_before_search() {
    let fixture = Fixture::new();
    let run = fixture.invoke(
        "Inappropriate",
        &["--check", "compiled", "--output", "tstp"],
        "run",
    );
    assert!(run.stdout().contains("--output status"));
    assert!(run.lines[0].contains("single file"));
    assert_eq!(text(run.manifest(), &["path"]), "single");
    assert!(!fixture.path("run/search").exists());
}

#[test]
fn signed_theorem_needs_every_listed_goal() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "two-goals", false);
    let run = fixture.invoke("Theorem", &COMPILED, "run-theorem");
    let manifest = run.manifest();
    assert!(run.lines[0].contains("signed bundle"));
    assert_eq!(text(manifest, &["path"]), "signed");
    let listing = fang_json::dumps_manifest(at(manifest, &["signed", "listing"])).unwrap();
    assert_eq!(
        listing.split_whitespace().collect::<String>(),
        "[[0,1],[1,0]]"
    );
    assert_eq!(
        column(manifest, &["signed", "tasks"], "task"),
        ["goal-0", "goal-1"]
    );
    let files: Vec<(String, String)> = rows(manifest, &["signed", "files"])
        .iter()
        .map(|row| {
            (
                row.get("root").unwrap().as_str().unwrap().to_string(),
                row.get("path").unwrap().as_str().unwrap().to_string(),
            )
        })
        .collect();
    assert_eq!(
        files,
        [
            ("base".to_string(), "problem.p".to_string()),
            ("base".to_string(), "ax.ax".to_string()),
            ("base".to_string(), "sub/b.ax".to_string())
        ]
    );
    for (producer, checker, expected) in [
        ("unknown-goal-1", "two-goals", "GaveUp"),
        ("candidate", "wrong-item", "Error"),
        ("candidate", "unsupported", "Inappropriate"),
    ] {
        fixture.write_signed(producer, checker, false);
        fixture.invoke(expected, &COMPILED, &format!("run-{producer}-{checker}"));
    }
}

#[test]
fn signed_inputs_without_goals_is_unsatisfiable() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "no-goals", false);
    let run = fixture.invoke("Unsatisfiable", &COMPILED, "run-inputs");
    assert_eq!(
        column(run.manifest(), &["signed", "tasks"], "task"),
        ["inputs"]
    );
}

#[test]
fn signed_tstp_and_missing_capability() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "two-goals", false);
    let run = fixture.invoke(
        "Inappropriate",
        &["--check", "compiled", "--output", "tstp"],
        "run-tstp",
    );
    assert!(
        run.stdout()
            .contains("conjectures or other non-axiom roles")
    );
    assert!(
        run.stdout()
            .contains(signed::TSTP_UNAVAILABLE.split(';').next().unwrap())
    );
    fixture.config.set("signed", Value::Null);
    fixture.save();
    let run = fixture.invoke("Inappropriate", &COMPILED, "run-none");
    assert!(run.stdout().contains("not installed"));
}

#[test]
fn goal_tstp_document_after_every_goal_is_accepted() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "one-goal", true);
    fixture.write_goal_exporter("document");
    let run = fixture.tstp("run-goal-tstp");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.lines[0].contains("signed"));
    assert!(run.lines[2].starts_with("% SZS status Theorem for problem"));
    assert_eq!(run.lines[3], "% SZS output start CNFRefutation for problem");
    assert_eq!(
        run.lines[4],
        "fof(g0,negated_conjecture,~p,inference(negate,[status(cth)],[g]))."
    );
    assert_eq!(
        run.lines.last().unwrap(),
        "% SZS output end CNFRefutation for problem"
    );
    assert_eq!(run.stderr(), "");
    let manifest = run.manifest();
    assert_eq!(text(manifest, &["export", "state"]), "documents");
    let names = stages(manifest);
    let position = |name: &str| names.iter().position(|stage| stage == name).unwrap();
    assert!(position("check-goal-0") < position("export-goal-0"));
    assert!(verified(manifest).contains(&fixture.named("goal-exporter")));
}

#[test]
fn goal_tstp_one_document_per_conjecture() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "two-goals", true);
    fixture.write_goal_exporter("document");
    let run = fixture.tstp("run-goal-tstp-two");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.lines[2].starts_with("% SZS status Theorem for problem"));
    assert_eq!(
        run.lines[3..],
        [
            "% SZS output start CNFRefutation for problem",
            "fof(g0,negated_conjecture,~p,inference(negate,[status(cth)],[g])).",
            "% SZS output end CNFRefutation for problem",
            "% SZS output start CNFRefutation for problem",
            "fof(g1,negated_conjecture,~p,inference(negate,[status(cth)],[g])).",
            "% SZS output end CNFRefutation for problem",
        ]
    );
    let goals: Vec<i64> = rows(run.manifest(), &["export", "documents"])
        .iter()
        .map(|row| row.get("goal").unwrap().as_i64().unwrap())
        .collect();
    assert_eq!(goals, [0, 1]);
    let names = stages(run.manifest());
    let position = |name: &str| names.iter().position(|stage| stage == name).unwrap();
    assert!(position("check-goal-1") < position("export-goal-0"));
}

#[test]
fn goal_tstp_failure_or_scope_keeps_theorem() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "one-goal", true);
    fixture.write_goal_exporter("export-error");
    let run = fixture.tstp("run-goal-tstp-error");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.stdout().contains("% SZS status Theorem for problem"));
    assert!(!run.stdout().contains("SZS output start"));
    assert_eq!(run.stderr().lines().count(), 1);
    assert!(run.stderr().starts_with("fang: TSTP export failed"));
    assert_eq!(text(run.manifest(), &["export", "state"]), "failed");
    // Two goals over an include bundle: the status stands, no exporter runs, one line says why.
    fixture.write_signed("candidate", "two-goals", false);
    fixture.write_goal_exporter("document");
    let run = fixture.tstp("run-goal-tstp-scope");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.stdout().contains("% SZS status Theorem for problem"));
    assert!(!run.stdout().contains("SZS output start"));
    assert_eq!(run.stderr(), format!("fang: {SIGNED_TSTP_SCOPE}\n"));
    assert_eq!(text(run.manifest(), &["export", "state"]), "not-covered");
    assert!(
        !stages(run.manifest())
            .iter()
            .any(|stage| stage.starts_with("export"))
    );
}

#[test]
fn signed_single_file_with_distinct_objects_names_the_scope() {
    let mut fixture = Fixture::new();
    let input: &[u8] = b"fof(a,axiom,p(\"x\")). fof(g,conjecture,p(\"x\")).";
    fixture.write_signed_files("candidate", "one-goal", &[("problem.p", input)]);
    fixture.write_goal_exporter("document");
    let run = fixture.tstp("run-object-scope");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.stdout().contains("% SZS status Theorem for problem"));
    assert!(!run.stdout().contains("SZS output start"));
    assert_eq!(run.stderr(), format!("fang: {OBJECT_TSTP_SCOPE}\n"));
    assert_eq!(text(run.manifest(), &["export", "state"]), "not-covered");
}

#[test]
fn signed_inputs_task_document_needs_the_inputs_exporter() {
    let mut fixture = Fixture::new();
    fixture.write_signed("candidate", "no-goals", true);
    fixture.write_goal_exporter("document");
    let run = fixture.tstp("run-inputs-scope");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(
        run.stdout()
            .contains("% SZS status Unsatisfiable for problem")
    );
    assert!(!run.stdout().contains("SZS output start"));
    assert_eq!(run.stderr(), format!("fang: {SIGNED_TSTP_SCOPE}\n"));
    let exporter = fixture.script("inputs-exporter", INPUTS_EXPORTER, "document");
    fixture.section("tstp").set("inputs_exporter", exporter);
    fixture.save();
    let run = fixture.tstp("run-inputs-document");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert_eq!(
        run.lines[2..],
        [
            "% SZS status Unsatisfiable for problem",
            "% SZS output start CNFRefutation for problem",
            "fof(a,axiom,p,file('problem.p',a)).",
            "% SZS output end CNFRefutation for problem",
        ]
    );
    assert_eq!(run.stderr(), "");
    assert_eq!(text(run.manifest(), &["export", "state"]), "document");
    assert!(verified(run.manifest()).contains(&fixture.named("inputs-exporter")));
}

#[test]
fn tstp_capability_fields() {
    let mut fixture = Fixture::new();
    fixture.write_exporter("document");
    let exporter = at(&fixture.config, &["tstp", "exporter"]).clone();
    let with = |names: &[&str]| {
        let mut tstp = Object::new();
        for name in names {
            tstp.set(*name, exporter.clone());
        }
        let mut config = fixture.config.clone();
        config.set("tstp", Value::Object(tstp));
        capability::check_fields(&config)
    };
    for names in [
        &["exporter"][..],
        &["exporter", "bundle_exporter"],
        &["exporter", "goal_exporter"],
        &["exporter", "bundle_exporter", "goal_exporter"],
        &["exporter", "goal_exporter", "inputs_exporter"],
        &[
            "exporter",
            "bundle_exporter",
            "goal_exporter",
            "inputs_exporter",
        ],
    ] {
        assert!(with(names).is_ok(), "{names:?}");
    }
    for names in [
        &["goal_exporter"][..],
        &["exporter", "other"],
        &["inputs_exporter"],
    ] {
        assert!(with(names).is_err(), "{names:?}");
    }
}

#[test]
fn run_hashes_what_it_executes_and_self_check_hashes_everything() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("candidate", "accept", false);
    fixture.set_source(SOURCE);
    let mut text_now = fs::read_to_string(fixture.path("bundle-checker")).unwrap();
    text_now.push_str("# changed after installation\n");
    fs::write(fixture.path("bundle-checker"), text_now).unwrap();
    let run = fixture.invoke("Unsatisfiable", &COMPILED, "run-single");
    let hashed = verified(run.manifest());
    for name in ["engine", "checker"] {
        assert!(hashed.contains(&fixture.named(name)), "{name}");
    }
    assert!(hashed.contains(&launcher().display().to_string()));
    for name in ["bundle-checker", "receipt.json"] {
        assert!(!hashed.contains(&fixture.named(name)), "{name}");
    }
    let check = Command::new(launcher())
        .arg("--capability")
        .arg(&fixture.capability)
        .arg("--self-check")
        .output()
        .unwrap();
    assert_eq!(check.status.code(), Some(6));
    assert!(String::from_utf8_lossy(&check.stdout).contains("self-check failed"));
    fixture.set_source(b"include('ax.ax'). fof(a,axiom,\"x\" = \"y\").");
    let run = fixture.invoke("Error", &COMPILED, "run-bundle");
    assert!(text(run.manifest(), &["reason"]).contains("Pinned version-8 dependency changed"));
}

#[test]
fn self_check_passes_on_an_unchanged_installation() {
    let fixture = Fixture::new();
    let check = Command::new(launcher())
        .arg("--capability")
        .arg(&fixture.capability)
        .arg("--self-check")
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&check.stdout);
    assert_eq!(check.status.code(), Some(0), "{stdout}");
    assert!(stdout.contains("match the installation"));
}

#[test]
fn tstp_document_after_acceptance() {
    let mut fixture = Fixture::new();
    fixture.write_exporter("document");
    let run = fixture.finished(
        fixture.command(
            &fixture.input,
            "run",
            &["--check", "compiled", "--output", "tstp"],
        ),
        "run",
    );
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(
        run.lines[1].starts_with("% fang: checked by the compiled Lean checker (--check compiled")
    );
    assert!(run.lines[2].starts_with("% SZS status Unsatisfiable for problem"));
    assert_eq!(run.lines[3], "% SZS output start CNFRefutation for problem");
    assert_eq!(run.lines[4], "cnf(a,axiom,($false),file('problem.p',a)).");
    assert_eq!(
        run.lines.last().unwrap(),
        "% SZS output end CNFRefutation for problem"
    );
    assert_eq!(run.stderr(), "");
    assert_eq!(text(run.manifest(), &["export", "state"]), "document");
    assert_eq!(
        at(run.manifest(), &["output_delivery", "document"]).as_bool(),
        Some(true)
    );
    let names = stages(run.manifest());
    assert_eq!(names, ["search", "checker", "export"]);
}

#[test]
fn tstp_failure_keeps_unsatisfiable_without_document() {
    for (mode, extra) in [
        ("export-error", &[][..]),
        ("bad", &[]),
        ("slow", &["--wall-seconds", "3"]),
    ] {
        let mut fixture = Fixture::new();
        fixture.write_exporter(mode);
        let mut arguments = vec!["--check", "compiled", "--output", "tstp"];
        arguments.extend(extra);
        let run = fixture.finished(fixture.command(&fixture.input, "run", &arguments), "run");
        assert_eq!(
            run.output.status.code(),
            Some(0),
            "{mode}: {}",
            run.stderr()
        );
        assert!(
            run.stdout()
                .contains("% SZS status Unsatisfiable for problem")
        );
        assert!(!run.stdout().contains("SZS output start"));
        assert_eq!(run.stderr().lines().count(), 1, "{mode}: {}", run.stderr());
        assert!(
            run.stderr().starts_with("fang: TSTP export"),
            "{mode}: {}",
            run.stderr()
        );
    }
}

#[test]
fn statement_limit_is_named_when_the_export_fails() {
    let mut fixture = Fixture::new();
    let mut input = Vec::new();
    for index in 0..1001 {
        input.extend_from_slice(format!("cnf(a{index},axiom,($false)).\n").as_bytes());
    }
    fixture.set_source(&input);
    fixture.write_exporter("export-error");
    let run = fixture.tstp("run");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(
        run.stdout()
            .contains("% SZS status Unsatisfiable for problem")
    );
    assert_eq!(run.stderr(), format!("fang: {STATEMENT_LIMIT_NOTE}\n"));
}

#[test]
fn tstp_not_run_without_acceptance() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("candidate", "logical");
    fixture.write_exporter("document");
    let run = fixture.invoke(
        "Error",
        &["--check", "compiled", "--output", "tstp"],
        "run-rejected",
    );
    assert!(run.manifest().get("export").is_none());
    assert!(!fixture.path("run-rejected/export").exists());
}

#[test]
fn bundle_path_passes_every_file_it_hashed() {
    let mut fixture = Fixture::new();
    let contents = fixture.write_bundle("candidate", "accept", true);
    let tptp = fixture.named("tptp");
    let run = fixture.invoke(
        "Unsatisfiable",
        &["--check", "compiled", "--tptp-root", &tptp],
        "run",
    );
    let manifest = run.manifest();
    assert!(run.lines[0].contains("bundle"));
    assert_eq!(text(manifest, &["path"]), "bundle");
    let files = rows(manifest, &["bundle", "files"]);
    let names: Vec<String> = files
        .iter()
        .map(|row| {
            format!(
                "{} {}",
                row.get("root").unwrap().as_str().unwrap(),
                row.get("path").unwrap().as_str().unwrap()
            )
        })
        .collect();
    assert_eq!(names, ["base problem.p", "base ax.ax", "tptp Axioms/eq.ax"]);
    let hashes: Vec<&str> = files
        .iter()
        .map(|row| row.get("sha256").unwrap().as_str().unwrap())
        .collect();
    let expected: Vec<String> = contents
        .iter()
        .map(|data| fang_hash::sha256_hex(data))
        .collect();
    assert_eq!(hashes, expected);
    assert_eq!(text(manifest, &["compiled_check", "checker"]), "bundle");
}

#[test]
fn bundle_outcomes() {
    for (producer, checker, expected) in [
        ("missing", "accept", "InputError"),
        ("limit", "accept", "ResourceOut"),
        ("candidate", "reject", "Error"),
    ] {
        let mut fixture = Fixture::new();
        fixture.write_bundle(producer, checker, false);
        fixture.invoke(expected, &COMPILED, &format!("run-{producer}-{checker}"));
    }
}

#[test]
fn bundle_tstp_and_missing_bundle_capability() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("candidate", "accept", false);
    let run = fixture.invoke(
        "Inappropriate",
        &["--check", "compiled", "--output", "tstp"],
        "run-tstp",
    );
    assert!(
        run.stdout()
            .contains("bundle exporter, which is not installed")
    );
    fixture.config.set("bundle", Value::Null);
    fixture.save();
    let run = fixture.invoke("Inappropriate", &COMPILED, "run-none");
    assert!(run.stdout().contains("not installed"));
    assert!(!fixture.path("run-none/search").exists());
}

#[test]
fn bundle_tstp_document_after_acceptance() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("candidate", "accept", false);
    fixture.write_bundle_exporter("document");
    let run = fixture.tstp("run-bundle-tstp");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(run.lines[0].contains("bundle"));
    assert!(run.lines[2].starts_with("% SZS status Unsatisfiable for problem"));
    assert_eq!(run.lines[3], "% SZS output start CNFRefutation for problem");
    assert_eq!(run.lines[4], "fof(b,axiom,$false,file('ax.ax',b)).");
    assert_eq!(
        run.lines.last().unwrap(),
        "% SZS output end CNFRefutation for problem"
    );
    assert_eq!(run.stderr(), "");
    assert_eq!(text(run.manifest(), &["export", "state"]), "document");
    assert_eq!(stages(run.manifest()), ["search", "checker", "export"]);
    assert!(verified(run.manifest()).contains(&fixture.named("bundle-exporter")));
}

#[test]
fn bundle_tstp_failure_keeps_unsatisfiable() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("candidate", "accept", false);
    fixture.write_bundle_exporter("export-error");
    let run = fixture.tstp("run-bundle-tstp-error");
    assert_eq!(run.output.status.code(), Some(0), "{}", run.stderr());
    assert!(
        run.stdout()
            .contains("% SZS status Unsatisfiable for problem")
    );
    assert!(!run.stdout().contains("SZS output start"));
    assert_eq!(run.stderr().lines().count(), 1);
    assert!(run.stderr().starts_with("fang: TSTP export"));
    assert_eq!(text(run.manifest(), &["export", "state"]), "failed");
}

#[test]
fn bundle_tstp_not_run_without_acceptance() {
    let mut fixture = Fixture::new();
    fixture.write_bundle("candidate", "reject", false);
    fixture.write_bundle_exporter("document");
    let run = fixture.tstp("run-bundle-tstp-rejected");
    assert_eq!(run.output.status.code(), Some(6));
    assert!(run.manifest().get("export").is_none());
    assert!(!fixture.path("run-bundle-tstp-rejected/export").exists());
}

#[test]
fn changed_engine_pin_is_an_error() {
    let fixture = Fixture::new();
    let mut engine = fs::read_to_string(fixture.path("engine")).unwrap();
    engine.push_str("# changed\n");
    fs::write(fixture.path("engine"), engine).unwrap();
    let run = fixture.invoke("Error", &COMPILED, "run");
    assert!(run.manifest().get("producer_outcome").is_none());
    assert!(!fixture.path("run/search").exists());
}

#[test]
fn unknown_capability_section_is_refused() {
    let mut fixture = Fixture::new();
    let mut future = Object::new();
    future.set("profile", "future");
    fixture.config.set("kernel", Value::Object(future));
    fixture.save();
    fixture.invoke("Error", &COMPILED, "run");
}

#[test]
fn input_limit() {
    let fixture = Fixture::new();
    fixture.invoke(
        "ResourceOut",
        &["--check", "compiled", "--max-input-bytes", "4"],
        "run",
    );
}

#[test]
fn existing_artifacts_directory_untouched() {
    let fixture = Fixture::new();
    fs::create_dir(fixture.path("run")).unwrap();
    fs::write(fixture.path("run/sentinel"), b"keep").unwrap();
    fixture.invoke("Error", &COMPILED, "run");
    let names: Vec<String> = fs::read_dir(fixture.path("run"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    assert_eq!(names, ["sentinel"]);
}

#[test]
fn invalid_arguments_are_an_error_with_the_status_line() {
    let fixture = Fixture::new();
    let run = fixture.finished(
        fixture.command(&fixture.input, "run", &["--check", "sometimes"]),
        "run",
    );
    assert_eq!(
        run.lines.last().map(String::as_str),
        Some("% SZS status Error for fang_unavailable")
    );
    assert_eq!(run.output.status.code(), Some(6));
    assert!(run.manifest.is_none());
    assert!(!fixture.path("run").exists());
}

#[test]
fn termination_of_the_caller_is_forced_and_recorded() {
    let mut fixture = Fixture::new();
    fixture.write_binaries("slow", "accept");
    let child = Command::new(launcher())
        .arg(&fixture.input)
        .arg("--capability")
        .arg(&fixture.capability)
        .arg("--artifacts")
        .arg(fixture.path("run"))
        .args(COMPILED)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while !fixture.path("run/search").exists() {
        assert!(
            started.elapsed() < Duration::from_secs(20),
            "the search never started"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let killed = Command::new("kill")
        .arg("-TERM")
        .arg(child.id().to_string())
        .status()
        .unwrap();
    assert!(killed.success());
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.code(), None);
    let path = fixture.path("run/manifest.json");
    let deadline = Instant::now() + Duration::from_secs(10);
    let manifest = loop {
        let value = fs::read(&path)
            .ok()
            .and_then(|bytes| fang_json::parse(&bytes, &ParseLimits::default()).ok());
        if let Some(Value::Object(manifest)) = value
            && manifest.get("status").and_then(Value::as_str) == Some("Forced")
        {
            break manifest;
        }
        assert!(Instant::now() < deadline, "no Forced record");
        std::thread::sleep(Duration::from_millis(50));
    };
    assert_eq!(text(&manifest, &["reason"]), "External cancellation");
    assert_eq!(text(&manifest, &["state"]), "finished");
    // The record is the one published before the search started: routing, input and hashed files included.
    assert_eq!(text(&manifest, &["path"]), "single");
    assert!(manifest.get("input").is_some());
    assert!(verified(&manifest).contains(&fixture.named("engine")));
    assert!(stages(&manifest).is_empty());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.ends_with("% SZS status Forced for problem\n"),
        "{stdout}"
    );
}
