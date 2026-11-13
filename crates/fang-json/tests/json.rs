// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Controls for the reader and the writer. The expected texts are Python 3's; the equivalence
//! runs compare both directions against Python itself on the archived records.
use fang_json::{
    DumpOptions, ErrorKind, Integer, Number, Object, ParseLimits, Value, dumps, dumps_manifest,
    parse, python_float_repr, write_json,
};

fn read(text: &str) -> Result<Value, fang_json::JsonError> {
    parse(text.as_bytes(), &ParseLimits::default())
}

fn message(text: &str) -> String {
    read(text).unwrap_err().python_message(text.as_bytes())
}

#[test]
fn integers_stay_exact_and_apart_from_floats() {
    assert_eq!(
        read("1").unwrap(),
        Value::Number(Number::Integer(Integer::from(1u8)))
    );
    assert_eq!(read("1.0").unwrap(), Value::Number(Number::Float(1.0)));
    assert_eq!(read("1e0").unwrap(), Value::Number(Number::Float(1.0)));
    assert_eq!(read("-0").unwrap().as_i64(), Some(0));
    assert!(!read("-0").unwrap().as_integer().unwrap().is_negative());
    let maximum = u128::MAX.to_string();
    assert_eq!(
        read(&maximum).unwrap().as_integer().unwrap().as_u128(),
        Some(u128::MAX)
    );
    let minimum = format!("-{}", u128::MAX);
    assert_eq!(
        read(&minimum).unwrap().as_integer().unwrap().magnitude(),
        u128::MAX
    );
    assert_eq!(
        read("340282366920938463463374607431768211456")
            .unwrap_err()
            .kind,
        ErrorKind::IntegerOutOfRange
    );
    assert_eq!(
        read("-9223372036854775808").unwrap().as_i64(),
        Some(i64::MIN)
    );
    assert_eq!(read("9223372036854775808").unwrap().as_i64(), None);
    assert_eq!(read("1e400").unwrap_err().kind, ErrorKind::FloatOutOfRange);
    assert_eq!(read("1e-400").unwrap(), Value::Number(Number::Float(0.0)));
}

#[test]
fn nonfinite_and_duplicates_carry_python_texts() {
    for text in ["NaN", "Infinity", "-Infinity", "[1, NaN]"] {
        assert_eq!(message(text), "Nonfinite JSON number");
    }
    for text in [r#"{"a": 1, "a": 2}"#, r#"[{"x": {"a": 1, "a": 2}}]"#] {
        assert_eq!(message(text), "Duplicate JSON field");
    }
    // The duplicate is reported when its object closes, so an earlier syntax error wins, as in Python.
    assert_eq!(
        message(r#"{"a":1,"a":2"#),
        "Expecting ',' delimiter: line 1 column 13 (char 12)"
    );
}

#[test]
fn syntax_errors_carry_python_texts() {
    let cases = [
        ("", "Expecting value: line 1 column 1 (char 0)"),
        ("  \n ", "Expecting value: line 2 column 2 (char 4)"),
        (
            "[1,]",
            "Illegal trailing comma before end of array: line 1 column 3 (char 2)",
        ),
        (
            r#"{"a": 1,}"#,
            "Illegal trailing comma before end of object: line 1 column 8 (char 7)",
        ),
        (
            r#"{"a" 1}"#,
            "Expecting ':' delimiter: line 1 column 6 (char 5)",
        ),
        (
            "{1: 2}",
            "Expecting property name enclosed in double quotes: line 1 column 2 (char 1)",
        ),
        ("[1 2]", "Expecting ',' delimiter: line 1 column 4 (char 3)"),
        ("1 2", "Extra data: line 1 column 3 (char 2)"),
        ("01", "Extra data: line 1 column 2 (char 1)"),
        ("-", "Expecting value: line 1 column 1 (char 0)"),
        (
            r#""abc"#,
            "Unterminated string starting at: line 1 column 1 (char 0)",
        ),
        (
            "\"a\u{1}b\"",
            "Invalid control character at: line 1 column 3 (char 2)",
        ),
        (r#""\x""#, "Invalid \\escape: line 1 column 2 (char 1)"),
        (
            r#""\u12G4""#,
            "Invalid \\uXXXX escape: line 1 column 3 (char 2)",
        ),
        ("\"é\" x", "Extra data: line 1 column 5 (char 4)"),
    ];
    for (text, expected) in cases {
        assert_eq!(message(text), expected, "input {text:?}");
    }
}

#[test]
fn strings_decode_every_escape_and_refuse_lone_surrogates() {
    let value = read(r#""\" \\ \/ \b \f \n \r \t \u00e9 \ud83d\ude00""#).unwrap();
    assert_eq!(value.as_str().unwrap(), "\" \\ / \u{8} \u{c} \n \r \t é 😀");
    assert_eq!(
        read(r#""\ud83d""#).unwrap_err().kind,
        ErrorKind::LoneSurrogate
    );
    assert_eq!(
        read(r#""\ude00x""#).unwrap_err().kind,
        ErrorKind::LoneSurrogate
    );
    assert_eq!(
        read(r#""\ud83d\u0041""#).unwrap_err().kind,
        ErrorKind::LoneSurrogate
    );
}

#[test]
fn limits_are_refusals_never_crashes() {
    let tight = ParseLimits {
        max_bytes: 10,
        max_depth: 3,
    };
    assert_eq!(parse(b"[[[1]]]", &tight).unwrap(), read("[[[1]]]").unwrap());
    assert_eq!(
        parse(b"[[[[1]]]]", &tight).unwrap_err().kind,
        ErrorKind::TooDeep
    );
    assert_eq!(
        parse(b"[1,2,3,4,5,6]", &tight).unwrap_err().kind,
        ErrorKind::TooLarge
    );
    let deep = "[".repeat(1_000_000);
    assert_eq!(read(&deep).unwrap_err().kind, ErrorKind::TooDeep);
    let wide = ParseLimits {
        max_bytes: 4 << 20,
        max_depth: 2_000_000,
    };
    assert_eq!(
        parse(deep.as_bytes(), &wide).unwrap_err().kind,
        ErrorKind::ExpectingValue
    );
    assert_eq!(
        parse(b"\xff", &tight).unwrap_err().kind,
        ErrorKind::InvalidUtf8
    );
    assert_eq!(
        read("\u{feff}{}").unwrap_err().kind,
        ErrorKind::UnexpectedBom
    );
}

#[test]
fn objects_keep_document_order_and_compare_as_dicts() {
    let value = read(r#"{"b": 1, "a": {"y": 2, "x": 3}}"#).unwrap();
    let keys: Vec<&str> = value.as_object().unwrap().keys().collect();
    assert_eq!(keys, ["b", "a"]);
    assert_eq!(value, read(r#"{"a": {"x": 3, "y": 2}, "b": 1}"#).unwrap());
    assert!(
        !value.as_object().unwrap().ordered_eq(
            read(r#"{"a": {"x": 3, "y": 2}, "b": 1}"#)
                .unwrap()
                .as_object()
                .unwrap()
        )
    );
    let mut object = Object::new();
    object.set("z", 1u8);
    object.set("a", 2u8);
    object.set("z", 3u8);
    assert_eq!(object.keys().collect::<Vec<_>>(), ["z", "a"]);
    assert_eq!(object.remove("z").unwrap().as_i64(), Some(3));
    assert_eq!(object.get("a").unwrap().as_i64(), Some(2));
}

#[test]
fn floats_print_as_python_repr() {
    let cases: [(f64, &str); 17] = [
        (60.0, "60.0"),
        (0.02, "0.02"),
        (0.1, "0.1"),
        (1e-5, "1e-05"),
        (0.0001, "0.0001"),
        (1e16, "1e+16"),
        (1e15, "1000000000000000.0"),
        (9999999999999998.0, "9999999999999998.0"),
        (12345678901234567.0, "1.2345678901234568e+16"),
        (1.5e300, "1.5e+300"),
        (5e-324, "5e-324"),
        (-2.5, "-2.5"),
        (-0.0, "-0.0"),
        (0.0, "0.0"),
        (123.456, "123.456"),
        (1.7976931348623157e308, "1.7976931348623157e+308"),
        (2.2250738585072014e-308, "2.2250738585072014e-308"),
    ];
    for (value, expected) in cases {
        assert_eq!(python_float_repr(value).unwrap(), expected);
    }
    assert_eq!(python_float_repr(f64::NAN), None);
    // Exactly halfway between two shortest strings: Python takes the even last digit.
    for (bits, expected) in [
        (0x4269a3af3fe16900u64, "880962830091.2812"),
        (0x42a063fb362ee220, "9010801219441.062"),
        (0x42d11390f0e8f248, "75102935032777.12"),
    ] {
        assert_eq!(python_float_repr(f64::from_bits(bits)).unwrap(), expected);
    }
}

#[test]
fn manifest_writer_matches_python_dumps() {
    let value = read(r#"{"b": [1, 2.5, {"z": null, "a": true}], "a": {}, "c": [], "é": "ö\u0007\ud83d\ude00/\u007f"}"#)
        .unwrap();
    let expected = concat!(
        "{\n",
        "  \"a\": {},\n",
        "  \"b\": [\n",
        "    1,\n",
        "    2.5,\n",
        "    {\n",
        "      \"a\": true,\n",
        "      \"z\": null\n",
        "    }\n",
        "  ],\n",
        "  \"c\": [],\n",
        "  \"\\u00e9\": \"\\u00f6\\u0007\\ud83d\\ude00/\\u007f\"\n",
        "}"
    );
    assert_eq!(dumps_manifest(&value).unwrap(), expected);
    let compact = dumps(
        &value,
        &DumpOptions {
            indent: None,
            sort_keys: false,
        },
    )
    .unwrap();
    assert_eq!(
        compact,
        "{\"b\": [1, 2.5, {\"z\": null, \"a\": true}], \"a\": {}, \"c\": [], \"\\u00e9\": \"\\u00f6\\u0007\\ud83d\\ude00/\\u007f\"}"
    );
    assert_eq!(
        dumps(&Value::from(f64::INFINITY), &DumpOptions::default())
            .unwrap_err()
            .0,
        "Out of range float values are not JSON compliant: inf"
    );
}

#[test]
fn write_json_writes_through_a_new_file_and_renames() {
    let directory = std::env::temp_dir().join(format!("fang-json-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("manifest.json");
    let value: Value = [
        ("status", Value::from("passed")),
        ("seconds", Value::from(1.0)),
    ]
    .into_iter()
    .collect::<Object>()
    .into();
    write_json(&path, &value).unwrap();
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "{\n  \"seconds\": 1.0,\n  \"status\": \"passed\"\n}\n"
    );
    assert!(!directory.join("manifest.json.new").exists());
    std::fs::write(directory.join("manifest.json.new"), b"x").unwrap();
    assert!(write_json(&path, &value).is_err());
}
