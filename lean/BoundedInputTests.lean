/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Compiled native-I/O regressions; these tests are not kernel proofs of file loading.
-/
import Fang.BoundedInput

open Fang.Runtime

private def ensure (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"bounded-input test failed: {label}")

private def expectAscii (path : String) (limit : Nat) (expected : String) : IO Unit := do
  match ← readAscii path limit with
  | .error error => throw (IO.userError s!"unexpected readAscii rejection: {error}")
  | .ok text => ensure path (text == expected)

private def expectError (path : String) (limit : Nat) (expectedPrefix : String) : IO Unit := do
  match ← readAscii path limit with
  | .error error => ensure path (error.startsWith expectedPrefix)
  | .ok _ => throw (IO.userError s!"unexpected readAscii acceptance: {path}")

def main (args : List String) : IO UInt32 := do
  let [directory] := args | throw (IO.userError "expected one fixture directory")
  let path := directory ++ "/pattern.bin"
  let data ← IO.FS.readBinFile path
  ensure "fixture length" (data.size == 131079)
  for allowance in [0, 1, 65535, 65536, 65537, 131078, 131079, 131080] do
    IO.FS.withFile path .read fun handle => do
      let observed ← readAtMost handle allowance
      let consumed := min allowance data.size
      ensure s!"readAtMost length {allowance}" (observed.size == consumed)
      ensure s!"readAtMost prefix {allowance}" (observed == data.extract 0 consumed)
      let next ← handle.read 3
      ensure s!"handle consumption {allowance}" (next == data.extract consumed (consumed + 3))
  IO.FS.withFile path .read fun handle => do
    let initial := "prefix:".toUTF8
    let zero ← readAtMost handle 0 initial
    ensure "zero allowance preserves accumulated bytes" (zero == initial)
    let one ← readAtMost handle 1 initial
    ensure "one allowance appends one byte" (one == initial ++ data.extract 0 1)
    let next ← handle.read 1
    ensure "accumulator does not change handle allowance" (next == data.extract 1 2)
  expectAscii (directory ++ "/empty.bin") 0 ""
  expectAscii (directory ++ "/ascii.bin") 4 "abcd"
  expectAscii (directory ++ "/ascii.bin") 5 "abcd"
  expectError (directory ++ "/ascii.bin") 0 "resource-exhaustion:"
  expectError (directory ++ "/ascii.bin") 3 "resource-exhaustion:"
  expectError (directory ++ "/utf8.bin") 2 "unsupported at byte 0:"
  expectError (directory ++ "/invalid-utf8.bin") 2 "unsupported at byte 0:"
  expectError (directory ++ "/nonascii-after-chunk.bin") 65537 "unsupported at byte 65536:"
  expectError (directory ++ "/nonascii-after-chunk.bin") 65536 "resource-exhaustion:"
  IO.println "passed bounded-input native-I/O regressions: 8 allowance/consumption cases, accumulator case, 9 ASCII/classification cases"
  return 0
