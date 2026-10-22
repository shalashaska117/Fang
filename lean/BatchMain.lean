import Fang.Replay
import Lean.Data.Json

/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/

open Lean

private def problemSource (problem : Fang.Problem) : String :=
  "[" ++ String.intercalate ", " (problem.map Fang.Replay.clauseSource) ++ "]"

private def response (line : String) : Except String Json := do
  let request ← Json.parse line
  let id ← request.getObjValAs? String "id"
  let operation := (request.getObjValAs? String "operation").toOption.getD "certificate"
  let input ← request.getObjValAs? String "input"
  let base := [("id", toJson id)]
  match Fang.decodeProblemWithSignature input with
  | .error reason => pure (Json.mkObj (base ++ [
      ("status", toJson "invalid-source"), ("reason", toJson reason)]))
  | .ok source =>
    if operation == "parse" || operation == "dedup" then
      pure (Json.mkObj (base ++ [
        ("status", toJson "parsed"),
        ("problem", toJson (problemSource source.problem)),
        ("normalized", toJson (problemSource (Fang.preprocess source.problem))),
        ("function_arities", toJson source.functionArities),
        ("predicate_arities", toJson source.predicateArities)]))
    else if operation == "certificate" || operation == "derivation" then
      let proof ← request.getObjValAs? String "certificate"
      match Fang.decodeCertificate proof with
      | .error reason => pure (Json.mkObj (base ++ [
          ("status", toJson "invalid-certificate"), ("reason", toJson reason)]))
      | .ok certificate =>
        if !Fang.certificateWellFormed source certificate then
          pure (Json.mkObj (base ++ [("status", toJson "invalid-certificate"),
            ("reason", toJson "unknown symbol or inconsistent arity")]))
        else
          let problem := Fang.preprocess source.problem
          let (accepted, success) := if operation == "derivation" then
              ((Fang.checkSteps problem [] certificate.steps).isSome, "accepted-derivation")
            else (Fang.check problem certificate, "accepted-refutation")
          pure (Json.mkObj (base ++ [("status", toJson
            (if accepted then success else "rejected-certificate"))]))
    else throw "unsupported batch operation"

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match args with
  | [inputPath, outputPath] =>
    try
      let input ← IO.FS.readFile inputPath
      if input.utf8ByteSize > 512 * 1024 * 1024 then
        stderr.putStrLn "resource-exhaustion: batch input exceeds 512 MiB"
        return 2
      IO.FS.withFile outputPath .write fun output => do
        for line in input.splitOn "\n" do
          if !line.isEmpty then
            let result := if line.utf8ByteSize > 1024 * 1024 then
                Except.error "resource-exhaustion: batch row exceeds 1 MiB"
              else response line
            let value := match result with
              | .ok value => value
              | .error reason => Json.mkObj [
                  ("status", toJson "invalid-request"), ("reason", toJson reason)]
            output.putStrLn value.compress
      return 0
    catch error =>
      stderr.putStrLn s!"batch-io-error: {error}"
      return 3
  | _ =>
    stderr.putStrLn "usage: fang-check-batch REQUESTS.jsonl RESULTS.jsonl"
    return 2
