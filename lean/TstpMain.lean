import TstpExport
import Fang.BoundedInput

/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match arguments with
  | [inputPath, proofPath, fileLabel] =>
    try
      let input ← Fang.Runtime.readAscii inputPath (1024 * 1024)
      let proof ← Fang.Runtime.readAscii proofPath (1024 * 1024)
      let result := do
        Fang.TstpExport.exportText (← input) (← proof) fileLabel
      match result with
      | .error error => stderr.putStrLn error; return 2
      | .ok text => IO.print text; return 0
    catch error => stderr.putStrLn s!"export-io-error: {error}"; return 3
  | _ =>
    stderr.putStrLn "usage: fang-tstp-export INPUT CERTIFICATE SOURCE_LABEL"
    return 2
