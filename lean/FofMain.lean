/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.VersionedCheck
import Fang.BoundedInput

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let [inputPath, proofPath] := args | do
    stderr.putStrLn "usage: fof-versioned-check INPUT CERTIFICATE"
    return 2
  try
    let input ← Fang.Runtime.readAscii inputPath (1024 * 1024)
    let proof ← Fang.Runtime.readAscii proofPath (1024 * 1024)
    let result := do Fang.FOFVersioned.accepts (← input) (← proof)
    match result with
    | .error error => stderr.putStrLn error; return 2
    | .ok false => stderr.putStrLn "rejected-certificate"; return 1
    | .ok true =>
      IO.println "accepted-original-ground-fof (compiled checker; compiler/runtime trusted)"
      return 0
  catch error =>
    stderr.putStrLn s!"checker-io-error: {error}"
    return 3
