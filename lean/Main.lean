import Fang.Input
import Fang.CertificateInput
import Fang.Replay
import Fang.BoundedInput

/- Copyright (c) 2026 Pietro Pellegrino. Released under the BSD 3-Clause license. -/

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let parsedArgs := match args with
    | [inputPath, certificatePath] => some (false, inputPath, certificatePath)
    | ["--emit-replay", inputPath, certificatePath] => some (true, inputPath, certificatePath)
    | _ => none
  match parsedArgs with
  | some (emitReplay, inputPath, certificatePath) =>
    try
      let input ← Fang.Runtime.readAscii inputPath (10 * 1024 * 1024)
      if let .error error := input then
        stderr.putStrLn error
        return 2
      let proof ← Fang.Runtime.readAscii certificatePath (64 * 1024 * 1024)
      let result : Except String (String × String × Fang.DecodedProblem × Fang.Certificate) := do
        let input ← input
        let proof ← proof
        let signature ← Fang.decodeProblemWithSignature input
        let certificate ← Fang.decodeCertificate proof
        if !Fang.certificateWellFormed signature certificate then
          throw "invalid-certificate: unknown symbol or inconsistent arity"
        pure (input, proof, signature, certificate)
      match result with
      | .error error => stderr.putStrLn error; return 2
      | .ok (input, proof, signature, certificate) =>
        if !Fang.check (Fang.preprocess signature.problem) certificate then
          stderr.putStrLn "rejected-certificate"
          return 1
        if emitReplay then
          IO.print (Fang.Replay.source input proof signature.problem certificate)
        else
          IO.println "accepted-refutation (compiled checker; no per-instance kernel replay performed)"
        return 0
    catch error =>
      stderr.putStrLn s!"checker-io-error: {error}"
      return 3
  | _ =>
    stderr.putStrLn "usage: fang-check [--emit-replay] INPUT CERTIFICATE"
    return 2
