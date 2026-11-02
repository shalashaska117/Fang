/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.FofCertificateInput
import Fang.FOF.FOFByteSemantics
import Fang.FOF.FOFDiagnostics

namespace Fang.FOFVersioned

def signature (decoded : FOFFrontend.Decoded) : DecodedProblem := {
  problem := GroundFOF.lowerDeclarations decoded.declarations
  functionArities := decoded.state.functions.map (fun symbol => symbol.arity.getD 0)
  predicateArities := decoded.state.predicates.map (fun symbol => symbol.arity.getD 0)
}

def accepts (input proof : String) : Except String Bool := do
  let decoded ← match FOFFrontend.decodeWithDiagnostics input with
    | .ok decoded => .ok decoded
    | .error error => .error s!"input: {reprStr error}"
  let certificate ← decodeCertificate proof
  if !certificateWellFormed (signature decoded) certificate then
    .error "invalid-certificate: symbol or arity"
  else pure (check (GroundFOF.prepareDeclarations decoded.declarations) certificate)

theorem accepts_original_unsat {input proof}
    (accepted : accepts input proof = .ok true) :
    ¬ FOFGrammar.BytesSatisfiable (Source.Grammar.spelling input) := by
  unfold accepts at accepted
  cases decodedEq : FOFFrontend.decodeWithDiagnostics input with
  | error error => simp [decodedEq, bind, Except.bind] at accepted
  | ok decoded =>
    simp only [decodedEq, bind, Except.bind] at accepted
    cases certificateEq : decodeCertificate proof with
    | error error => simp [certificateEq] at accepted
    | ok certificate =>
      simp only [certificateEq] at accepted
      split at accepted
      · contradiction
      · have checked : check (GroundFOF.prepareDeclarations decoded.declarations) certificate = true :=
          Except.ok.inj accepted
        exact FOFFrontend.decode_check_original_unsat
          ((FOFFrontend.decodeWithDiagnostics_success input decoded).mp decodedEq) certificate checked

end Fang.FOFVersioned
