import Fang.CertificateInput

/- Copyright (c) 2026 Pietro Pellegrino. Released under the BSD 3-Clause license. -/

namespace Fang.Replay

mutual
  def termSource : Term → String
    | .var id => s!"(.var {id})"
    | .app id args => s!"(.app {id} [{String.intercalate ", " (termsSource args)}])"

  def termsSource : List Term → List String
    | [] => []
    | first :: rest => termSource first :: termsSource rest
end

def clauseSource (clause : Clause) : String :=
  "[" ++ String.intercalate ", " (clause.map fun literal =>
    "{ positive := " ++ toString literal.positive ++ ", atom := { pred := " ++
    toString literal.atom.pred ++ ", args := [" ++
    String.intercalate ", " (termsSource literal.atom.args) ++ "] } }") ++ "]"

def substSource (subst : Subst) : String :=
  "[" ++ String.intercalate ", "
    (subst.map fun (id, term) => s!"({id}, {termSource term})") ++ "]"

def stepSource : Step → String
  | .input index => s!".input {index}"
  | .factor parent first second subst claimed =>
    s!".factor {parent} {first} {second} {substSource subst} {clauseSource claimed}"
  | .resolve left leftPos right rightPos subst claimed =>
    s!".resolve {left} {leftPos} {right} {rightPos} {substSource subst} {clauseSource claimed}"

def source (input proof : String) (problem : Problem) (certificate : Certificate) : String :=
  "/-\nCopyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n" ++
  "The kernel checks exact decoder computations and checker acceptance, then\n" ++
  "applies general source soundness to the original input byte value.\n" ++
  "The compiled exporter is untrusted. Source acceptance completeness is separate.\n-/\n" ++
  "import Fang.CertificateInput\nimport Fang.FrontendSoundness\n" ++
  "import Lean.Elab.Tactic.Cbv\n\nnamespace Fang.InstanceReplay\n\n" ++
  "set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n" ++
  "set_option cbv.maxSteps 10000000\n\n" ++
  "def originalInput : String := " ++ reprStr input ++ "\n\n" ++
  "def originalCertificate : String := " ++ reprStr proof ++ "\n\n" ++
  "def problem : Problem := [\n  " ++
  String.intercalate ",\n  " (problem.map clauseSource) ++ "\n]\n\n" ++
  "def certificate : Certificate := Certificate.mk [\n  " ++
  String.intercalate ",\n  " (certificate.steps.map stepSource) ++
  s!"\n] {certificate.final}\n\n" ++
  "theorem source_decodes : decodeProblem originalInput = .ok problem := by cbv\n\n" ++
  "theorem certificate_decodes : decodeCertificate originalCertificate = .ok certificate := by cbv\n\n" ++
  "theorem accepted : check (preprocess problem) certificate = true := by decide +kernel\n\n" ++
  "theorem parsed_ast_unsat : ¬ Satisfiable problem :=\n" ++
  "  check_preprocessed_sound problem certificate accepted\n\n" ++
  "theorem original_input_unsat : ¬ Source.Grammar.BytesSatisfiable\n" ++
  "    (Source.Grammar.spelling originalInput) :=\n" ++
  "  decoded_refutation_unsat source_decodes certificate accepted\n\n" ++
  "#print axioms source_decodes\n#print axioms certificate_decodes\n" ++
  "#print axioms accepted\n#print axioms parsed_ast_unsat\n" ++
  "#print axioms original_input_unsat\n\nend Fang.InstanceReplay\n"

end Fang.Replay
