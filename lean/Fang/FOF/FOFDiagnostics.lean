/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.FOFInput

namespace Fang.FOFFrontend

set_option maxHeartbeats 2000000

inductive InputError where
  | invalid : String → InputError
  | unsupported : String → InputError
  | resource : String → InputError
  deriving Repr, DecidableEq

/- The inherited CNF decoder uses an unsupported-term message for delimiters in
   argument position. Those tokens are known syntax in the supported language;
   their occurrence where a term/predicate is required is malformed input. Keep
   the complete original message, including its byte offset, in the typed error. -/
def malformedStructuralDiagnostic (message : String) : Bool :=
  ["(", ")", ",", ".", "|", "~", "&", "=>"].any fun token =>
    message.startsWith s!"unsupported: expected an uninterpreted term, found '{token}'" ||
    message.startsWith s!"unsupported: expected a predicate, found '{token}'"

def classifyInputError (message : String) : InputError :=
  if message.startsWith "resource-exhaustion" then .resource message
  else if malformedStructuralDiagnostic message then .invalid message
  else if message.startsWith "unsupported" then .unsupported message
  else .invalid message

/-- Typed diagnostics preserve exactly the original decoder's accepted values. -/
def decodeWithDiagnostics (input : String) : Except InputError Decoded :=
  match decode input with
  | .ok decoded => .ok decoded
  | .error message => .error (classifyInputError message)

theorem decodeWithDiagnostics_success (input : String) (decoded : Decoded) :
    decodeWithDiagnostics input = .ok decoded ↔ decode input = .ok decoded := by
  unfold decodeWithDiagnostics
  cases decode input <;> simp

theorem decodeWithDiagnostics_error (input : String) (error : InputError) :
    decodeWithDiagnostics input = .error error ↔
      ∃ message, decode input = .error message ∧ classifyInputError message = error := by
  unfold decodeWithDiagnostics
  cases decode input <;> simp

def diagnosticKind (input : String) : String :=
  match decodeWithDiagnostics input with
  | .ok _ => "ok"
  | .error (.invalid _) => "invalid"
  | .error (.unsupported _) => "unsupported"
  | .error (.resource _) => "resource"

theorem emptyArguments_invalid : diagnosticKind "fof(a,axiom,p())." = "invalid" := by cbv
theorem trailingComma_invalid : diagnosticKind "fof(a,axiom,p(a,))." = "invalid" := by cbv
theorem equality_unsupported : diagnosticKind "fof(a,axiom,a=b)." = "unsupported" := by cbv
theorem implication_accepted : diagnosticKind "fof(a,axiom,(p=>q))." = "ok" := by cbv
theorem resource_preserved (message : String)
    (resourcePrefix : message.startsWith "resource-exhaustion" = true) :
    classifyInputError message = .resource message := by
  simp [classifyInputError, resourcePrefix]

#print axioms decodeWithDiagnostics_success
#print axioms decodeWithDiagnostics_error
#print axioms emptyArguments_invalid
#print axioms trailingComma_invalid
#print axioms equality_unsupported
#print axioms implication_accepted
#print axioms resource_preserved

end Fang.FOFFrontend
