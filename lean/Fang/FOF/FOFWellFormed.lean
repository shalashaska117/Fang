/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFProblemGrammar
import Fang.SourceWellFormed

namespace Fang.NamedFOF

def Formula.WellFormed (signature : Source.Signature) : Formula → Prop
  | .atom name args => signature.predicateArity name = some args.length ∧
      Source.TermsWellFormed signature args
  | .truth | .falsity => True
  | .neg child => child.WellFormed signature
  | .conj left right | .disj left right | .implies left right =>
      left.WellFormed signature ∧ right.WellFormed signature

def Declaration.WellFormed (signature : Source.Signature) : Declaration → Prop
  | .cnf clause => clause.WellFormed signature
  | .fof _ formula => formula.Ground ∧ formula.WellFormed signature

def ProblemWellFormed (signature : Source.Signature) (named : List Declaration) : Prop :=
  ∀ declaration ∈ named, declaration.WellFormed signature

theorem Encoding.wellFormed {signature symbols variables named encoded}
    (encoding : Encoding signature symbols variables named encoded) : named.WellFormed signature := by
  induction encoding with
  | atom name args encoded roundtrip arity terms => exact ⟨arity, terms.wellFormed⟩
  | truth | falsity => trivial
  | neg child ih => exact ih
  | conj first second ih₁ ih₂ | disj first second ih₁ ih₂ | implies first second ih₁ ih₂ =>
      exact ⟨ih₁, ih₂⟩

theorem DeclarationEncoding.wellFormed {signature symbols named encoded}
    (encoding : DeclarationEncoding signature symbols named encoded) : named.WellFormed signature := by
  cases encoding with
  | cnf variables encoding => exact encoding.wellFormed
  | fof name variables ground encoding => exact ⟨ground, encoding.wellFormed⟩

theorem ProblemEncoding.wellFormed {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded) : ProblemWellFormed signature named := by
  intro declaration member
  obtain ⟨output, _, related⟩ := encoding.declarations.member_left member
  exact related.wellFormed

end Fang.NamedFOF

namespace Fang.FOFGrammar

/- Validity adds a shared arity assignment to the independent byte grammar.
   It contains no successful executable-decoder premise. -/
def ValidInput (bytes : List UInt8) : Prop :=
  ∃ named signature, Parses bytes named ∧ NamedFOF.ProblemWellFormed signature named

end Fang.FOFGrammar

namespace Fang.FOFFrontend
open Frontend

theorem decode_valid_input {input decoded} (success : decode input = .ok decoded) :
    FOFGrammar.ValidInput (Source.Grammar.spelling input) := by
  obtain ⟨named, parsed, encoding⟩ := decode_byte_grammar success
  exact ⟨named, signatureFrom decoded.state, parsed, encoding.wellFormed⟩

end Fang.FOFFrontend
