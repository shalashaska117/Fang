/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Version 4 is an isolated explicit-equality CNF certificate dialect. -/
import Fang.CertificateInput
import Trace

namespace Fang.EqualityCertificateInput
open Frontend

def literal (fuel : Nat) : Parser Equality.Literal := do
  expect "("
  let polarity ← consume
  if polarity != "pos" && polarity != "neg" then
    fail "invalid-certificate: expected pos or neg"
  expect "("
  let kind ← consume
  let atom ← if kind == "pred" then do
      let symbol ← natural
      pure (.predicate ⟨symbol, ← CertificateInput.terms fuel⟩)
    else if kind == "eq" then do
      let left ← CertificateInput.term fuel
      let right ← CertificateInput.term fuel
      pure (.equal left right)
    else fail "invalid-certificate: expected pred or eq"
  expect ")"
  expect ")"
  pure ⟨polarity == "pos", atom⟩

def literals : Nat → Parser Equality.Clause
  | 0 => fail "resource-exhaustion: equality certificate clause fuel"
  | fuel + 1 => do
    if (← peek) == some ")" then pure []
    else
      let first ← literal fuel
      pure (first :: (← literals fuel))

def clause (fuel : Nat) : Parser Equality.Clause := do
  expect "("
  expect "clause"
  let result ← literals fuel
  expect ")"
  pure result

def nodes : Nat → Nat → Parser (List Equality.Step × Nat)
  | 0, _ => fail "resource-exhaustion: equality certificate node fuel"
  | fuel + 1, nextId => do
    expect "("
    let kind ← consume
    if kind == "final" then
      let finalId ← natural
      if finalId ≥ nextId then fail "invalid-certificate: final node is out of range"
      expect ")"
      pure ([], finalId)
    else
      let id ← natural
      if id != nextId then fail "invalid-certificate: node IDs must be sequential"
      let step ← if kind == "input" then do
          pure (Equality.Step.input (← natural))
        else if kind == "eq-resolve" then do
          let parent ← CertificateInput.parent id
          let before ← clause fuel
          let after ← clause fuel
          let left ← CertificateInput.term fuel
          let right ← CertificateInput.term fuel
          let substitution ← CertificateInput.substitution fuel
          let claimed ← clause fuel
          pure (.unary parent (.equalityResolution before after left right substitution) claimed)
        else if kind == "factor" then do
          let parent ← CertificateInput.parent id
          let first ← natural
          let second ← natural
          let substitution ← CertificateInput.substitution fuel
          let claimed ← clause fuel
          pure (.unary parent (.factor first second substitution) claimed)
        else if kind == "resolve" then do
          let left ← CertificateInput.parent id
          let leftPosition ← natural
          let right ← CertificateInput.parent id
          let rightPosition ← natural
          let substitution ← CertificateInput.substitution fuel
          let claimed ← clause fuel
          pure (.binary left right (.resolution leftPosition rightPosition substitution) claimed)
        else fail "unsupported: equality certificate rule"
      expect ")"
      let (rest, finalId) ← nodes fuel (nextId + 1)
      pure (step :: rest, finalId)

def certificate (fuel : Nat) : Parser Equality.Certificate := do
  expect "("
  expect "fang-proof"
  let version ← natural
  if version != 4 then fail "unsupported: equality certificate version"
  expect "("
  expect "preprocessing"
  expect "identity-cnf-equality-v1"
  expect ")"
  let (steps, finalId) ← nodes fuel 0
  expect ")"
  if (← peek).isSome then fail "invalid-certificate: trailing tokens"
  pure { steps, final := finalId }

def decode (input : String) : Except String Equality.Certificate := do
  let tokens ← Frontend.tokenize input
  let (certificate, _) ← certificate (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize }
  pure certificate

def clauseWellFormed (functions predicates : List Nat) (clause : Equality.Clause) : Bool :=
  clause.all fun literal => match literal.atom with
    | .predicate atom => predicates[atom.pred]? == some atom.args.length &&
        termsWellFormed functions atom.args
    | .equal left right => termWellFormed functions left && termWellFormed functions right

def certificateWellFormed (functions predicates : List Nat) (certificate : Equality.Certificate) : Bool :=
  certificate.steps.all fun step => match step with
    | .input _ => true
    | .unary _ (.equalityResolution before after left right substitution) claimed =>
        clauseWellFormed functions predicates before && clauseWellFormed functions predicates after &&
        termWellFormed functions left && termWellFormed functions right &&
        substitution.all (fun entry => termWellFormed functions entry.2) &&
        clauseWellFormed functions predicates claimed
    | .unary _ (.factor _ _ substitution) claimed
      | .binary _ _ (.resolution _ _ substitution) claimed =>
        substitution.all (fun entry => termWellFormed functions entry.2) &&
        clauseWellFormed functions predicates claimed
    | _ => false

inductive CheckError where
  | certificate : String → CheckError
  | signature : CheckError
  | inference : Equality.TraceError → CheckError
  deriving Repr

/-- Numeric AST boundary only. The source decoder must supply its own theorem. -/
def accepts (problem : Equality.Problem) (functions predicates : List Nat)
    (proof : String) : Except CheckError Unit := do
  let certificate ← (decode proof).mapError CheckError.certificate
  if !(problem.all (clauseWellFormed functions predicates)) ||
      !(certificateWellFormed functions predicates certificate) then
    .error .signature
  else (Equality.check problem certificate).mapError CheckError.inference

theorem accepts_refutes {problem functions predicates proof}
    (accepted : accepts problem functions predicates proof = .ok ()) :
    ¬ Equality.Satisfiable problem := by
  unfold accepts at accepted
  cases decoded : decode proof with
  | error error => simp [decoded, Except.mapError, bind, Except.bind] at accepted
  | ok certificate =>
    simp only [decoded, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · contradiction
    · cases checked : Equality.check problem certificate with
      | error error => simp [checked] at accepted
      | ok result => exact Equality.check_refutes problem certificate (by cases result; exact checked)

end Fang.EqualityCertificateInput
