/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft version 5: ordered positional paramodulation over explicit equality CNF. -/
import EqualityCertificateInput
import OrderedTrace

namespace Fang.EqualityOrderedCertificateInput
open Frontend
open Equality.Ordered

def root : Parser Equality.Ordered.Root := do
  expect "("
  let kind ← consume
  let result ← if kind == "argument" then pure (Root.argument (← natural))
    else if kind == "equality-left" then pure Root.equalityLeft
    else if kind == "equality-right" then pure Root.equalityRight
    else fail "unsupported: paramodulation root"
  expect ")"
  pure result

def pathItems : Nat → Parser (List Nat)
  | 0 => fail "resource-exhaustion: occurrence path fuel"
  | fuel + 1 => do
    if (← peek) == some ")" then pure []
    else
      let first ← natural
      pure (first :: (← pathItems fuel))

def path (fuel : Nat) : Parser (List Nat) := do
  expect "("
  expect "path"
  let result ← pathItems fuel
  expect ")"
  pure result

def witness (fuel : Nat) : Parser Equality.Ordered.Witness := do
  let sourcePivot ← natural
  let targetLiteral ← natural
  let root ← root
  let path ← path fuel
  let direction ← consume
  if direction != "forward" && direction != "reverse" then
    fail "unsupported: paramodulation direction"
  let substitution ← CertificateInput.substitution fuel
  pure { sourcePivot, targetLiteral, root, path, reverse := direction == "reverse", substitution }

def nodes : Nat → Nat → Parser (List Equality.Ordered.Step × Nat)
  | 0, _ => fail "resource-exhaustion: ordered equality certificate node fuel"
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
          pure (Equality.Ordered.Step.input (← natural))
        else if kind == "eq-resolve" then do
          let parent ← CertificateInput.parent id
          let before ← EqualityCertificateInput.clause fuel
          let after ← EqualityCertificateInput.clause fuel
          let left ← CertificateInput.term fuel
          let right ← CertificateInput.term fuel
          let substitution ← CertificateInput.substitution fuel
          let claimed ← EqualityCertificateInput.clause fuel
          pure (.equalityResolution parent before after left right substitution claimed)
        else if kind == "factor" then do
          let parent ← CertificateInput.parent id
          let first ← natural
          let second ← natural
          let substitution ← CertificateInput.substitution fuel
          let claimed ← EqualityCertificateInput.clause fuel
          pure (.factor parent first second substitution claimed)
        else if kind == "resolve" then do
          let left ← CertificateInput.parent id
          let leftPosition ← natural
          let right ← CertificateInput.parent id
          let rightPosition ← natural
          let substitution ← CertificateInput.substitution fuel
          let claimed ← EqualityCertificateInput.clause fuel
          pure (.resolution left leftPosition right rightPosition substitution claimed)
        else if kind == "paramodulate" then do
          let source ← CertificateInput.parent id
          let target ← CertificateInput.parent id
          let selected ← witness fuel
          let claimed ← EqualityCertificateInput.clause fuel
          pure (.paramodulation source target selected claimed)
        else fail "unsupported: ordered equality certificate rule"
      expect ")"
      let (rest, finalId) ← nodes fuel (nextId + 1)
      pure (step :: rest, finalId)

def certificate (fuel : Nat) : Parser Equality.Ordered.Certificate := do
  expect "("
  expect "fang-proof"
  let version ← natural
  if version != 5 then fail "unsupported: ordered equality certificate version"
  expect "("
  expect "preprocessing"
  expect "identity-cnf-equality-v1"
  expect ")"
  let (steps, finalId) ← nodes fuel 0
  expect ")"
  if (← peek).isSome then fail "invalid-certificate: trailing tokens"
  pure { steps, final := finalId }

def decode (input : String) : Except String Equality.Ordered.Certificate := do
  let tokens ← Frontend.tokenize input
  let (certificate, _) ← certificate (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize }
  pure certificate

def certificateWellFormed (functions predicates : List Nat) (certificate : Equality.Ordered.Certificate) : Bool :=
  certificate.steps.all fun step => match step with
    | .input _ => true
    | .equalityResolution _ before after left right substitution claimed =>
        EqualityCertificateInput.clauseWellFormed functions predicates before &&
        EqualityCertificateInput.clauseWellFormed functions predicates after &&
        termWellFormed functions left && termWellFormed functions right &&
        substitution.all (fun entry => termWellFormed functions entry.2) &&
        EqualityCertificateInput.clauseWellFormed functions predicates claimed
    | .factor _ _ _ substitution claimed | .resolution _ _ _ _ substitution claimed =>
        substitution.all (fun entry => termWellFormed functions entry.2) &&
        EqualityCertificateInput.clauseWellFormed functions predicates claimed
    | .paramodulation _ _ witness claimed =>
        witness.substitution.all (fun entry => termWellFormed functions entry.2) &&
        EqualityCertificateInput.clauseWellFormed functions predicates claimed

inductive CheckError where
  | certificate : String → CheckError
  | signature
  | inference : Equality.TraceError → CheckError
  deriving Repr

def accepts (problem : Equality.Problem) (functions predicates : List Nat)
    (proof : String) : Except CheckError Unit := do
  let certificate ← (decode proof).mapError CheckError.certificate
  if !(problem.all (EqualityCertificateInput.clauseWellFormed functions predicates)) ||
      !(certificateWellFormed functions predicates certificate) then
    .error .signature
  else (Equality.Ordered.check problem certificate).mapError CheckError.inference

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
    · cases checked : Equality.Ordered.check problem certificate with
      | error error => simp [checked] at accepted
      | ok result => exact Equality.Ordered.check_unsat problem certificate (by cases result; exact checked)

end Fang.EqualityOrderedCertificateInput
