import Fang.Input
import Fang.Checker

/- Copyright (c) 2026 Pietro Pellegrino. Released under the BSD 3-Clause license. -/

namespace Fang
namespace CertificateInput

open Frontend

mutual
  def term : Nat → Parser Term
    | 0 => fail "resource-exhaustion: certificate term decoder fuel"
    | fuel + 1 => do
      expect "("
      let kind ← consume
      let result ← if kind == "v" then do
          pure (.var (← natural))
        else if kind == "f" then do
          let symbol ← natural
          pure (.app symbol (← terms fuel))
        else fail s!"invalid-certificate: unknown term tag '{kind}'"
      expect ")"
      pure result

  def terms : Nat → Parser (List Term)
    | 0 => fail "resource-exhaustion: certificate argument decoder fuel"
    | fuel + 1 => do
      if (← peek) == some ")" then pure []
      else
        let first ← term fuel
        pure (first :: (← terms fuel))
end

def bindings : Nat → Parser Subst
  | 0 => fail "resource-exhaustion: substitution decoder fuel"
  | fuel + 1 => do
    if (← peek) == some ")" then pure []
    else
      expect "("
      let varId ← natural
      let value ← term fuel
      expect ")"
      let rest ← bindings fuel
      if rest.any (fun entry => entry.1 == varId) then
        fail "invalid-certificate: duplicate substitution key"
      pure ((varId, value) :: rest)

def substitution (fuel : Nat) : Parser Subst := do
  expect "("
  expect "subst"
  let result ← bindings fuel
  expect ")"
  pure result

def literals : Nat → Parser Clause
  | 0 => fail "resource-exhaustion: certificate clause decoder fuel"
  | fuel + 1 => do
    if (← peek) == some ")" then pure []
    else
      expect "("
      let polarity ← consume
      if polarity != "pos" && polarity != "neg" then
        fail "invalid-certificate: expected pos or neg"
      let pred ← natural
      let args ← terms fuel
      expect ")"
      let rest ← literals fuel
      pure ({ positive := polarity == "pos", atom := { pred, args } } :: rest)

def clause (fuel : Nat) : Parser Clause := do
  expect "("
  expect "clause"
  let result ← literals fuel
  expect ")"
  pure result

def parent (nodeId : Nat) : Parser Nat := do
  let id ← natural
  if id ≥ nodeId then fail "invalid-certificate: parent must precede its node"
  pure id

def nodes : Nat → Nat → Parser (List Step × Nat)
  | 0, _ => fail "resource-exhaustion: certificate node decoder fuel"
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
          pure (Step.input (← natural))
        else if kind == "factor" then do
          let premise ← parent id
          let first ← natural
          let second ← natural
          if first == second then fail "invalid-certificate: factoring positions must differ"
          let subst ← substitution fuel
          let claimed ← clause fuel
          pure (.factor premise first second subst claimed)
        else if kind == "resolve" then do
          let left ← parent id
          let leftPos ← natural
          let right ← parent id
          let rightPos ← natural
          let subst ← substitution fuel
          let claimed ← clause fuel
          pure (.resolve left leftPos right rightPos subst claimed)
        else fail s!"invalid-certificate: unknown node kind '{kind}'"
      expect ")"
      let (rest, finalId) ← nodes fuel (nextId + 1)
      pure (step :: rest, finalId)

def certificate (fuel : Nat) : Parser Certificate := do
  expect "("
  expect "fang-proof"
  let version ← natural
  if version != 1 then fail "unsupported: certificate version"
  let (steps, finalId) ← nodes fuel 0
  expect ")"
  if (← peek).isSome then fail "invalid-certificate: trailing tokens"
  pure { steps, final := finalId }

end CertificateInput

def decodeCertificate (input : String) : Except String Certificate := do
  let tokens ← Frontend.tokenize input
  let (certificate, _) ← CertificateInput.certificate (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize
  }
  pure certificate

mutual
  def termWellFormed (arities : List Nat) : Term → Bool
    | .var _ => true
    | .app symbol args => arities[symbol]? == some args.length && termsWellFormed arities args

  def termsWellFormed (arities : List Nat) : List Term → Bool
    | [] => true
    | first :: rest => termWellFormed arities first && termsWellFormed arities rest
end

def clauseWellFormed (signature : DecodedProblem) (clause : Clause) : Bool :=
  clause.all fun literal =>
    signature.predicateArities[literal.atom.pred]? == some literal.atom.args.length &&
    termsWellFormed signature.functionArities literal.atom.args

def certificateWellFormed (signature : DecodedProblem) (certificate : Certificate) : Bool :=
  certificate.steps.all fun step =>
    match step with
    | .input _ => true
    | .factor _ _ _ subst claimed | .resolve _ _ _ _ subst claimed =>
      subst.all (fun entry => termWellFormed signature.functionArities entry.2) &&
      clauseWellFormed signature claimed

end Fang
