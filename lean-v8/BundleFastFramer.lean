/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Linear framing for bundle acceptance. The lexer keeps the remaining length
   as a counter instead of recomputing it and collects pieces in reverse, and
   statement splitting collects pieces in reverse. Each fast function is proved
   equal to the gated one, so `acceptsBundleFast` is `acceptsBundle` and its
   theorems follow by rewriting. The same pattern as `fastTokenizeBytes`. -/
import BundleFastLexer
import BundleReplay

namespace Fang.TptpCandidate.FullFof.Coverage.FramerV2

open Fang.TptpCandidate.FullFof.Coverage

def statementsFast : Nat → List Name → Nat → List Piece → Except Error (List Statement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ 1000 then .error ⟨.resource, first.start⟩
    else
      let split := splitStatementFast 0 [] (first :: more)
      match keyword split.1 with
      | some "include" =>
        match directive split.1 with
        | .error failure => .error failure
        | .ok (parts, selection) =>
          match statementsFast fuel seen endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecord seen endOffset split.1 with
        | .error failure => .error failure
        | .ok value =>
          match statementsFast fuel (value.name :: seen) endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.formula value :: tail)

theorem statementsFast_eq : ∀ (fuel : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Piece),
    statementsFast fuel seen endOffset pieces = statements fuel seen endOffset pieces
  | 0, _, _, _ => rfl
  | _ + 1, _, _, [] => rfl
  | fuel + 1, seen, endOffset, first :: more => by
    have split : splitStatementFast 0 [] (first :: more) = splitStatement 0 [] (first :: more) :=
      splitStatementFast_eq 0 [] (first :: more)
    simp only [statementsFast, statements, split, statementsFast_eq fuel]
    -- The two definitions use distinct auxiliary match functions with equal bodies.
    rfl

def frameFileFast (bytes : List UInt8) (maximum : Nat) : Except Error (List Statement) :=
  match tokenizeFast bytes maximum with
  | .error failure => .error failure
  | .ok pieces => statementsFast (pieces.length + 1) [] bytes.length pieces

theorem frameFileFast_eq (bytes : List UInt8) (maximum : Nat) :
    frameFileFast bytes maximum = frameFile bytes maximum := by
  simp only [frameFileFast, frameFile, tokenizeFast_eq, statementsFast_eq]
  rfl

def frameBundleFast : List (Key × List UInt8) → Nat → Except Error Bundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFileFast bytes maximum with
    | .error failure => .error failure
    | .ok framed => match frameBundleFast rest maximum with
      | .error failure => .error failure
      | .ok others => .ok (⟨key, framed⟩ :: others)

theorem frameBundleFast_eq : ∀ (files : List (Key × List UInt8)) (maximum : Nat),
    frameBundleFast files maximum = frameBundle files maximum
  | [], _ => rfl
  | (key, bytes) :: rest, maximum => by
    simp only [frameBundleFast, frameBundle, frameFileFast_eq, frameBundleFast_eq rest maximum]
    rfl

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.statementsFast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.frameFileFast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.frameBundleFast_eq

end Fang.TptpCandidate.FullFof.Coverage.FramerV2

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8

open Aeneas.Std
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def bundleNumericFast (files : List (Key × List UInt8)) (maximumBytes : Nat) :
    Except BundleError NumericInput :=
  match frameBundleFast files maximumBytes with
  | .error failure => .error (.frame failure)
  | .ok bundle =>
    match expand bundle bundleFuel with
    | .error failure => .error (.expand failure)
    | .ok items =>
      if wellShaped bundle bundleFuel then
        match readInput (declarationsOf bundle items) with
        | none => .error .nonliteral
        | some input => .ok (withGenerated input
            (distinctAxioms input.predicates.length (objectIds input (declarationsOf bundle items))))
      else .error .shape

theorem bundleNumericFast_eq (files : List (Key × List UInt8)) (maximumBytes : Nat) :
    bundleNumericFast files maximumBytes = bundleNumeric files maximumBytes := by
  unfold bundleNumericFast bundleNumeric
  rw [frameBundleFast_eq]
  rfl

def prepareBundleFast (files : List (Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleReplayError ReplayPrepared := do
  let numeric ← (bundleNumericFast files maximumBytes).mapError .bundle
  (replayFrom numeric limits maximumPredicates maximumLiterals).mapError .replay

theorem prepareBundleFast_eq (files : List (Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    prepareBundleFast files maximumBytes limits maximumPredicates maximumLiterals =
      prepareBundle files maximumBytes limits maximumPredicates maximumLiterals := by
  simp only [prepareBundleFast, prepareBundle, bundleNumericFast_eq]

/-- The entry for the native checker: `acceptsBundle` with the linear framer. -/
def acceptsBundleFast (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleAcceptError Unit := do
  let prepared ← (prepareBundleFast files maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem acceptsBundleFast_eq (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundleFast files maximumBytes proof limits maximumPredicates maximumLiterals =
      acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals := by
  simp only [acceptsBundleFast, acceptsBundle, prepareBundleFast_eq]

theorem acceptsBundleFast_refuted {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundleFast files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    BundleRefuted files maximumBytes bundleFuel := by
  rw [acceptsBundleFast_eq] at accepted
  exact acceptsBundle_refuted accepted

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.bundleNumericFast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.prepareBundleFast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.acceptsBundleFast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.acceptsBundleFast_refuted

end Fang.TptpCandidate.FullFof.Coverage.BundleV8
