/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Controls only. Runs the replay with naming on a small input under the
   checker's limits record: at threshold 8 the left side of the disjunction is
   named, which adds one unary predicate and leaves six clauses instead of nine;
   with a threshold that names nothing, the prepared problem is the one of the
   replay without naming. The arity list of the named predicates comes from the
   definitions of the naming run; a copy of the preparation that changes that
   list shows that a list which disagrees with the clauses is refused: by the
   count check, by the equality conversion, which checks every atom against the
   reserved table, and again by the signature gate of the certificate check. -/
import NamedReplay
import NativeLimits

namespace Fang.TptpCandidate.FullFof.Integration.Named.Controls
open Aeneas.Std Fang.TptpCandidate.FullFof.Integration

def input : List UInt8 :=
  "fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n".toUTF8.toList

def named (threshold : Nat) : Except NamedError ReplayPrepared :=
  prepareNamed Fang.NativeLimits.declarationLimit input Fang.NativeLimits.byteLimit Fang.NativeLimits.replayLimits
    { bv := BitVec.ofNat _ threshold } Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals

def plain : Except ReplayError ReplayPrepared :=
  prepareLimited Fang.NativeLimits.declarationLimit input Fang.NativeLimits.byteLimit Fang.NativeLimits.replayLimits
    Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals

#guard match named 8 with
  | .ok prepared => prepared.predicateArities == [1, 1, 1, 1, 1, 1, 1] && prepared.problem.length == 6
  | .error _ => false

#guard match named 1000000, plain with
  | .ok prepared, .ok reference =>
    reprStr prepared.problem == reprStr reference.problem && prepared.problem.length == 9 &&
      prepared.predicateArities == reference.predicateArities &&
      prepared.functionArities == reference.functionArities
  | _, _ => false

/-- The steps of `prepareNamed` at threshold 8, with the arity list of the named
    predicates passed through `change` before the final checks. -/
def changed (change : List Usize → List Usize) : Except NamedError ReplayPrepared := do
  let limits := Fang.NativeLimits.replayLimits
  let numeric ← (decodeNumericLimited Fang.NativeLimits.declarationLimit input Fang.NativeLimits.byteLimit).mapError
    .replay
  let encoded ← ((transport numeric Fang.NativeLimits.maximumPredicates).mapError .transport).mapError .replay
  let transformed ← ((FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing).mapError .replay
  let first ← firstNamed encoded.reservation.equality
  let named ← ((replayNamedBlocks limits { bv := BitVec.ofNat _ 8 } first.val first
    transformed.formulas.val).mapError .preprocessing).mapError .replay
  let ordinary ← ((FangOriginalReplay.assemble numeric.declarations named.1).mapError .preprocessing).mapError .replay
  finishNamed numeric encoded.reservation (transformed.signature.functions.val.map (fun value => value.val)) first
    (named.1, named.2.1, change named.2.2) ordinary Fang.NativeLimits.maximumPredicates
    Fang.NativeLimits.maximumLiterals

/-- A certificate that decodes and passes the signature gate of a well-formed
    problem, and whose final clause is not empty. -/
def probe : String :=
  "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 0) (final 0))"

/-- `acceptsNamed` over the changed preparation, with the probe certificate. -/
def checked (change : List Usize → List Usize) : Except AcceptNamedError Unit := do
  let prepared ← (changed change).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities probe).mapError .certificate

-- Unchanged, the copy prepares what `prepareNamed` prepares, and the probe passes
-- the signature gate and fails in the inference check.
#guard match changed id, named 8 with
  | .ok prepared, .ok reference =>
    reprStr prepared.problem == reprStr reference.problem &&
      prepared.predicateArities == reference.predicateArities
  | _, _ => false

#guard match checked id with
  | .error (.certificate (.inference _)) => true
  | _ => false

-- A missing or an extra named predicate fails the count check.
#guard match changed (fun _ => []) with
  | .error .range => true
  | _ => false

#guard match changed (· ++ [1#usize]) with
  | .error .range => true
  | _ => false

-- A wrong arity is refused by the equality conversion.
#guard match changed (List.map fun _ => 2#usize) with
  | .error (.replay (.conversion _)) => true
  | _ => false

#guard match changed (List.map fun _ => 0#usize) with
  | .error (.replay (.conversion _)) => true
  | _ => false

-- The signature gate of the certificate check refuses it too: the prepared
-- problem checked against a table with a wrong arity for the named predicate.
#guard match named 8 with
  | .ok prepared =>
    match checkProblem prepared.problem prepared.functionArities (prepared.predicateArities.dropLast ++ [2]) probe with
    | .error .signature => true
    | _ => false
  | .error _ => false

end Fang.TptpCandidate.FullFof.Integration.Named.Controls
