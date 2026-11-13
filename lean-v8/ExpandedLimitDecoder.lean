/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The version-8 checker with the declaration limit as a parameter. The accepted
   decoder stops after 1000 declarations and checks each new name against the
   list of names seen so far. `declarationsUpTo` is the accepted loop with the
   limit as a parameter, proved sound for every limit the way the accepted loop
   is, and equal to it at 1000. `declarationsHashed` runs it with the counted
   parsers, a declaration counter and a hash set of seen names, and is proved
   equal to it. The endpoint is restated: acceptance proves that the original
   bytes have no model, for every limit. -/
import ExpandedLinearCertificate
import Std.Data.HashSet

namespace Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-! The accepted loop with its limit as a parameter. -/

def declarationsUpTo (limit : Nat) : Nat → List Name → Nat → List Token → Except Error (List Declaration)
  | 0, _, endOffset, tokens => failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ limit then failure .resource endOffset tokens
    let (first, rest) ← CnfBoolean.declaration seen endOffset tokens
    let tail ← declarationsUpTo limit fuel (first.name :: seen) endOffset rest
    pure (first :: tail)

theorem declarationsUpTo_accepted : ∀ fuel seen endOffset tokens,
    declarationsUpTo 1000 fuel seen endOffset tokens = CnfBoolean.declarations fuel seen endOffset tokens
  | 0, _, _, _ => by
    unfold declarationsUpTo CnfBoolean.declarations
    rfl
  | _ + 1, _, _, [] => by
    unfold declarationsUpTo CnfBoolean.declarations
    rfl
  | fuel + 1, seen, endOffset, token :: rest => by
    unfold declarationsUpTo CnfBoolean.declarations
    by_cases full : seen.length ≥ 1000
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      apply bind_congr_ok
      intro value _
      rw [declarationsUpTo_accepted fuel (value.1.name :: seen) endOffset value.2]

theorem declarationsUpTo_sound {limit fuel seen endOffset input values}
    (success : declarationsUpTo limit fuel seen endOffset input = .ok values) :
    CnfBoolean.StatementsTokens input values ∧ Grammar.WellNamed values ∧
      ∀ label ∈ values.map Declaration.name, label ∉ seen := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpTo, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpTo] at success
      subst values
      exact ⟨.empty, by simp [Grammar.WellNamed], by simp⟩
    | cons token rest =>
      by_cases large : seen.length ≥ limit
      · simp [declarationsUpTo, large, failure, bind, Except.bind] at success
      · cases firstAt : CnfBoolean.declaration seen endOffset (token :: rest) with
        | error error => simp [declarationsUpTo, large, firstAt, bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨first, afterFirst⟩
          cases tailAt : declarationsUpTo limit fuel (first.name :: seen) endOffset afterFirst with
          | error error => simp [declarationsUpTo, large, firstAt, tailAt, bind, Except.bind] at success
          | ok more =>
            simp [declarationsUpTo, large, firstAt, tailAt, bind, Except.bind, pure, Except.pure] at success
            subst values
            obtain ⟨firstParsed, firstFresh⟩ := CnfBoolean.declaration_sound firstAt
            obtain ⟨moreParsed, moreUnique, moreFresh⟩ := ih tailAt
            refine ⟨.cons firstParsed moreParsed, ?_, ?_⟩
            · simp only [Grammar.WellNamed, List.map_cons, List.nodup_cons] at *
              exact ⟨fun member => moreFresh first.name member (by simp), moreUnique⟩
            · intro label member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with rfl | member
              · exact firstFresh
              · exact fun old => moreFresh label member (by simp [old])

theorem declarationsUpTo_closed {limit fuel seen endOffset input values}
    (success : declarationsUpTo limit fuel seen endOffset input = .ok values) : Grammar.Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpTo, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpTo] at success
      subst values
      simp [Grammar.Closed]
    | cons token rest =>
      unfold declarationsUpTo at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact CnfBoolean.declaration_closed firstAt
      · exact ih tailAt value member

/-! Bytes, grammar and models. -/

def decodeBytesUpTo (limit : Nat) (input : List UInt8) (maximumBytes : Nat) : Except Error (List Declaration) := do
  let tokens ← tokenizeBytes input maximumBytes
  declarationsUpTo limit (tokens.length + 1) [] input.length tokens

theorem decodeBytesUpTo_accepted (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesUpTo 1000 input maximumBytes = CnfBoolean.decodeBytes input maximumBytes := by
  unfold decodeBytesUpTo CnfBoolean.decodeBytes
  apply bind_congr_ok
  intro tokens _
  exact declarationsUpTo_accepted _ _ _ _

theorem decodeUpTo_has_tokens {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) :
    ∃ tokens, tokenizeBytes input maximum = .ok tokens ∧
      declarationsUpTo limit (tokens.length + 1) [] input.length tokens = .ok values := by
  unfold decodeBytesUpTo at success
  cases lexical : tokenizeBytes input maximum with
  | error reason => simp [lexical, bind, Except.bind] at success
  | ok tokens => exact ⟨tokens, rfl, by simpa [lexical, bind, Except.bind] using success⟩

theorem decodeUpTo_grammar {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) : CnfBoolean.ByteParsed input maximum values := by
  obtain ⟨tokens, lexical, parsed⟩ := decodeUpTo_has_tokens success
  obtain ⟨grammar, unique, _⟩ := declarationsUpTo_sound parsed
  exact ⟨tokens, lexical, grammar, unique⟩

theorem decodeUpTo_closed {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) : Grammar.Closed values := by
  obtain ⟨tokens, _, parsed⟩ := decodeUpTo_has_tokens success
  exact declarationsUpTo_closed parsed

theorem decodeUpTo_bytes_satisfiable {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) :
    CnfBoolean.BytesSatisfiable input maximum ↔ Satisfiable (source values) := by
  have models {D : Type} (model : Source.Interpretation D) :
      CnfBoolean.BytesModels input maximum model ↔ Models (source values) model := by
    constructor
    · rintro ⟨other, parsed, _, holds⟩
      have same := CnfBoolean.byteParsed_source_unique parsed (decodeUpTo_grammar success)
      simpa only [same] using holds
    · intro holds
      exact ⟨values, decodeUpTo_grammar success, decodeUpTo_closed success, holds⟩
  constructor
  · rintro ⟨domain, inhabited, model, holds⟩
    exact ⟨domain, inhabited, model, (models model).mp holds⟩
  · rintro ⟨domain, inhabited, model, holds⟩
    exact ⟨domain, inhabited, model, (models model).mpr holds⟩

theorem decodeUpTo_readInput_unsat {limit bytes maximum values input}
    (decoded : decodeBytesUpTo limit bytes maximum = .ok values)
    (encoded : readInput values = some input) (refuted : ¬ input.Satisfiable) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximum :=
  fun model => refuted (((decodeUpTo_bytes_satisfiable decoded).trans
    (readInput_satisfiable encoded (decodeUpTo_closed decoded))).mp model)

/-! The counted decoder with a declaration counter and a hash set of seen names. -/

deriving instance Hashable for Name

/-- `declarationC` with the test for seen names as a parameter. -/
def declarationSeenC (isSeen : Name → Bool) (endOffset : Nat) (tokens : List Token) (count : Nat) :
    Except Error (Declaration × List Token × Nat) := do
  let keyword :: rest := tokens | failure .invalid endOffset tokens
  let isCnf ← match keyword.kind with
    | .legacy (.lower "cnf") => pure true
    | .legacy (.lower "fof") => pure false
    | .legacy (.lower "include") | .legacy (.lower "tff") | .legacy (.lower "thf") |
        .legacy (.lower "tcf") => failure .unsupported endOffset tokens
    | _ => failure .invalid endOffset tokens
  let (_, rest) ← expect '(' endOffset rest
  let nameToken :: rest := rest | failure .invalid endOffset rest
  let .legacy nameKind := nameToken.kind | failure .invalid endOffset (nameToken :: rest)
  let some label := nameKind.name | failure .invalid endOffset (nameToken :: rest)
  if isSeen label then failure .invalid endOffset (nameToken :: rest)
  let (_, rest) ← expect ',' endOffset rest
  let role :: rest := rest | failure .invalid endOffset rest
  match role.kind with
  | .legacy (.lower "axiom") => pure ()
  | .legacy (.lower _) => failure .unsupported endOffset (role :: rest)
  | _ => failure .invalid endOffset (role :: rest)
  let (_, originalBody) ← expect ',' endOffset rest
  let bodyCount := count - 6
  let (body, rest, restCount) ← if isCnf then do
      let (values, rest, restCount) ← clauseC (bodyCount + 1) 1 endOffset originalBody bodyCount
      pure (Body.cnf values, rest, restCount)
    else do
      let (body, rest, restCount) ← formulaC (3 * bodyCount + 1) 1 [] endOffset originalBody bodyCount
      pure (Body.fof body, rest, restCount)
  let bodyStop := ((originalBody.take (bodyCount - restCount)).getLast?.map Token.stop).getD endOffset
  if isChar ',' rest then failure .unsupported endOffset rest
  let (_, rest) ← expect ')' endOffset rest
  let (dot, rest) ← expect '.' endOffset rest
  pure (⟨label, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest, restCount - 2)

theorem declarationSeenC_eq {isSeen : Name → Bool} {seen : List Name} (same : ∀ label, isSeen label = seen.contains label)
    (endOffset : Nat) (tokens : List Token) (count : Nat) :
    declarationSeenC isSeen endOffset tokens count = declarationC seen endOffset tokens count := by
  have : isSeen = fun label => seen.contains label := funext same
  subst this
  rfl

def declarationsHashed (limit : Nat) : Nat → Std.HashSet Name → Nat → Nat → List Token → Nat →
    Except Error (List Declaration)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | _ + 1, _, _, _, [], _ => .ok []
  | fuel + 1, seen, seenCount, endOffset, tokens@(_ :: _), count => do
    if seenCount ≥ limit then failure .resource endOffset tokens
    let (first, rest, restCount) ← declarationSeenC (fun label => seen.contains label) endOffset tokens count
    let tail ← declarationsHashed limit fuel (seen.insert first.name) (seenCount + 1) endOffset rest restCount
    pure (first :: tail)

theorem declarationsHashed_eq (limit : Nat) : ∀ fuel (set : Std.HashSet Name) seen seenCount endOffset tokens count,
    (∀ label, set.contains label = seen.contains label) → seenCount = seen.length → count = tokens.length →
    declarationsHashed limit fuel set seenCount endOffset tokens count =
      declarationsUpTo limit fuel seen endOffset tokens
  | 0, _, _, _, _, _, _, _, _, _ => by
    unfold declarationsHashed declarationsUpTo
    rfl
  | _ + 1, _, _, _, _, [], _, _, _, _ => by
    unfold declarationsHashed declarationsUpTo
    rfl
  | fuel + 1, set, seen, seenCount, endOffset, token :: rest, count, members, counted, length => by
    subst counted
    unfold declarationsHashed declarationsUpTo
    by_cases full : seen.length ≥ limit
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      rw [declarationSeenC_eq members, declarationC_eq length, bind_annotate]
      apply bind_congr_ok
      intro value _
      simp only [annotate]
      rw [declarationsHashed_eq limit fuel (set.insert value.1.name) (value.1.name :: seen) (seen.length + 1)
        endOffset value.2 value.2.length (by
          intro label
          rw [Std.HashSet.contains_insert, members, List.contains_cons]
          by_cases same : label = value.1.name
          · subst same
            simp
          · have other : value.1.name ≠ label := fun reversed => same reversed.symm
            rw [beq_false_of_ne other, beq_false_of_ne same])
        (by simp) rfl]

/-- The declaration limit as a parameter, with the linear lexer, the counted
    parsers, a declaration counter and a hash set of seen names. -/
def decodeBytesLimited (limit : Nat) (input : List UInt8) (maximumBytes : Nat) : Except Error (List Declaration) :=
  (fastTokenizeBytes input maximumBytes).bind fun tokens =>
    declarationsHashed limit (tokens.length + 1) {} 0 input.length tokens tokens.length

theorem decodeBytesLimited_eq (limit : Nat) (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesLimited limit input maximumBytes = decodeBytesUpTo limit input maximumBytes := by
  unfold decodeBytesLimited decodeBytesUpTo
  rw [fastTokenizeBytes_eq]
  cases tokenizeBytes input maximumBytes with
  | error error => rfl
  | ok tokens =>
    exact declarationsHashed_eq limit _ {} [] 0 input.length tokens tokens.length
      (by intro label; simp) rfl rfl

/-! The checker with the declaration limit as a parameter. -/

def decodeNumericLimited (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) :
    Except ReplayError NumericInput := do
  let source ← (decodeBytesLimited limit bytes maximumBytes).mapError .input
  match readInput source with
  | none => .error .nonliteral
  | some input => .ok input

theorem decodeNumericLimited_witness {limit bytes maximum input}
    (success : decodeNumericLimited limit bytes maximum = .ok input) :
    ∃ values, decodeBytesUpTo limit bytes maximum = .ok values ∧ readInput values = some input := by
  obtain ⟨values, decoded, success⟩ := bind_success success
  cases encoded : readInput values with
  | none => simp [encoded] at success
  | some result =>
    have same : result = input := Except.ok.inj (by simpa only [encoded] using success)
    subst input
    exact ⟨values, by rw [← decodeBytesLimited_eq]; exact mapError_success decoded, encoded⟩

def prepareLimited (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except ReplayError ReplayPrepared := do
  let numeric ← decodeNumericLimited limit bytes maximumBytes
  let encoded ← (transport numeric maximumPredicates).mapError .transport
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble numeric.declarations blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨numeric, equality, transformed.signature.functions.val.map (fun value => value.val),
    numeric.predicates.map Prod.snd⟩

theorem prepareLimited_witness {limit bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareLimited limit bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ values encoded transformed blocks ordinary,
      decodeBytesUpTo limit bytes maximumBytes = .ok values ∧
      readInput values = some prepared.original ∧
      transport prepared.original maximumPredicates = .ok encoded ∧
      fang_skolem_core.skolemize_problem encoded.declarations encoded.signature limits.skolem = .ok (.Ok transformed) ∧
      List.Forall₂ ActualClausificationStep transformed.formulas.val blocks ∧
      MixedLayout prepared.original.declarations blocks ordinary ∧
      FangQuantifiedEquality.ActualProblemConversion encoded.reservation ordinary prepared.problem := by
  obtain ⟨numeric, decoded, success⟩ := bind_success success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨blocks, blocksRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨equality, conversionRun, success⟩ := bind_success success
  cases Except.ok.inj success
  obtain ⟨values, parsed, numericRun⟩ := decodeNumericLimited_witness decoded
  exact ⟨values, encoded, transformed, blocks, ordinary, parsed, numericRun,
    mapError_success inputRun, FangOriginalReplay.observe_success (mapError_success skolemRun),
    FangOriginalReplay.replayBlocks_steps (mapError_success blocksRun),
    FangOriginalReplay.assemble_layout (mapError_success assemblyRun),
    FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_success conversionRun)⟩

/-- Acceptance of the prepared problem excludes every original byte model, for every declaration limit. -/
theorem prepareLimited_check_original_unsat {limit bytes maximumBytes limits maximumPredicates maximumLiterals
    prepared}
    (success : prepareLimited limit bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨values, encoded, transformed, blocks, ordinary, decoded, numericRun,
    inputRun, skolemRun, steps, layout, converted⟩ := prepareLimited_witness success
  apply decodeUpTo_readInput_unsat decoded numericRun
  rintro ⟨D, nonempty, original, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, _, _⟩ := transport_tables inputRun
  have originalHolds := transport_models inputRun holds
  have reservedHolds :
      (retained prepared.original.declarations).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
        encoded.declarations.val := by
    rw [slot, ← reserve_interpretation]
    exact originalHolds
  obtain ⟨extended, preserved, grouped⟩ := skolem_actual_problem_models skolemRun
    (retained prepared.original.declarations) (transport_retained_below numericRun inputRun)
    blocks steps (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
  have groupedModel := grouped.mpr reservedHolds
  have mixedModel : ordinary.Models extended := (mixedLayout_models layout extended).mpr
    ((FangQuantifiedPipeline.models_append extended _ _).mp groupedModel)
  have equalityModel := (FangQuantifiedEquality.actualProblem_models original extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact Fang.Equality.Ordered.check_unsat prepared.problem certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended, equalityModel⟩

/-- The native entry with the declaration limit as a parameter. Same envelope and checker as `accepts`. -/
def acceptsLimited (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareLimited limit bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

/-- Acceptance proves that the original bytes have no model, for every declaration limit. -/
theorem acceptsLimited_original_unsat {limit bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsLimited limit bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  exact prepareLimited_check_original_unsat (mapError_success replayRun) parsed refuted

/-- At the accepted limit the parameterized entry is the accepted one. -/
theorem acceptsLimited_accepted (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    acceptsLimited 1000 bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals := by
  have decoded : ∀ bytes maximumBytes, decodeNumericLimited 1000 bytes maximumBytes = decodeNumeric bytes maximumBytes := by
    intro bytes maximumBytes
    unfold decodeNumericLimited decodeNumeric
    rw [decodeBytesLimited_eq, decodeBytesUpTo_accepted]
    rfl
  unfold acceptsLimited accepts prepareLimited prepare
  simp only [decoded]

#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpTo_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpTo_sound
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpTo_closed
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeBytesUpTo_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpTo_has_tokens
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpTo_grammar
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpTo_closed
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpTo_bytes_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpTo_readInput_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationSeenC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsHashed_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeBytesLimited_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeNumericLimited_witness
#print axioms Fang.TptpCandidate.FullFof.Integration.prepareLimited_witness
#print axioms Fang.TptpCandidate.FullFof.Integration.prepareLimited_check_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsLimited_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsLimited_accepted

end Fang.TptpCandidate.FullFof.Integration
