/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The version-8 checker with the declaration limit and the formula height bound
   as parameters (option A of `roles/bundle/PREMISE-REPLAY.md`). Each definition
   is the one of `ExpandedLimitDecoder` with `CnfBoolean.declarationD maxDepth`
   or `declarationSeenCD maxDepth` in place of the record decoder at 64. The
   loop is sound for every bound, the hashed loop equals the list loop, the
   endpoint is restated, and at 64 every definition is today's. -/
import ExpandedLimitDecoder
import ExpandedDecoderDepth

namespace Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-! The declaration loop with both bounds as parameters. -/

def declarationsUpToD (limit maxDepth : Nat) : Nat → List Name → Nat → List Token → Except Error (List Declaration)
  | 0, _, endOffset, tokens => failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ limit then failure .resource endOffset tokens
    let (first, rest) ← CnfBoolean.declarationD maxDepth seen endOffset tokens
    let tail ← declarationsUpToD limit maxDepth fuel (first.name :: seen) endOffset rest
    pure (first :: tail)

theorem declarationsUpToD_accepted_at (limit : Nat) : ∀ fuel seen endOffset tokens,
    declarationsUpToD limit 64 fuel seen endOffset tokens = declarationsUpTo limit fuel seen endOffset tokens
  | 0, _, _, _ => by
    unfold declarationsUpToD declarationsUpTo
    rfl
  | _ + 1, _, _, [] => by
    unfold declarationsUpToD declarationsUpTo
    rfl
  | fuel + 1, seen, endOffset, token :: rest => by
    unfold declarationsUpToD declarationsUpTo
    rw [CnfBoolean.declarationD_accepted]
    by_cases full : seen.length ≥ limit
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      apply bind_congr_ok
      intro value _
      rw [declarationsUpToD_accepted_at limit fuel (value.1.name :: seen) endOffset value.2]

theorem declarationsUpToD_accepted (limit : Nat) : declarationsUpToD limit 64 = declarationsUpTo limit := by
  funext fuel seen endOffset tokens
  exact declarationsUpToD_accepted_at limit fuel seen endOffset tokens

theorem declarationsUpToD_sound {limit maxDepth fuel seen endOffset input values}
    (success : declarationsUpToD limit maxDepth fuel seen endOffset input = .ok values) :
    CnfBoolean.StatementsTokens input values ∧ Grammar.WellNamed values ∧
      ∀ label ∈ values.map Declaration.name, label ∉ seen := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpToD, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpToD] at success
      subst values
      exact ⟨.empty, by simp [Grammar.WellNamed], by simp⟩
    | cons token rest =>
      by_cases large : seen.length ≥ limit
      · simp [declarationsUpToD, large, failure, bind, Except.bind] at success
      · cases firstAt : CnfBoolean.declarationD maxDepth seen endOffset (token :: rest) with
        | error error => simp [declarationsUpToD, large, firstAt, bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨first, afterFirst⟩
          cases tailAt : declarationsUpToD limit maxDepth fuel (first.name :: seen) endOffset afterFirst with
          | error error => simp [declarationsUpToD, large, firstAt, tailAt, bind, Except.bind] at success
          | ok more =>
            simp [declarationsUpToD, large, firstAt, tailAt, bind, Except.bind, pure, Except.pure] at success
            subst values
            obtain ⟨firstParsed, firstFresh⟩ := CnfBoolean.declarationD_sound firstAt
            obtain ⟨moreParsed, moreUnique, moreFresh⟩ := ih tailAt
            refine ⟨.cons firstParsed moreParsed, ?_, ?_⟩
            · simp only [Grammar.WellNamed, List.map_cons, List.nodup_cons] at *
              exact ⟨fun member => moreFresh first.name member (by simp), moreUnique⟩
            · intro label member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with rfl | member
              · exact firstFresh
              · exact fun old => moreFresh label member (by simp [old])

theorem declarationsUpToD_closed {limit maxDepth fuel seen endOffset input values}
    (success : declarationsUpToD limit maxDepth fuel seen endOffset input = .ok values) : Grammar.Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpToD, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpToD] at success
      subst values
      simp [Grammar.Closed]
    | cons token rest =>
      unfold declarationsUpToD at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact CnfBoolean.declarationD_closed firstAt
      · exact ih tailAt value member

/-! Bytes, grammar and models. -/

def decodeBytesUpToD (limit maxDepth : Nat) (input : List UInt8) (maximumBytes : Nat) :
    Except Error (List Declaration) := do
  let tokens ← tokenizeBytes input maximumBytes
  declarationsUpToD limit maxDepth (tokens.length + 1) [] input.length tokens

theorem decodeBytesUpToD_accepted (limit : Nat) : decodeBytesUpToD limit 64 = decodeBytesUpTo limit := by
  funext input maximumBytes
  unfold decodeBytesUpToD decodeBytesUpTo
  rw [declarationsUpToD_accepted]

theorem decodeUpToD_has_tokens {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) :
    ∃ tokens, tokenizeBytes input maximum = .ok tokens ∧
      declarationsUpToD limit maxDepth (tokens.length + 1) [] input.length tokens = .ok values := by
  unfold decodeBytesUpToD at success
  cases lexical : tokenizeBytes input maximum with
  | error reason => simp [lexical, bind, Except.bind] at success
  | ok tokens => exact ⟨tokens, rfl, by simpa [lexical, bind, Except.bind] using success⟩

theorem decodeUpToD_grammar {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) :
    CnfBoolean.ByteParsed input maximum values := by
  obtain ⟨tokens, lexical, parsed⟩ := decodeUpToD_has_tokens success
  obtain ⟨grammar, unique, _⟩ := declarationsUpToD_sound parsed
  exact ⟨tokens, lexical, grammar, unique⟩

theorem decodeUpToD_closed {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) : Grammar.Closed values := by
  obtain ⟨tokens, _, parsed⟩ := decodeUpToD_has_tokens success
  exact declarationsUpToD_closed parsed

theorem decodeUpToD_bytes_satisfiable {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) :
    CnfBoolean.BytesSatisfiable input maximum ↔ Satisfiable (source values) := by
  have models {D : Type} (model : Source.Interpretation D) :
      CnfBoolean.BytesModels input maximum model ↔ Models (source values) model := by
    constructor
    · rintro ⟨other, parsed, _, holds⟩
      have same := CnfBoolean.byteParsed_source_unique parsed (decodeUpToD_grammar success)
      simpa only [same] using holds
    · intro holds
      exact ⟨values, decodeUpToD_grammar success, decodeUpToD_closed success, holds⟩
  constructor
  · rintro ⟨domain, inhabited, model, holds⟩
    exact ⟨domain, inhabited, model, (models model).mp holds⟩
  · rintro ⟨domain, inhabited, model, holds⟩
    exact ⟨domain, inhabited, model, (models model).mpr holds⟩

theorem decodeUpToD_readInput_unsat {limit maxDepth bytes maximum values input}
    (decoded : decodeBytesUpToD limit maxDepth bytes maximum = .ok values)
    (encoded : readInput values = some input) (refuted : ¬ input.Satisfiable) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximum :=
  fun model => refuted (((decodeUpToD_bytes_satisfiable decoded).trans
    (readInput_satisfiable encoded (decodeUpToD_closed decoded))).mp model)

/-! The counted decoder with a declaration counter and a hash set of seen names. -/

def declarationsHashedD (limit maxDepth : Nat) : Nat → Std.HashSet Name → Nat → Nat → List Token → Nat →
    Except Error (List Declaration)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | _ + 1, _, _, _, [], _ => .ok []
  | fuel + 1, seen, seenCount, endOffset, tokens@(_ :: _), count => do
    if seenCount ≥ limit then failure .resource endOffset tokens
    let (first, rest, restCount) ← declarationSeenCD maxDepth (fun label => seen.contains label) endOffset tokens count
    let tail ← declarationsHashedD limit maxDepth fuel (seen.insert first.name) (seenCount + 1) endOffset rest restCount
    pure (first :: tail)

theorem declarationsHashedD_eq (limit maxDepth : Nat) :
    ∀ fuel (set : Std.HashSet Name) seen seenCount endOffset tokens count,
    (∀ label, set.contains label = seen.contains label) → seenCount = seen.length → count = tokens.length →
    declarationsHashedD limit maxDepth fuel set seenCount endOffset tokens count =
      declarationsUpToD limit maxDepth fuel seen endOffset tokens
  | 0, _, _, _, _, _, _, _, _, _ => by
    unfold declarationsHashedD declarationsUpToD
    rfl
  | _ + 1, _, _, _, _, [], _, _, _, _ => by
    unfold declarationsHashedD declarationsUpToD
    rfl
  | fuel + 1, set, seen, seenCount, endOffset, token :: rest, count, members, counted, length => by
    subst counted
    unfold declarationsHashedD declarationsUpToD
    by_cases full : seen.length ≥ limit
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      rw [declarationSeenCD_eq members, declarationCD_eq length, bind_annotate]
      apply bind_congr_ok
      intro value _
      simp only [annotate]
      rw [declarationsHashedD_eq limit maxDepth fuel (set.insert value.1.name) (value.1.name :: seen)
        (seen.length + 1) endOffset value.2 value.2.length (by
          intro label
          rw [Std.HashSet.contains_insert, members, List.contains_cons]
          by_cases same : label = value.1.name
          · subst same
            simp
          · have other : value.1.name ≠ label := fun reversed => same reversed.symm
            rw [beq_false_of_ne other, beq_false_of_ne same])
        (by simp) rfl]

/-- Both bounds as parameters, with the linear lexer, the counted parsers, a
    declaration counter and a hash set of seen names. -/
def decodeBytesLimitedD (limit maxDepth : Nat) (input : List UInt8) (maximumBytes : Nat) :
    Except Error (List Declaration) :=
  (fastTokenizeBytes input maximumBytes).bind fun tokens =>
    declarationsHashedD limit maxDepth (tokens.length + 1) {} 0 input.length tokens tokens.length

theorem decodeBytesLimitedD_eq (limit maxDepth : Nat) (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesLimitedD limit maxDepth input maximumBytes = decodeBytesUpToD limit maxDepth input maximumBytes := by
  unfold decodeBytesLimitedD decodeBytesUpToD
  rw [fastTokenizeBytes_eq]
  cases tokenizeBytes input maximumBytes with
  | error error => rfl
  | ok tokens =>
    exact declarationsHashedD_eq limit maxDepth _ {} [] 0 input.length tokens tokens.length
      (by intro label; simp) rfl rfl

/-! The checker with both bounds as parameters. -/

def decodeNumericLimitedD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) :
    Except ReplayError NumericInput := do
  let source ← (decodeBytesLimitedD limit maxDepth bytes maximumBytes).mapError .input
  match readInput source with
  | none => .error .nonliteral
  | some input => .ok input

theorem decodeNumericLimitedD_witness {limit maxDepth bytes maximum input}
    (success : decodeNumericLimitedD limit maxDepth bytes maximum = .ok input) :
    ∃ values, decodeBytesUpToD limit maxDepth bytes maximum = .ok values ∧ readInput values = some input := by
  obtain ⟨values, decoded, success⟩ := bind_success success
  cases encoded : readInput values with
  | none => simp [encoded] at success
  | some result =>
    have same : result = input := Except.ok.inj (by simpa only [encoded] using success)
    subst input
    exact ⟨values, by rw [← decodeBytesLimitedD_eq]; exact mapError_success decoded, encoded⟩

def prepareLimitedD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except ReplayError ReplayPrepared := do
  let numeric ← decodeNumericLimitedD limit maxDepth bytes maximumBytes
  let encoded ← (transport numeric maximumPredicates).mapError .transport
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble numeric.declarations blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨numeric, equality, transformed.signature.functions.val.map (fun value => value.val),
    numeric.predicates.map Prod.snd⟩

theorem prepareLimitedD_witness {limit maxDepth bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareLimitedD limit maxDepth bytes maximumBytes limits maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ values encoded transformed blocks ordinary,
      decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧
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
  obtain ⟨values, parsed, numericRun⟩ := decodeNumericLimitedD_witness decoded
  exact ⟨values, encoded, transformed, blocks, ordinary, parsed, numericRun,
    mapError_success inputRun, FangOriginalReplay.observe_success (mapError_success skolemRun),
    FangOriginalReplay.replayBlocks_steps (mapError_success blocksRun),
    FangOriginalReplay.assemble_layout (mapError_success assemblyRun),
    FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_success conversionRun)⟩

/-- Acceptance of the prepared problem excludes every original byte model, for every pair of bounds. -/
theorem prepareLimitedD_check_original_unsat {limit maxDepth bytes maximumBytes limits maximumPredicates
    maximumLiterals prepared}
    (success : prepareLimitedD limit maxDepth bytes maximumBytes limits maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨values, encoded, transformed, blocks, ordinary, decoded, numericRun,
    inputRun, skolemRun, steps, layout, converted⟩ := prepareLimitedD_witness success
  apply decodeUpToD_readInput_unsat decoded numericRun
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

/-- The native entry with both bounds as parameters. Same envelope and checker as `acceptsLimited`. -/
def acceptsLimitedD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareLimitedD limit maxDepth bytes maximumBytes limits maximumPredicates
    maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

/-- Acceptance proves that the original bytes have no model, for every pair of bounds. -/
theorem acceptsLimitedD_original_unsat {limit maxDepth bytes maximumBytes proof limits maximumPredicates
    maximumLiterals}
    (accepted : acceptsLimitedD limit maxDepth bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  exact prepareLimitedD_check_original_unsat (mapError_success replayRun) parsed refuted

/-- At the height bound 64 the entry is `acceptsLimited`. -/
theorem acceptsLimitedD_accepted (limit : Nat) : acceptsLimitedD limit 64 = acceptsLimited limit := by
  have decoded : decodeNumericLimitedD limit 64 = decodeNumericLimited limit := by
    funext bytes maximumBytes
    unfold decodeNumericLimitedD decodeNumericLimited
    rw [decodeBytesLimitedD_eq, decodeBytesLimited_eq, decodeBytesUpToD_accepted]
    rfl
  funext bytes maximumBytes proof limits maximumPredicates maximumLiterals
  unfold acceptsLimitedD acceptsLimited prepareLimitedD prepareLimited
  rw [decoded]

#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpToD_accepted_at
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpToD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpToD_sound
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsUpToD_closed
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeBytesUpToD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpToD_has_tokens
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpToD_grammar
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpToD_closed
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpToD_bytes_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeUpToD_readInput_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsHashedD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeBytesLimitedD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeNumericLimitedD_witness
#print axioms Fang.TptpCandidate.FullFof.Integration.prepareLimitedD_witness
#print axioms Fang.TptpCandidate.FullFof.Integration.prepareLimitedD_check_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsLimitedD_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsLimitedD_accepted

end Fang.TptpCandidate.FullFof.Integration
