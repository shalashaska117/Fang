/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The signed role decoder with the declaration limit as a parameter. The role loop takes the limit, a declaration counter and a hash set of seen names over the counted decoder's `declarationSeenC`; it is proved equal to the list loop with the same limit, which at 1,000 is the accepted role loop. The byte meaning needs no limit, so the decoder facts and the signed version-8 endpoints are restated for any limit. -/
import SignedLinear
import ExpandedLimitDecoder

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

/-! The role record decoder with a membership test for seen names. -/

/-- `declarationC` with the duplicate test as a parameter. -/
def declarationSeenC (isSeen : Name → Bool) (endOffset : Nat) (tokens : List FullFof.Token) (count : Nat) :
    Except Error (Entry × List FullFof.Token × Nat) := do
  let some header := header? tokens | FullFof.failure .invalid endOffset tokens
  let role ← readRole endOffset header.role
  if invalidGoal header role then FullFof.failure .invalid endOffset tokens
  let (original, rest, restCount) ← Integration.declarationSeenC isSeen endOffset header.patched count
  pure (⟨original, role, header.role.start, header.role.stop⟩, rest, restCount)

theorem declarationSeenC_eq {isSeen : Name → Bool} {seen : List Name} (same : ∀ label, isSeen label = seen.contains label)
    (endOffset : Nat) (tokens : List FullFof.Token) (count : Nat) :
    declarationSeenC isSeen endOffset tokens count = declarationC seen endOffset tokens count := by
  unfold declarationSeenC declarationC
  simp only [Integration.declarationSeenC_eq same]
  rfl

/-! The list loop with the limit as a parameter. -/

def declarationsUpTo (limit : Nat) : Nat → List Name → Nat → List FullFof.Token → Except Error (List Entry)
  | 0, _, endOffset, tokens => FullFof.failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ limit then FullFof.failure .resource endOffset tokens
    let (first, rest) ← declaration seen endOffset tokens
    let tail ← declarationsUpTo limit fuel (first.original.name :: seen) endOffset rest
    pure (first :: tail)

theorem declarationsUpTo_accepted : ∀ fuel seen endOffset tokens,
    declarationsUpTo 1000 fuel seen endOffset tokens = declarations fuel seen endOffset tokens
  | 0, _, _, _ => by
    unfold declarationsUpTo declarations
    rfl
  | _ + 1, _, _, [] => by
    unfold declarationsUpTo declarations
    rfl
  | fuel + 1, seen, endOffset, token :: rest => by
    unfold declarationsUpTo declarations
    by_cases full : seen.length ≥ 1000
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      apply Integration.bind_congr_ok
      intro value _
      rw [declarationsUpTo_accepted fuel (value.1.original.name :: seen) endOffset value.2]

theorem declarationsUpTo_sound {limit fuel seen endOffset input values}
    (success : declarationsUpTo limit fuel seen endOffset input = .ok values) :
    StatementsTokens input values ∧ WellNamed values ∧
      ∀ label ∈ values.map (fun value => value.original.name), label ∉ seen := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpTo, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpTo] at success
      subst values
      exact ⟨.empty, by simp [WellNamed], by simp⟩
    | cons token rest =>
      by_cases large : seen.length ≥ limit
      · simp [declarationsUpTo, large, FullFof.failure, Bind.bind, Except.bind] at success
      · cases firstAt : declaration seen endOffset (token :: rest) with
        | error error => simp [declarationsUpTo, large, firstAt, Bind.bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨first, afterFirst⟩
          cases tailAt : declarationsUpTo limit fuel (first.original.name :: seen) endOffset afterFirst with
          | error error => simp [declarationsUpTo, large, firstAt, tailAt, Bind.bind, Except.bind] at success
          | ok more =>
            simp [declarationsUpTo, large, firstAt, tailAt, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
            subst values
            obtain ⟨firstParsed, firstFresh⟩ := declaration_sound firstAt
            obtain ⟨moreParsed, moreUnique, moreFresh⟩ := ih tailAt
            refine ⟨.cons firstParsed moreParsed, ?_, ?_⟩
            · simp only [WellNamed, List.map_cons, List.nodup_cons] at *
              exact ⟨fun member => moreFresh first.original.name member (by simp), moreUnique⟩
            · intro label member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with rfl | member
              · exact firstFresh
              · exact fun old => moreFresh label member (by simp [old])

theorem declarationsUpTo_closed {limit fuel seen endOffset input values}
    (success : declarationsUpTo limit fuel seen endOffset input = .ok values) : Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpTo, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpTo] at success
      subst values
      simp [Closed]
    | cons token rest =>
      unfold declarationsUpTo at success
      simp only [FullFof.failure, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact declaration_closed firstAt
      · exact ih tailAt value member

theorem declarationsUpTo_goals_fof {limit fuel seen endOffset input values}
    (success : declarationsUpTo limit fuel seen endOffset input = .ok values) : Signed.GoalsFof values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpTo, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpTo] at success
      subst values
      simp [Signed.GoalsFof]
    | cons token rest =>
      unfold declarationsUpTo at success
      simp only [FullFof.failure, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member goal
      rcases List.mem_cons.mp member with rfl | member
      · exact Signed.declaration_goal_fof firstAt goal
      · exact ih tailAt value member goal

/-! The counted loop with a declaration counter and a hash set of seen names. -/

def declarationsHashed (limit : Nat) : Nat → Std.HashSet Name → Nat → Nat → List FullFof.Token → Nat →
    Except Error (List Entry)
  | 0, _, _, endOffset, tokens, _ => FullFof.failure .resource endOffset tokens
  | _ + 1, _, _, _, [], _ => .ok []
  | fuel + 1, seen, seenCount, endOffset, tokens@(_ :: _), count => do
    if seenCount ≥ limit then FullFof.failure .resource endOffset tokens
    let (first, rest, restCount) ← declarationSeenC (fun label => seen.contains label) endOffset tokens count
    let tail ← declarationsHashed limit fuel (seen.insert first.original.name) (seenCount + 1) endOffset rest restCount
    pure (first :: tail)

theorem declarationsHashed_eq (limit : Nat) : ∀ fuel (set : Std.HashSet Name) seen seenCount endOffset tokens count,
    (∀ label, set.contains label = seen.contains label) → seenCount = seen.length → count = tokens.length →
    declarationsHashed limit fuel set seenCount endOffset tokens count = declarationsUpTo limit fuel seen endOffset tokens
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
      rw [declarationSeenC_eq members, declarationC_eq length, Integration.bind_annotate]
      apply Integration.bind_congr_ok
      intro value _
      simp only [Integration.annotate]
      rw [declarationsHashed_eq limit fuel (set.insert value.1.original.name) (value.1.original.name :: seen)
        (seen.length + 1) endOffset value.2 value.2.length (by
          intro label
          rw [Std.HashSet.contains_insert, members, List.contains_cons]
          by_cases same : label = value.1.original.name
          · subst same
            simp
          · have other : value.1.original.name ≠ label := fun reversed => same reversed.symm
            rw [beq_false_of_ne other, beq_false_of_ne same])
        (by simp) rfl]

/-! Byte decoders. -/

def decodeBytesUpTo (limit : Nat) (input : List UInt8) (maximumBytes : Nat) : Except Error (List Entry) := do
  let tokens ← FullFof.tokenizeBytes input maximumBytes
  let values ← declarationsUpTo limit (tokens.length + 1) [] input.length tokens
  if modesValid values then pure values else FullFof.failure .unsupported input.length []

theorem decodeBytesUpTo_accepted (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesUpTo 1000 input maximumBytes = decodeBytes input maximumBytes := by
  unfold decodeBytesUpTo decodeBytes
  apply Integration.bind_congr_ok
  intro tokens _
  rw [declarationsUpTo_accepted]

/-- The role byte decoder with the linear lexer, counted parsing, a declaration counter and a hash set. -/
def decodeBytesLimited (limit : Nat) (input : List UInt8) (maximumBytes : Nat) : Except Error (List Entry) := do
  let tokens ← Integration.fastTokenizeBytes input maximumBytes
  let values ← declarationsHashed limit (tokens.length + 1) {} 0 input.length tokens tokens.length
  if modesValid values then pure values else FullFof.failure .unsupported input.length []

theorem decodeBytesLimited_eq (limit : Nat) (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesLimited limit input maximumBytes = decodeBytesUpTo limit input maximumBytes := by
  unfold decodeBytesLimited decodeBytesUpTo
  rw [Integration.fastTokenizeBytes_eq]
  apply Integration.bind_congr_ok
  intro tokens _
  rw [declarationsHashed_eq limit _ {} [] 0 input.length tokens tokens.length (by intro label; simp) rfl rfl]

theorem decodeUpTo_has_tokens {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) :
    ∃ tokens, FullFof.tokenizeBytes input maximum = .ok tokens ∧
      declarationsUpTo limit (tokens.length + 1) [] input.length tokens = .ok values ∧
      modesValid values = true := by
  unfold decodeBytesUpTo at success
  cases lexical : FullFof.tokenizeBytes input maximum with
  | error reason => simp [lexical, Bind.bind, Except.bind] at success
  | ok tokens =>
    cases parsed : declarationsUpTo limit (tokens.length + 1) [] input.length tokens with
    | error reason => simp [lexical, parsed, Bind.bind, Except.bind] at success
    | ok result =>
      by_cases valid : modesValid result = true
      · simp [lexical, parsed, valid, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
        subst values
        exact ⟨tokens, rfl, parsed, valid⟩
      · simp [lexical, parsed, valid, Bind.bind, Except.bind, FullFof.failure] at success

theorem decodeUpTo_grammar {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) : ByteParsed input maximum values := by
  obtain ⟨tokens, lexical, parsed, valid⟩ := decodeUpTo_has_tokens success
  obtain ⟨grammar, unique, _⟩ := declarationsUpTo_sound parsed
  exact ⟨tokens, lexical, grammar, unique, valid⟩

theorem decodeUpTo_closed {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) : Closed values := by
  obtain ⟨_, _, parsed, _⟩ := decodeUpTo_has_tokens success
  exact declarationsUpTo_closed parsed

theorem decodeUpTo_goals_fof {limit input maximum values}
    (success : decodeBytesUpTo limit input maximum = .ok values) : Signed.GoalsFof values := by
  obtain ⟨_, _, parsed, _⟩ := decodeUpTo_has_tokens success
  exact declarationsUpTo_goals_fof parsed

/-! The byte meanings from a parse, without a decoder. -/

theorem parsed_entails_in {input maximum values} (parsed : ByteParsed input maximum values) (closed : Closed values)
    (D : Type) : BytesEntailsIn input maximum D ↔ Roles.EntailsAll (sentence (D := D)) (source values) := by
  constructor
  · rintro ⟨other, otherParsed, _, entails⟩
    have same := byteParsed_source_unique otherParsed parsed
    simpa only [same] using entails
  · intro entails
    exact ⟨values, parsed, closed, entails⟩

theorem parsed_entails_all {input maximum values} (parsed : ByteParsed input maximum values) (closed : Closed values) :
    BytesEntailsAll input maximum ↔
      ∀ (D : Type) (_ : Nonempty D), Roles.EntailsAll (sentence (D := D)) (source values) := by
  constructor
  · intro entails D inhabited
    exact (parsed_entails_in parsed closed D).mp (entails D inhabited)
  · intro entails D inhabited
    exact (parsed_entails_in parsed closed D).mpr (entails D inhabited)

theorem parsed_inputs_satisfiable {input maximum values} (parsed : ByteParsed input maximum values)
    (closed : Closed values) (noGoals : Roles.goals (source values) = []) :
    BytesInputsSatisfiable input maximum ↔
      ∃ (D : Type) (_ : Nonempty D), Roles.SatisfiableInputs (sentence (D := D)) (source values) := by
  constructor
  · rintro ⟨other, otherParsed, _, _, models⟩
    have same := byteParsed_source_unique otherParsed parsed
    simpa only [same] using models
  · intro models
    exact ⟨values, parsed, closed, noGoals, models⟩

end Fang.TptpCandidate.Roles.Bytes

namespace Fang.TptpCandidate.Roles.Signed
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-! Signed entries over the limited decoder. -/

def decodeSignedLimited (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) :
    Except SignedError (List Bytes.Entry × SignedInput) := do
  let values ← (Bytes.decodeBytesLimited limit bytes maximumBytes).mapError .input
  match readSigned values with
  | none => .error .nonliteral
  | some input => .ok (values, input)

theorem decodeSignedLimited_witness {limit bytes maximumBytes values input}
    (success : decodeSignedLimited limit bytes maximumBytes = .ok (values, input)) :
    Bytes.decodeBytesUpTo limit bytes maximumBytes = .ok values ∧ readSigned values = some input := by
  obtain ⟨decodedValues, decoded, success⟩ := bind_success success
  rw [Bytes.decodeBytesLimited_eq] at decoded
  cases read : readSigned decodedValues with
  | none => simp [read] at success
  | some result =>
    have same : (decodedValues, result) = (values, input) := Except.ok.inj (by simpa only [read] using success)
    cases same
    exact ⟨mapError_success decoded, read⟩

def prepareGoalLimited (limit : Nat) (bytes : List UInt8) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) : Except SignedError GoalPrepared := do
  let (_, input) ← decodeSignedLimited limit bytes maximumBytes
  let some (before, goal, after) := (goalSplits input)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← replayTask input task limits maximumPredicates maximumLiterals
  pure ⟨goal.declaration, replay⟩

def prepareInputsLimited (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except SignedError SignedPrepared := do
  let decoded ← decodeSignedLimited limit bytes maximumBytes
  if (goalSplits decoded.2).isEmpty then
    replayTask decoded.2 (inputsTask decoded.2) limits maximumPredicates maximumLiterals
  else .error .goalsPresent

theorem prepareGoalLimited_witness {limit bytes maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoalLimited limit bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ values input before goal after task,
      Bytes.decodeBytesUpTo limit bytes maximumBytes = .ok values ∧ readSigned values = some input ∧
      (goalSplits input)[index]? = some (before, goal, after) ∧
      goalTask before goal after = some task ∧
      replayTask input task limits maximumPredicates maximumLiterals = .ok prepared.replay ∧
      prepared.goal = goal.declaration := by
  obtain ⟨⟨values, input⟩, decoded, success⟩ := bind_success success
  obtain ⟨decodedRun, read⟩ := decodeSignedLimited_witness decoded
  cases selected : (goalSplits input)[index]? with
  | none => simp [selected] at success
  | some split =>
    obtain ⟨before, goal, after⟩ := split
    cases built : goalTask before goal after with
    | none => simp [selected, built] at success
    | some task =>
      simp only [selected, built] at success
      obtain ⟨replay, replayRun, success⟩ := bind_success success
      cases Except.ok.inj success
      exact ⟨values, input, before, goal, after, task, decodedRun, read, selected, built, replayRun, rfl⟩

/-- Checker acceptance on the task for one goal proves that the original premises entail that goal. -/
theorem prepareGoalLimited_check_entails {limit bytes maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoalLimited limit bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
      prepared.goal ∈ Roles.goals (Bytes.source values) ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
          Bytes.sentence model prepared.goal.original := by
  obtain ⟨values, input, before, goal, after, task, decoded, read, selected, built, replayRun, goalSame⟩ :=
    prepareGoalLimited_witness success
  obtain ⟨split, role⟩ := goalSplits_member (List.mem_of_getElem? selected)
  have closed := Bytes.decodeUpTo_closed decoded
  have unsat := replayTask_check_unsat read (goalTask_fromRows split built) replayRun certificate accepted
  obtain ⟨_, _, _, sources⟩ := readSigned_exact read
  refine ⟨values, Bytes.decodeUpTo_grammar decoded, closed, ?_, ?_⟩
  · rw [goalSame, ← sources, split]
    exact Roles.goal_member.mpr ⟨List.mem_map_of_mem (f := RoleRow.declaration) (by simp), role⟩
  · rw [goalSame]
    exact goalTask_refuted_entails read closed split built unsat

/-- Ordered checker acceptance on the no-goal task proves that the accepted positive inputs are unsatisfiable. -/
theorem prepareInputsLimited_check_unsat {limit bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareInputsLimited limit bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨⟨values, input⟩, decodedRun, success⟩ := bind_success success
  obtain ⟨decoded, read⟩ := decodeSignedLimited_witness decodedRun
  split at success
  · rename_i empty
    have noGoals : Roles.goals (Bytes.source values) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro goal member
      obtain ⟨before, row, after, split, role, rfl⟩ := goal_row read member
      have inside : (before, row, after) ∈ goalSplits input := by
        simp only [goalSplits, List.mem_filter, decide_eq_true_eq]
        exact ⟨mem_splits.mpr split, role⟩
      rw [List.isEmpty_iff.mp empty] at inside
      cases inside
    have closed := Bytes.decodeUpTo_closed decoded
    rw [Bytes.parsed_inputs_satisfiable (Bytes.decodeUpTo_grammar decoded) closed noGoals]
    rintro ⟨D, inhabited, model, holds⟩
    exact replayTask_check_unsat read (inputsTask_fromRows input) success certificate accepted
      ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates,
        (inputsTask_models read closed (model_toNumeric model _ _)).mpr holds⟩
  · cases success

/-! Version-8 acceptance over the limited decoder. -/

def acceptsGoalLimited (limit : Nat) (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except SignedAcceptError Unit := do
  let prepared ← (prepareGoalLimited limit bytes maximumBytes index limits maximumPredicates maximumLiterals).mapError
    .replay
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate

def acceptsInputsLimited (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except SignedAcceptError Unit := do
  let prepared ← (prepareInputsLimited limit bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities
    prepared.predicateArities proof).mapError .certificate

theorem acceptsGoalLimited_replay {limit bytes maximumBytes index proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsGoalLimited limit bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalLimited limit bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      ∃ parsed, Fang.Equality.Ordered.check prepared.replay.problem parsed = .ok () := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact ⟨prepared, mapError_success run, parsed, refuted⟩

/-- Acceptance of one goal's certificate proves that the original premises entail that original conjecture. -/
theorem acceptsGoalLimited_entails {limit bytes maximumBytes index proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsGoalLimited limit bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalLimited limit bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
        prepared.goal ∈ Roles.goals (Bytes.source values) ∧
        ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
            Bytes.sentence model prepared.goal.original := by
  obtain ⟨prepared, run, parsed, refuted⟩ := acceptsGoalLimited_replay accepted
  exact ⟨prepared, run, prepareGoalLimited_check_entails run parsed refuted⟩

/-- Theorem endpoint over the limited decoder: at least one original conjecture, and an accepted certificate for each one. -/
theorem acceptsGoalsLimited_theorem {limit bytes maximumBytes values limits maximumPredicates maximumLiterals}
    (decoded : Bytes.decodeBytesLimited limit bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (accepted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared proof,
      prepareGoalLimited limit bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      prepared.goal = goal ∧
      acceptsGoalLimited limit bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    BytesTheorem bytes maximumBytes := by
  rw [Bytes.decodeBytesLimited_eq] at decoded
  have parsed := Bytes.decodeUpTo_grammar decoded
  have closed := Bytes.decodeUpTo_closed decoded
  refine ⟨values, parsed, closed, nonempty, ?_⟩
  intro D inhabited goal member model premisesHold
  obtain ⟨index, prepared, proof, run, same, checked⟩ := accepted goal member
  obtain ⟨other, otherRun, certificate, refuted⟩ := acceptsGoalLimited_replay checked
  have equal : other = prepared := Except.ok.inj (otherRun.symm.trans run)
  subst equal
  obtain ⟨otherValues, otherParsed, _, _, entails⟩ := prepareGoalLimited_check_entails run certificate refuted
  have sources := Bytes.byteParsed_source_unique otherParsed parsed
  rw [sources, same] at entails
  exact entails D inhabited model premisesHold

/-- Acceptance of the no-goal task's certificate proves that the accepted positive inputs are unsatisfiable. -/
theorem acceptsInputsLimited_unsat {limit bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputsLimited limit bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputsLimited_check_unsat (mapError_success run) parsed refuted

end Fang.TptpCandidate.Roles.Signed

#print axioms Fang.TptpCandidate.Roles.Bytes.declarationSeenC_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpTo_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpTo_sound
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpTo_closed
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpTo_goals_fof
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeBytesUpTo_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeBytesLimited_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpTo_has_tokens
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpTo_grammar
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpTo_closed
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpTo_goals_fof
#print axioms Fang.TptpCandidate.Roles.Bytes.parsed_entails_in
#print axioms Fang.TptpCandidate.Roles.Bytes.parsed_entails_all
#print axioms Fang.TptpCandidate.Roles.Bytes.parsed_inputs_satisfiable
#print axioms Fang.TptpCandidate.Roles.Signed.decodeSignedLimited_witness
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoalLimited_witness
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoalLimited_check_entails
#print axioms Fang.TptpCandidate.Roles.Signed.prepareInputsLimited_check_unsat
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalLimited_replay
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalLimited_entails
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalsLimited_theorem
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsInputsLimited_unsat
