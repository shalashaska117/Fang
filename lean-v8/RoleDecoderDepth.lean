/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Role byte decoders parameterised by declaration count and formula depth. -/
import RoleDeclarationDepth

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

def declarationsUpToD (limit maxDepth : Nat) : Nat → List Name → Nat → List FullFof.Token → Except Error (List Entry)
  | 0, _, endOffset, tokens => FullFof.failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ limit then FullFof.failure .resource endOffset tokens
    let (first, rest) ← declarationD maxDepth seen endOffset tokens
    let tail ← declarationsUpToD limit maxDepth fuel (first.original.name :: seen) endOffset rest
    pure (first :: tail)

theorem declarationsUpToD_sound {limit maxDepth fuel seen endOffset input values}
    (success : declarationsUpToD limit maxDepth fuel seen endOffset input = .ok values) :
    StatementsTokens input values ∧ WellNamed values ∧
      ∀ label ∈ values.map (fun value => value.original.name), label ∉ seen := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpToD, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpToD] at success
      subst values
      exact ⟨.empty, by simp [WellNamed], by simp⟩
    | cons token rest =>
      by_cases large : seen.length ≥ limit
      · simp [declarationsUpToD, large, FullFof.failure, Bind.bind, Except.bind] at success
      · cases firstAt : declarationD maxDepth seen endOffset (token :: rest) with
        | error error => simp [declarationsUpToD, large, firstAt, Bind.bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨first, afterFirst⟩
          cases tailAt : declarationsUpToD limit maxDepth fuel (first.original.name :: seen) endOffset afterFirst with
          | error error => simp [declarationsUpToD, large, firstAt, tailAt, Bind.bind, Except.bind] at success
          | ok more =>
            simp [declarationsUpToD, large, firstAt, tailAt, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
            subst values
            obtain ⟨firstParsed, firstFresh⟩ := declarationD_sound firstAt
            obtain ⟨moreParsed, moreUnique, moreFresh⟩ := ih tailAt
            refine ⟨.cons firstParsed moreParsed, ?_, ?_⟩
            · simp only [WellNamed, List.map_cons, List.nodup_cons] at *
              exact ⟨fun member => moreFresh first.original.name member (by simp), moreUnique⟩
            · intro label member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with rfl | member
              · exact firstFresh
              · exact fun old => moreFresh label member (by simp [old])

theorem declarationsUpToD_closed {limit maxDepth fuel seen endOffset input values}
    (success : declarationsUpToD limit maxDepth fuel seen endOffset input = .ok values) : Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpToD, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpToD] at success
      subst values
      simp [Closed]
    | cons token rest =>
      unfold declarationsUpToD at success
      simp only [FullFof.failure, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact declarationD_closed firstAt
      · exact ih tailAt value member

theorem declarationsUpToD_goals_fof {limit maxDepth fuel seen endOffset input values}
    (success : declarationsUpToD limit maxDepth fuel seen endOffset input = .ok values) : Signed.GoalsFof values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarationsUpToD, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarationsUpToD] at success
      subst values
      simp [Signed.GoalsFof]
    | cons token rest =>
      unfold declarationsUpToD at success
      simp only [FullFof.failure, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member goal
      rcases List.mem_cons.mp member with rfl | member
      · exact declarationD_goal_fof firstAt goal
      · exact ih tailAt value member goal

/-! The counted loop with a declaration counter and a hash set of seen names. -/

def declarationsHashedD (limit maxDepth : Nat) : Nat → Std.HashSet Name → Nat → Nat → List FullFof.Token → Nat →
    Except Error (List Entry)
  | 0, _, _, endOffset, tokens, _ => FullFof.failure .resource endOffset tokens
  | _ + 1, _, _, _, [], _ => .ok []
  | fuel + 1, seen, seenCount, endOffset, tokens@(_ :: _), count => do
    if seenCount ≥ limit then FullFof.failure .resource endOffset tokens
    let (first, rest, restCount) ← declarationSeenCD maxDepth (fun label => seen.contains label) endOffset tokens count
    let tail ← declarationsHashedD limit maxDepth fuel (seen.insert first.original.name) (seenCount + 1) endOffset rest restCount
    pure (first :: tail)

theorem declarationsHashedD_eq (limit maxDepth : Nat) : ∀ fuel (set : Std.HashSet Name) seen seenCount endOffset tokens count,
    (∀ label, set.contains label = seen.contains label) → seenCount = seen.length → count = tokens.length →
    declarationsHashedD limit maxDepth fuel set seenCount endOffset tokens count = declarationsUpToD limit maxDepth fuel seen endOffset tokens
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
      rw [declarationSeenCD_eq members, declarationCD_eq length, Integration.bind_annotate]
      apply Integration.bind_congr_ok
      intro value _
      simp only [Integration.annotate]
      rw [declarationsHashedD_eq limit maxDepth fuel (set.insert value.1.original.name) (value.1.original.name :: seen)
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

def decodeBytesUpToD (limit maxDepth : Nat) (input : List UInt8) (maximumBytes : Nat) : Except Error (List Entry) := do
  let tokens ← FullFof.tokenizeBytes input maximumBytes
  let values ← declarationsUpToD limit maxDepth (tokens.length + 1) [] input.length tokens
  if modesValid values then pure values else FullFof.failure .unsupported input.length []

/-- The role byte decoder with the linear lexer, counted parsing, a declaration counter and a hash set. -/
def decodeBytesLimitedD (limit maxDepth : Nat) (input : List UInt8) (maximumBytes : Nat) : Except Error (List Entry) := do
  let tokens ← Integration.fastTokenizeBytes input maximumBytes
  let values ← declarationsHashedD limit maxDepth (tokens.length + 1) {} 0 input.length tokens tokens.length
  if modesValid values then pure values else FullFof.failure .unsupported input.length []

theorem decodeBytesLimitedD_eq (limit maxDepth : Nat) (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesLimitedD limit maxDepth input maximumBytes = decodeBytesUpToD limit maxDepth input maximumBytes := by
  unfold decodeBytesLimitedD decodeBytesUpToD
  rw [Integration.fastTokenizeBytes_eq]
  apply Integration.bind_congr_ok
  intro tokens _
  rw [declarationsHashedD_eq limit maxDepth _ {} [] 0 input.length tokens tokens.length (by intro label; simp) rfl rfl]

theorem decodeUpToD_has_tokens {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) :
    ∃ tokens, FullFof.tokenizeBytes input maximum = .ok tokens ∧
      declarationsUpToD limit maxDepth (tokens.length + 1) [] input.length tokens = .ok values ∧
      modesValid values = true := by
  unfold decodeBytesUpToD at success
  cases lexical : FullFof.tokenizeBytes input maximum with
  | error reason => simp [lexical, Bind.bind, Except.bind] at success
  | ok tokens =>
    cases parsed : declarationsUpToD limit maxDepth (tokens.length + 1) [] input.length tokens with
    | error reason => simp [lexical, parsed, Bind.bind, Except.bind] at success
    | ok result =>
      by_cases valid : modesValid result = true
      · simp [lexical, parsed, valid, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
        subst values
        exact ⟨tokens, rfl, parsed, valid⟩
      · simp [lexical, parsed, valid, Bind.bind, Except.bind, FullFof.failure] at success

theorem decodeUpToD_grammar {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) : ByteParsed input maximum values := by
  obtain ⟨tokens, lexical, parsed, valid⟩ := decodeUpToD_has_tokens success
  obtain ⟨grammar, unique, _⟩ := declarationsUpToD_sound parsed
  exact ⟨tokens, lexical, grammar, unique, valid⟩

theorem decodeUpToD_closed {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) : Closed values := by
  obtain ⟨_, _, parsed, _⟩ := decodeUpToD_has_tokens success
  exact declarationsUpToD_closed parsed

theorem decodeUpToD_goals_fof {limit maxDepth input maximum values}
    (success : decodeBytesUpToD limit maxDepth input maximum = .ok values) : Signed.GoalsFof values := by
  obtain ⟨_, _, parsed, _⟩ := decodeUpToD_has_tokens success
  exact declarationsUpToD_goals_fof parsed

/-! The byte meanings from a parse, without a decoder. -/

theorem declarationsUpToD_accepted_at (limit : Nat) : ∀ fuel seen endOffset tokens,
    declarationsUpToD limit 64 fuel seen endOffset tokens = declarationsUpTo limit fuel seen endOffset tokens
  | 0, _, _, _ => rfl
  | _ + 1, _, _, [] => rfl
  | fuel + 1, seen, endOffset, token :: rest => by
    unfold declarationsUpToD declarationsUpTo
    rw [declarationD_accepted]
    by_cases full : seen.length ≥ limit
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      apply Integration.bind_congr_ok
      intro value _
      rw [declarationsUpToD_accepted_at limit fuel (value.1.original.name :: seen) endOffset value.2]

theorem decodeBytesUpToD_accepted (limit : Nat) : decodeBytesUpToD limit 64 = decodeBytesUpTo limit := by
  funext input maximumBytes
  unfold decodeBytesUpToD decodeBytesUpTo
  apply Integration.bind_congr_ok
  intro tokens _
  rw [declarationsUpToD_accepted_at]

theorem decodeBytesLimitedD_accepted (limit : Nat) : decodeBytesLimitedD limit 64 = decodeBytesLimited limit := by
  funext input maximumBytes
  rw [decodeBytesLimitedD_eq, decodeBytesLimited_eq, decodeBytesUpToD_accepted]

end Fang.TptpCandidate.Roles.Bytes
