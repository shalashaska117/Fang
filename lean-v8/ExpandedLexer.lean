/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A tail-recursive form of the accepted byte lexer. It calls the same `piece`,
   keeps the remaining length as a counter instead of recomputing it, and
   accumulates tokens in reverse. It returns exactly what `tokenizeBytes` returns. -/
import FofLexer

namespace Fang.TptpCandidate.FullFof.Integration

/-- Add the token for one lexer piece, if it has one, to the reversed list. -/
def pushToken (acc : List FullFof.Token) (kind : Option FullFof.Kind) (offset count : Nat)
    (input : List Char) : List FullFof.Token :=
  match kind with
  | none => acc
  | some kind => ⟨kind, offset, offset + count, input.take count⟩ :: acc

/-- `remaining` stands for the length of `input`; `acc` holds the tokens found so
    far, newest first. -/
def fastLexLoop : Nat → List Char → Nat → Nat → List FullFof.Token →
    Except Fang.TptpCandidate.Error (List FullFof.Token)
  | 0, _, _, offset, _ => .error ⟨.resource, offset⟩
  | _ + 1, [], _, _, acc => .ok acc.reverse
  | fuel + 1, input@(_ :: _), remaining, offset, acc =>
    match FullFof.piece offset input with
    | .error error => .error error
    | .ok (kind, count) =>
      if count == 0 || remaining < count then .error ⟨.internal, offset⟩
      else
        fastLexLoop fuel (input.drop count) (remaining - count) (offset + count)
          (pushToken acc kind offset count input)

def fastTokenizeBytes (input : List UInt8) (maximumBytes : Nat := 1048576) :
    Except Fang.TptpCandidate.Error (List FullFof.Token) :=
  if input.length > maximumBytes then .error ⟨.resource, 0⟩
  else fastLexLoop (input.length + 1) (Fang.TptpCandidate.byteChars input) input.length 0 []

theorem fastLexLoop_eq : ∀ (fuel : Nat) (input : List Char) (offset : Nat) (acc : List FullFof.Token),
    fastLexLoop fuel input input.length offset acc =
      (FullFof.lexLoop fuel input offset).map (fun tail => acc.reverse ++ tail)
  | 0, _, _, _ => rfl
  | _ + 1, [], _, acc => by simp [fastLexLoop, FullFof.lexLoop, Except.map]
  | fuel + 1, c :: rest, offset, acc => by
    cases hp : FullFof.piece offset (c :: rest) with
    | error error =>
      simp [fastLexLoop, FullFof.lexLoop, hp, Except.map, bind, Except.bind]
    | ok result =>
      obtain ⟨kind, count⟩ := result
      by_cases bad : count = 0 ∨ rest.length + 1 < count
      · simp [fastLexLoop, FullFof.lexLoop, hp, bad, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
          Except.map]
      · have good : (count == 0 || decide ((c :: rest).length < count)) = false := by simpa using bad
        have remaining : (c :: rest).length - count = ((c :: rest).drop count).length := by
          rw [List.length_drop]
        have step := fastLexLoop_eq fuel ((c :: rest).drop count) (offset + count)
          (pushToken acc kind offset count (c :: rest))
        rw [← remaining] at step
        simp only [fastLexLoop, hp, good, Bool.false_eq_true, ↓reduceIte]
        rw [step]
        simp [FullFof.lexLoop, hp, bad, bind, Except.bind]
        cases tail : FullFof.lexLoop fuel ((c :: rest).drop count) (offset + count) with
        | error error => simp [Except.map]
        | ok tokens => cases kind <;> simp [pushToken, Except.map, pure, Except.pure]

theorem fastTokenizeBytes_eq (input : List UInt8) (maximumBytes : Nat) :
    fastTokenizeBytes input maximumBytes = FullFof.tokenizeBytes input maximumBytes := by
  by_cases large : input.length > maximumBytes
  · simp only [fastTokenizeBytes, FullFof.tokenizeBytes, large, ↓reduceIte]
  · simp only [fastTokenizeBytes, FullFof.tokenizeBytes, large, ↓reduceIte]
    have same : input.length = (Fang.TptpCandidate.byteChars input).length := by
      simp [Fang.TptpCandidate.byteChars]
    rw [same, fastLexLoop_eq]
    cases FullFof.lexLoop ((Fang.TptpCandidate.byteChars input).length + 1)
      (Fang.TptpCandidate.byteChars input) 0 <;> rfl

#print axioms Fang.TptpCandidate.FullFof.Integration.fastLexLoop_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.fastTokenizeBytes_eq

end Fang.TptpCandidate.FullFof.Integration
