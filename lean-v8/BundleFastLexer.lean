/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The linear lexer and statement splitting of the bundle framer, each proved
   equal to the gated one (`lexLoop` and `tokenize`, `splitStatement`). Moved
   unchanged from `BundleFastFramer` so that a framer can use them without
   importing `BundleReplay`; this module imports only `BundleFramer`. -/
import BundleFramer

namespace Fang.TptpCandidate.FullFof.Coverage.FramerV2

open Fang.TptpCandidate.FullFof.Coverage

/-- Add the piece for one accepted lexer step, if it has one, to the reversed list. -/
def pushPiece (acc : List Piece) (kind : Option FullFof.Kind) (offset count : Nat) (input : List Char) :
    List Piece :=
  match kind with
  | none => acc
  | some kind => .old ⟨kind, offset, offset + count, input.take count⟩ :: acc

/-- `remaining` stands for the length of `input`; `acc` holds the pieces found
    so far, newest first. -/
def fastFrameLexLoop : Nat → List Char → Nat → Nat → List Piece → Except Error (List Piece)
  | 0, _, _, offset, _ => .error ⟨.resource, offset⟩
  | _ + 1, [], _, _, acc => .ok acc.reverse
  | fuel + 1, input@(_ :: _), remaining, offset, acc =>
    match extraPiece offset input with
    | some (.error failure) => .error failure
    | some (.ok (extra, count)) =>
      if count == 0 || remaining < count then .error ⟨.internal, offset⟩
      else fastFrameLexLoop fuel (input.drop count) (remaining - count) (offset + count)
        (.extra extra offset (offset + count) :: acc)
    | none =>
      match FullFof.piece offset input with
      | .error failure => .error failure
      | .ok (kind, count) =>
        if count == 0 || remaining < count then .error ⟨.internal, offset⟩
        else fastFrameLexLoop fuel (input.drop count) (remaining - count) (offset + count)
          (pushPiece acc kind offset count input)

theorem fastFrameLexLoop_eq : ∀ (fuel : Nat) (input : List Char) (offset : Nat) (acc : List Piece),
    fastFrameLexLoop fuel input input.length offset acc =
      (lexLoop fuel input offset).map (fun tail => acc.reverse ++ tail)
  | 0, _, _, _ => rfl
  | _ + 1, [], _, acc => by simp [fastFrameLexLoop, lexLoop, Except.map]
  | fuel + 1, c :: rest, offset, acc => by
    have remaining : ∀ count, (c :: rest).length - count = ((c :: rest).drop count).length :=
      fun count => by rw [List.length_drop]
    cases hx : extraPiece offset (c :: rest) with
    | some result =>
      cases result with
      | error failure => simp [fastFrameLexLoop, lexLoop, hx, Except.map]
      | ok value =>
        obtain ⟨extra, count⟩ := value
        by_cases bad : count = 0 ∨ rest.length + 1 < count
        · simp [fastFrameLexLoop, lexLoop, hx, bad, Except.map]
        · have good : (count == 0 || decide ((c :: rest).length < count)) = false := by simpa using bad
          have step := fastFrameLexLoop_eq fuel ((c :: rest).drop count) (offset + count)
            (.extra extra offset (offset + count) :: acc)
          rw [← remaining] at step
          simp only [fastFrameLexLoop, hx, good, Bool.false_eq_true, ↓reduceIte]
          rw [step]
          simp only [lexLoop, hx, good, Bool.false_eq_true, ↓reduceIte]
          cases lexLoop fuel ((c :: rest).drop count) (offset + count) <;> simp [Except.map]
    | none =>
      cases hp : FullFof.piece offset (c :: rest) with
      | error failure => simp [fastFrameLexLoop, lexLoop, hx, hp, Except.map, bind, Except.bind]
      | ok result =>
        obtain ⟨kind, count⟩ := result
        by_cases bad : count = 0 ∨ rest.length + 1 < count
        · simp [fastFrameLexLoop, lexLoop, hx, hp, bad, bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw, Except.map]
        · have good : (count == 0 || decide ((c :: rest).length < count)) = false := by simpa using bad
          have step := fastFrameLexLoop_eq fuel ((c :: rest).drop count) (offset + count)
            (pushPiece acc kind offset count (c :: rest))
          rw [← remaining] at step
          simp only [fastFrameLexLoop, hx, hp, good, Bool.false_eq_true, ↓reduceIte]
          rw [step]
          simp [lexLoop, hx, hp, bad, bind, Except.bind]
          cases lexLoop fuel ((c :: rest).drop count) (offset + count) with
          | error failure => simp [Except.map]
          | ok pieces => cases kind <;> simp [pushPiece, Except.map, pure, Except.pure]

def tokenizeFast (input : List UInt8) (maximum : Nat) : Except Error (List Piece) :=
  if input.length > maximum then .error ⟨.resource, 0⟩
  else fastFrameLexLoop (input.length + 1) (byteChars input) input.length 0 []

theorem tokenizeFast_eq (input : List UInt8) (maximum : Nat) :
    tokenizeFast input maximum = tokenize input maximum := by
  by_cases large : input.length > maximum
  · simp only [tokenizeFast, tokenize, large, ↓reduceIte]
  · simp only [tokenizeFast, tokenize, large, ↓reduceIte]
    have same : input.length = (byteChars input).length := by simp [byteChars]
    rw [same, fastFrameLexLoop_eq]
    cases lexLoop ((byteChars input).length + 1) (byteChars input) 0 <;> rfl

/-- `splitStatement` with the pieces before the dot collected newest first. -/
def splitStatementFast : Int → List Piece → List Piece → List Piece × List Piece
  | _, acc, [] => (acc.reverse, [])
  | depth, acc, piece :: rest =>
    if piece.isPunct '.' && depth == 0 then ((piece :: acc).reverse, rest)
    else splitStatementFast (depthStep depth piece) (piece :: acc) rest

theorem splitStatementFast_eq : ∀ (depth : Int) (acc input : List Piece),
    splitStatementFast depth acc input = splitStatement depth acc.reverse input
  | _, acc, [] => by simp [splitStatementFast, splitStatement]
  | depth, acc, piece :: rest => by
    by_cases stop : (piece.isPunct '.' && depth == 0) = true
    · simp [splitStatementFast, splitStatement, stop]
    · simp only [splitStatementFast, splitStatement, stop, Bool.false_eq_true, ↓reduceIte]
      rw [splitStatementFast_eq (depthStep depth piece) (piece :: acc) rest, List.reverse_cons]

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.fastFrameLexLoop_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.tokenizeFast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.splitStatementFast_eq

end Fang.TptpCandidate.FullFof.Coverage.FramerV2
