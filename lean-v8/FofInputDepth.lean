/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The formula parsers of `FofInput` with the formula height bound as a parameter (option A of
   `roles/bundle/PREMISE-REPLAY.md`). `maxDepth` replaces 64 in the unit depth test, in the height test of
   `checked` (`depth + body.height - 1 > maxDepth`) and in the binder test (`names.length + depth > maxDepth`).
   Term depth stays 64: `term`, `arguments` and `atom` are the accepted ones. Each parser is proved equal to the
   accepted one at 64. -/
import ExpandedFofInput

namespace Fang.TptpCandidate.FullFof

def checkedAt (maxDepth depth endOffset : Nat) (original : List Token) (body : Formula) (rest : List Token) :
    Except Error (Formula × List Token) :=
  if depth + body.height - 1 > maxDepth then failure .resource endOffset original
  else .ok (body, rest)

mutual
def unitAt (maxDepth : Nat) : Nat → Nat → List String → Nat → List Token → Except Error (Formula × List Token)
  | 0, _, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens => do
    if depth > maxDepth then failure .resource endOffset tokens
    let token :: rest := tokens | failure .invalid endOffset tokens
    match token.kind with
    | .legacy .truth => pure (.truth, rest)
    | .legacy .falsity => pure (.falsity, rest)
    | .legacy (.punctuation '~') =>
      let (body, final) ← unitAt maxDepth fuel (depth + 1) bound endOffset rest
      checkedAt maxDepth depth endOffset tokens (.neg body) final
    | .legacy (.punctuation '(') =>
      let (body, tail) ← formulaAt maxDepth fuel (depth + 1) bound endOffset rest
      let (_, final) ← expect ')' endOffset tail
      pure (body, final)
    | .legacy (.punctuation '!') | .legacy (.punctuation '?') =>
      let (_, tail) ← expect '[' endOffset rest
      let (names, tail) ← binders (tokens.length + 1) endOffset tail
      if names.length + depth > maxDepth then failure .resource endOffset tokens
      let (_, tail) ← expect ']' endOffset tail
      let (_, tail) ← expect ':' endOffset tail
      let (body, final) ← unitAt maxDepth fuel (depth + names.length) (names ++ bound) endOffset tail
      checkedAt maxDepth depth endOffset tokens (close (token.kind == .legacy (.punctuation '!')) names body) final
    | .legacy (.integer _) => failure .unsupported endOffset tokens
    | _ =>
      let (body, rest) ← atom (2 * tokens.length + 1) (some bound) endOffset tokens
      checkedAt maxDepth depth endOffset tokens body rest

def formulaAt (maxDepth : Nat) : Nat → Nat → List String → Nat → List Token → Except Error (Formula × List Token)
  | 0, _, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens => do
    let (left, rest) ← unitAt maxDepth fuel depth bound endOffset tokens
    match rest with
    | [] => pure (left, rest)
    | next :: _ =>
      match binary next.kind with
      | none => pure (left, rest)
      | some operator => chainAt maxDepth fuel depth bound endOffset operator left rest

def chainAt (maxDepth : Nat) : Nat → Nat → List String → Nat → Binary → Formula → List Token →
    Except Error (Formula × List Token)
  | 0, _, _, endOffset, _, _, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, operator, left, tokens => do
    let next :: rest := tokens | failure .invalid endOffset tokens
    if binary next.kind != some operator then failure .internal endOffset tokens
    let (right, tail) ← unitAt maxDepth fuel (depth + operator.extra) bound endOffset rest
    let body := Formula.pair operator left right
    let (_, _) ← checkedAt maxDepth depth endOffset tokens body tail
    if operator.associative && tail.head?.bind (binary ∘ Token.kind) == some operator then
      chainAt maxDepth fuel depth bound endOffset operator body tail
    else pure (body, tail)
end

theorem checkedAt_accepted : checkedAt 64 = checked := rfl

theorem unit_formula_chain_at_accepted : ∀ fuel : Nat,
    (∀ depth bound endOffset tokens, unitAt 64 fuel depth bound endOffset tokens = unit fuel depth bound endOffset tokens) ∧
    (∀ depth bound endOffset tokens,
      formulaAt 64 fuel depth bound endOffset tokens = formula fuel depth bound endOffset tokens) ∧
    (∀ depth bound endOffset operator left tokens,
      chainAt 64 fuel depth bound endOffset operator left tokens =
        chain fuel depth bound endOffset operator left tokens)
  | 0 => ⟨fun _ _ _ _ => by unfold unitAt unit; rfl, fun _ _ _ _ => by unfold formulaAt formula; rfl,
      fun _ _ _ _ _ _ => by unfold chainAt chain; rfl⟩
  | fuel + 1 => by
    obtain ⟨units, formulas, chains⟩ := unit_formula_chain_at_accepted fuel
    refine ⟨fun depth bound endOffset tokens => ?_, fun depth bound endOffset tokens => ?_,
      fun depth bound endOffset operator left tokens => ?_⟩
    · unfold unitAt unit
      simp only [units, formulas, checkedAt_accepted]
      rfl
    · unfold formulaAt formula
      simp only [units, chains]
      rfl
    · unfold chainAt chain
      simp only [units, chains, checkedAt_accepted]
      rfl

theorem unitAt_accepted : unitAt 64 = unit := by
  funext fuel depth bound endOffset tokens
  exact (unit_formula_chain_at_accepted fuel).1 depth bound endOffset tokens

theorem formulaAt_accepted : formulaAt 64 = formula := by
  funext fuel depth bound endOffset tokens
  exact (unit_formula_chain_at_accepted fuel).2.1 depth bound endOffset tokens

theorem chainAt_accepted : chainAt 64 = chain := by
  funext fuel depth bound endOffset operator left tokens
  exact (unit_formula_chain_at_accepted fuel).2.2 depth bound endOffset operator left tokens

#print axioms Fang.TptpCandidate.FullFof.checkedAt_accepted
#print axioms Fang.TptpCandidate.FullFof.unit_formula_chain_at_accepted
#print axioms Fang.TptpCandidate.FullFof.unitAt_accepted
#print axioms Fang.TptpCandidate.FullFof.formulaAt_accepted
#print axioms Fang.TptpCandidate.FullFof.chainAt_accepted

end Fang.TptpCandidate.FullFof
