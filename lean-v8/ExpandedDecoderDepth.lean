/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The counted record decoder with the formula height bound as a parameter (option A of
   `roles/bundle/PREMISE-REPLAY.md`). `declarationCD maxDepth` is `declarationC` with `maxDepth`
   in place of 64 in the unit depth test, the height test and the binder test of FOF bodies and in
   the parenthesis test of CNF bodies; term depth stays 64. `declarationCD_eq` proves it equal to
   `CnfBoolean.declarationD maxDepth` with the count added, for every bound, and
   `declarationSeenCD_eq` relates the version with the seen test as a parameter. At 64 both are
   today's `declarationC` and `declarationSeenC`. -/
import ExpandedLimitDecoder
import CnfBooleanDeclarationDepth

namespace Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof

def clauseCD (maxDepth : Nat) : Nat → Nat → Nat → List Token → Nat → Except Error (List Formula × List Token × Nat)
  | 0, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, endOffset, tokens, count => do
    if depth > maxDepth then failure .resource endOffset tokens
    if isChar '(' tokens then
      let (values, rest, restCount) ← clauseCD maxDepth fuel (depth + 1) endOffset tokens.tail (count - 1)
      let (_, final) ← expect ')' endOffset rest
      pure (values, final, restCount - 1)
    else disjunctionC (count + 1) endOffset tokens count

def checkedCD (maxDepth depth endOffset : Nat) (original : List Token) (body : Formula) (rest : List Token)
    (count : Nat) : Except Error (Formula × List Token × Nat) :=
  if depth + body.height - 1 > maxDepth then failure .resource endOffset original
  else .ok (body, rest, count)

mutual
def unitCD (maxDepth : Nat) : Nat → Nat → List String → Nat → List Token → Nat →
    Except Error (Formula × List Token × Nat)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens, count => do
    if depth > maxDepth then failure .resource endOffset tokens
    let token :: rest := tokens | failure .invalid endOffset tokens
    match token.kind with
    | .legacy .truth => pure (.truth, rest, count - 1)
    | .legacy .falsity => pure (.falsity, rest, count - 1)
    | .legacy (.punctuation '~') =>
      let (body, final, finalCount) ← unitCD maxDepth fuel (depth + 1) bound endOffset rest (count - 1)
      checkedCD maxDepth depth endOffset tokens (.neg body) final finalCount
    | .legacy (.punctuation '(') =>
      let (body, tail, tailCount) ← formulaCD maxDepth fuel (depth + 1) bound endOffset rest (count - 1)
      let (_, final) ← expect ')' endOffset tail
      pure (body, final, tailCount - 1)
    | .legacy (.punctuation '!') | .legacy (.punctuation '?') =>
      let (_, tail) ← expect '[' endOffset rest
      let (names, tail, tailCount) ← bindersC (count + 1) endOffset tail (count - 2)
      if names.length + depth > maxDepth then failure .resource endOffset tokens
      let (_, tail) ← expect ']' endOffset tail
      let (_, tail) ← expect ':' endOffset tail
      let (body, final, finalCount) ←
        unitCD maxDepth fuel (depth + names.length) (names ++ bound) endOffset tail (tailCount - 2)
      checkedCD maxDepth depth endOffset tokens (close (token.kind == .legacy (.punctuation '!')) names body) final
        finalCount
    | .legacy (.integer _) => failure .unsupported endOffset tokens
    | _ =>
      let (body, rest, restCount) ← atomC (2 * count + 1) (some bound) endOffset tokens count
      checkedCD maxDepth depth endOffset tokens body rest restCount

def formulaCD (maxDepth : Nat) : Nat → Nat → List String → Nat → List Token → Nat →
    Except Error (Formula × List Token × Nat)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens, count => do
    let (left, rest, restCount) ← unitCD maxDepth fuel depth bound endOffset tokens count
    match rest with
    | [] => pure (left, rest, restCount)
    | next :: _ =>
      match binary next.kind with
      | none => pure (left, rest, restCount)
      | some operator => chainCD maxDepth fuel depth bound endOffset operator left rest restCount

def chainCD (maxDepth : Nat) : Nat → Nat → List String → Nat → Binary → Formula → List Token → Nat →
    Except Error (Formula × List Token × Nat)
  | 0, _, _, endOffset, _, _, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, operator, left, tokens, count => do
    let next :: rest := tokens | failure .invalid endOffset tokens
    if binary next.kind != some operator then failure .internal endOffset tokens
    let (right, tail, tailCount) ← unitCD maxDepth fuel (depth + operator.extra) bound endOffset rest (count - 1)
    let body := Formula.pair operator left right
    let (_, _) ← checkedAt maxDepth depth endOffset tokens body tail
    if operator.associative && tail.head?.bind (binary ∘ Token.kind) == some operator then
      chainCD maxDepth fuel depth bound endOffset operator body tail tailCount
    else pure (body, tail, tailCount)
end

def declarationCD (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (tokens : List Token) (count : Nat) :
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
  if seen.contains label then failure .invalid endOffset (nameToken :: rest)
  let (_, rest) ← expect ',' endOffset rest
  let role :: rest := rest | failure .invalid endOffset rest
  match role.kind with
  | .legacy (.lower "axiom") => pure ()
  | .legacy (.lower _) => failure .unsupported endOffset (role :: rest)
  | _ => failure .invalid endOffset (role :: rest)
  let (_, originalBody) ← expect ',' endOffset rest
  let bodyCount := count - 6
  let (body, rest, restCount) ← if isCnf then do
      let (values, rest, restCount) ← clauseCD maxDepth (bodyCount + 1) 1 endOffset originalBody bodyCount
      pure (Body.cnf values, rest, restCount)
    else do
      let (body, rest, restCount) ← formulaCD maxDepth (3 * bodyCount + 1) 1 [] endOffset originalBody bodyCount
      pure (Body.fof body, rest, restCount)
  let bodyStop := ((originalBody.take (bodyCount - restCount)).getLast?.map Token.stop).getD endOffset
  if isChar ',' rest then failure .unsupported endOffset rest
  let (_, rest) ← expect ')' endOffset rest
  let (dot, rest) ← expect '.' endOffset rest
  pure (⟨label, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest, restCount - 2)

/-- `declarationCD` with the test for seen names as a parameter. -/
def declarationSeenCD (maxDepth : Nat) (isSeen : Name → Bool) (endOffset : Nat) (tokens : List Token) (count : Nat) :
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
      let (values, rest, restCount) ← clauseCD maxDepth (bodyCount + 1) 1 endOffset originalBody bodyCount
      pure (Body.cnf values, rest, restCount)
    else do
      let (body, rest, restCount) ← formulaCD maxDepth (3 * bodyCount + 1) 1 [] endOffset originalBody bodyCount
      pure (Body.fof body, rest, restCount)
  let bodyStop := ((originalBody.take (bodyCount - restCount)).getLast?.map Token.stop).getD endOffset
  if isChar ',' rest then failure .unsupported endOffset rest
  let (_, rest) ← expect ')' endOffset rest
  let (dot, rest) ← expect '.' endOffset rest
  pure (⟨label, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest, restCount - 2)

/-! Equality with the parameterised parsers, for every bound. -/

theorem clauseCD_eq (maxDepth : Nat) : ∀ fuel depth endOffset tokens count, count = tokens.length →
    clauseCD maxDepth fuel depth endOffset tokens count =
      (CnfBoolean.clauseAt maxDepth fuel depth endOffset tokens).map annotate
  | 0, _, _, _, _, _ => by
    unfold clauseCD CnfBoolean.clauseAt
    rfl
  | fuel + 1, depth, endOffset, tokens, count, counted => by
    unfold clauseCD CnfBoolean.clauseAt
    by_cases deep : depth > maxDepth
    · rw [ite_eq_left deep, ite_eq_left deep]
      rfl
    · rw [ite_eq_right deep, ite_eq_right deep]
      by_cases paren : isChar '(' tokens = true
      · rw [ite_eq_left paren, ite_eq_left paren,
          clauseCD_eq maxDepth fuel (depth + 1) endOffset tokens.tail (count - 1) (by simp [counted]), bind_annotate,
          map_bind]
        apply bind_congr_ok
        intro value _
        rw [map_bind]
        apply bind_congr_ok
        intro closing closed
        have shorter := expect_rest closed
        simp only at shorter ⊢
        rw [← shorter]
        rfl
      · rw [ite_eq_right paren, ite_eq_right paren]
        subst counted
        exact disjunctionC_eq _ endOffset tokens tokens.length rfl

theorem checkedCD_eq {maxDepth depth endOffset original body rest count} (counted : count = rest.length) :
    checkedCD maxDepth depth endOffset original body rest count =
      (checkedAt maxDepth depth endOffset original body rest).map annotate := by
  subst counted
  unfold checkedCD checkedAt
  by_cases high : depth + body.height - 1 > maxDepth
  · simp only [high]
    rfl
  · simp only [high]
    rfl

theorem unitCD_formulaCD_chainCD_eq (maxDepth : Nat) : ∀ fuel : Nat,
    (∀ depth bound endOffset tokens count, count = tokens.length →
      unitCD maxDepth fuel depth bound endOffset tokens count =
        (unitAt maxDepth fuel depth bound endOffset tokens).map annotate) ∧
    (∀ depth bound endOffset tokens count, count = tokens.length →
      formulaCD maxDepth fuel depth bound endOffset tokens count =
        (formulaAt maxDepth fuel depth bound endOffset tokens).map annotate) ∧
    (∀ depth bound endOffset operator left tokens count, count = tokens.length →
      chainCD maxDepth fuel depth bound endOffset operator left tokens count =
        (chainAt maxDepth fuel depth bound endOffset operator left tokens).map annotate)
  | 0 => ⟨fun _ _ _ _ _ _ => by unfold unitCD unitAt; rfl, fun _ _ _ _ _ _ => by unfold formulaCD formulaAt; rfl,
      fun _ _ _ _ _ _ _ _ => by unfold chainCD chainAt; rfl⟩
  | fuel + 1 => by
    obtain ⟨unitIH, formulaIH, chainIH⟩ := unitCD_formulaCD_chainCD_eq maxDepth fuel
    refine ⟨?_, ?_, ?_⟩
    · intro depth bound endOffset tokens count counted
      subst counted
      unfold unitCD unitAt
      by_cases deep : depth > maxDepth
      · simp only [deep, ↓reduceIte]
        rfl
      cases tokens with
      | nil =>
        simp only [deep, ↓reduceIte]
        rfl
      | cons token rest =>
        simp only [deep, ↓reduceIte]
        split
        all_goals
          split
          all_goals try (exfalso; simp_all; done)
        next _ _ => rfl
        next _ _ => rfl
        next _ _ =>
          rw [unitIH (depth + 1) bound endOffset rest ((token :: rest).length - 1) (by simp), bind_annotate, map_bind]
          apply bind_congr_ok
          intro value _
          exact checkedCD_eq rfl
        next _ _ =>
          rw [formulaIH (depth + 1) bound endOffset rest ((token :: rest).length - 1) (by simp), bind_annotate,
            map_bind]
          apply bind_congr_ok
          intro value _
          rw [map_bind]
          apply bind_congr_ok
          intro closing closed
          have shorter := expect_rest closed
          simp only [annotate] at shorter ⊢
          rw [← shorter]
          rfl
        next _ heq =>
          rw [map_bind]
          apply bind_congr_ok
          intro opened openedOk
          have openedShorter := expect_rest openedOk
          rw [bindersC_eq _ endOffset opened.2 ((token :: rest).length - 2) (by simp [openedShorter]), bind_annotate,
            map_bind]
          apply bind_congr_ok
          intro names _
          dsimp only [annotate]
          by_cases wide : names.1.length + depth > maxDepth
          · simp only [wide, ↓reduceIte]
            rfl
          · simp only [wide, ↓reduceIte]
            rw [map_bind]
            apply bind_congr_ok
            intro closing closingOk
            rw [map_bind]
            apply bind_congr_ok
            intro colon colonOk
            have closingShorter := expect_rest closingOk
            have colonShorter := expect_rest colonOk
            rw [unitIH (depth + names.1.length) (names.1 ++ bound) endOffset colon.2 (names.2.length - 2) (by omega),
              bind_annotate, map_bind]
            apply bind_congr_ok
            intro body _
            rw [heq]
            exact checkedCD_eq rfl
        next _ heq =>
          rw [map_bind]
          apply bind_congr_ok
          intro opened openedOk
          have openedShorter := expect_rest openedOk
          rw [bindersC_eq _ endOffset opened.2 ((token :: rest).length - 2) (by simp [openedShorter]), bind_annotate,
            map_bind]
          apply bind_congr_ok
          intro names _
          dsimp only [annotate]
          by_cases wide : names.1.length + depth > maxDepth
          · simp only [wide, ↓reduceIte]
            rfl
          · simp only [wide, ↓reduceIte]
            rw [map_bind]
            apply bind_congr_ok
            intro closing closingOk
            rw [map_bind]
            apply bind_congr_ok
            intro colon colonOk
            have closingShorter := expect_rest closingOk
            have colonShorter := expect_rest colonOk
            rw [unitIH (depth + names.1.length) (names.1 ++ bound) endOffset colon.2 (names.2.length - 2) (by omega),
              bind_annotate, map_bind]
            apply bind_congr_ok
            intro body _
            rw [heq]
            exact checkedCD_eq rfl
        next _ _ _ _ => rfl
        next =>
          rw [atomC_eq rfl, bind_annotate, map_bind]
          apply bind_congr_ok
          intro value _
          exact checkedCD_eq rfl
    · intro depth bound endOffset tokens count counted
      unfold formulaCD formulaAt
      rw [unitIH depth bound endOffset tokens count counted, bind_annotate, map_bind]
      apply bind_congr_ok
      intro value _
      obtain ⟨left, rest⟩ := value
      dsimp only [annotate]
      cases rest with
      | nil => rfl
      | cons next after =>
        dsimp only
        cases hb : binary next.kind with
        | none => rfl
        | some operator => exact chainIH depth bound endOffset operator left (next :: after) _ rfl
    · intro depth bound endOffset operator left tokens count counted
      subst counted
      unfold chainCD chainAt
      cases tokens with
      | nil => rfl
      | cons next rest =>
        dsimp only
        by_cases other : (binary next.kind != some operator) = true
        · simp only [other, ↓reduceIte]
          rfl
        · simp only [other, Bool.false_eq_true, ↓reduceIte]
          rw [unitIH (depth + operator.extra) bound endOffset rest ((next :: rest).length - 1) (by simp),
            bind_annotate, map_bind]
          apply bind_congr_ok
          intro value _
          obtain ⟨right, tail⟩ := value
          dsimp only [annotate]
          rw [map_bind]
          apply bind_congr_ok
          intro done _
          by_cases more : (operator.associative && tail.head?.bind (binary ∘ Token.kind) == some operator) = true
          · simp only [more, ↓reduceIte]
            exact chainIH depth bound endOffset operator _ tail _ rfl
          · simp only [more, Bool.false_eq_true, ↓reduceIte]
            rfl

/-- The counted record decoder equals `CnfBoolean.declarationD` with the count added, for every bound. -/
theorem declarationCD_eq {maxDepth seen endOffset tokens count} (counted : count = tokens.length) :
    declarationCD maxDepth seen endOffset tokens count =
      (CnfBoolean.declarationD maxDepth seen endOffset tokens).map annotate := by
  subst counted
  unfold declarationCD CnfBoolean.declarationD
  cases tokens with
  | nil => rfl
  | cons keyword rest =>
    dsimp only
    split
    all_goals
      split
      all_goals try (exfalso; simp_all; done)
    all_goals try rfl
    all_goals
      simp only [pure_bind]
      rw [map_bind]
      apply bind_congr_ok
      intro opened openedOk
      obtain ⟨openToken, afterOpen⟩ := opened
      cases afterOpen with
      | nil => rfl
      | cons nameToken afterName =>
        dsimp only
        cases hk : nameToken.kind with
        | legacy nameKind =>
          dsimp only
          cases hn : nameKind.name with
          | none => rfl
          | some label =>
            dsimp only
            by_cases dup : seen.contains label = true
            · simp only [dup, ↓reduceIte]
              rfl
            · simp only [dup, Bool.false_eq_true, ↓reduceIte]
              rw [map_bind]
              apply bind_congr_ok
              intro comma comma1Ok
              obtain ⟨commaToken, afterComma⟩ := comma
              cases afterComma with
              | nil => rfl
              | cons role afterRole =>
                dsimp only
                split
                all_goals
                  split
                  all_goals try (exfalso; simp_all; done)
                all_goals try rfl
                all_goals
                  rw [map_bind]
                  apply bind_congr_ok
                  intro bodyComma bodyCommaOk
                  obtain ⟨bodyCommaToken, originalBody⟩ := bodyComma
                  have openedShorter := expect_rest openedOk
                  have commaShorter := expect_rest comma1Ok
                  have bodyShorter := expect_rest bodyCommaOk
                  simp only [List.length_cons] at openedShorter commaShorter bodyShorter
                  have bodyLength : (keyword :: rest).length - 6 = originalBody.length := by
                    simp only [List.length_cons]
                    omega
                  rw [bodyLength]
                  first
                    | rw [clauseCD_eq maxDepth _ 1 endOffset originalBody originalBody.length rfl]
                    | rw [(unitCD_formulaCD_chainCD_eq maxDepth _).2.1 1 [] endOffset originalBody originalBody.length rfl]
                  rw [bind_annotate, map_bind]
                  apply bind_congr_ok
                  intro parsed _
                  simp only [annotate]
                  by_cases trailing : isChar ',' parsed.2 = true
                  · simp only [trailing, ↓reduceIte]
                    rfl
                  · simp only [trailing, Bool.false_eq_true, ↓reduceIte]
                    rw [map_bind]
                    apply bind_congr_ok
                    intro closing closingOk
                    rw [map_bind]
                    apply bind_congr_ok
                    intro dot dotOk
                    have closingShorter := expect_rest closingOk
                    have dotShorter := expect_rest dotOk
                    have restLength : parsed.2.length - 2 = dot.2.length := by omega
                    rw [restLength]
                    rfl
        | _ => rfl

/-- With a seen test that agrees with the list of seen names, the two counted decoders agree. -/
theorem declarationSeenCD_eq {maxDepth : Nat} {isSeen : Name → Bool} {seen : List Name}
    (same : ∀ label, isSeen label = seen.contains label) (endOffset : Nat) (tokens : List Token) (count : Nat) :
    declarationSeenCD maxDepth isSeen endOffset tokens count = declarationCD maxDepth seen endOffset tokens count := by
  have : isSeen = fun label => seen.contains label := funext same
  subst this
  rfl

/-! At 64 the parameterised decoders are today's. -/

theorem clauseCD_accepted_at : ∀ fuel depth endOffset tokens count,
    clauseCD 64 fuel depth endOffset tokens count = clauseC fuel depth endOffset tokens count
  | 0, _, _, _, _ => by unfold clauseCD clauseC; rfl
  | fuel + 1, depth, endOffset, tokens, count => by
    unfold clauseCD clauseC
    simp only [clauseCD_accepted_at fuel]

theorem clauseCD_accepted : clauseCD 64 = clauseC := by
  funext fuel depth endOffset tokens count
  exact clauseCD_accepted_at fuel depth endOffset tokens count

theorem checkedCD_accepted : checkedCD 64 = checkedC := rfl

theorem unitCD_formulaCD_chainCD_accepted : ∀ fuel : Nat,
    (∀ depth bound endOffset tokens count,
      unitCD 64 fuel depth bound endOffset tokens count = unitC fuel depth bound endOffset tokens count) ∧
    (∀ depth bound endOffset tokens count,
      formulaCD 64 fuel depth bound endOffset tokens count = formulaC fuel depth bound endOffset tokens count) ∧
    (∀ depth bound endOffset operator left tokens count,
      chainCD 64 fuel depth bound endOffset operator left tokens count =
        chainC fuel depth bound endOffset operator left tokens count)
  | 0 => ⟨fun _ _ _ _ _ => by unfold unitCD unitC; rfl, fun _ _ _ _ _ => by unfold formulaCD formulaC; rfl,
      fun _ _ _ _ _ _ _ => by unfold chainCD chainC; rfl⟩
  | fuel + 1 => by
    obtain ⟨units, formulas, chains⟩ := unitCD_formulaCD_chainCD_accepted fuel
    refine ⟨fun depth bound endOffset tokens count => ?_, fun depth bound endOffset tokens count => ?_,
      fun depth bound endOffset operator left tokens count => ?_⟩
    · unfold unitCD unitC
      simp only [units, formulas, checkedCD_accepted]
      all_goals rfl
    · unfold formulaCD formulaC
      simp only [units, chains]
      all_goals rfl
    · unfold chainCD chainC
      simp only [units, chains, checkedAt_accepted]
      all_goals rfl

theorem formulaCD_accepted : formulaCD 64 = formulaC := by
  funext fuel depth bound endOffset tokens count
  exact (unitCD_formulaCD_chainCD_accepted fuel).2.1 depth bound endOffset tokens count

theorem declarationCD_accepted : declarationCD 64 = declarationC := by
  funext seen endOffset tokens count
  unfold declarationCD declarationC
  simp only [clauseCD_accepted, formulaCD_accepted]
  all_goals rfl

theorem declarationSeenCD_accepted : declarationSeenCD 64 = declarationSeenC := by
  funext isSeen endOffset tokens count
  unfold declarationSeenCD declarationSeenC
  simp only [clauseCD_accepted, formulaCD_accepted]
  all_goals rfl

#print axioms Fang.TptpCandidate.FullFof.Integration.clauseCD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.checkedCD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.unitCD_formulaCD_chainCD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationCD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationSeenCD_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.clauseCD_accepted_at
#print axioms Fang.TptpCandidate.FullFof.Integration.clauseCD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.checkedCD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.unitCD_formulaCD_chainCD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.formulaCD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationCD_accepted
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationSeenCD_accepted

end Fang.TptpCandidate.FullFof.Integration
