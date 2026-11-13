/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The accepted CNF/FOF declaration decoder with each parser also returning the
   number of tokens it leaves. The accepted parsers compute their fuel and the
   body end from `List.length` of the remaining tokens, which is the rest of the
   file, once per literal, atom, quantifier and declaration. Here every such
   length is the counter carried beside the list, so each argument has the same
   value as in the accepted call. Each parser is proved equal to the accepted
   one with the count added, and `decodeBytesLinear` equals
   `CnfBoolean.decodeBytes`. Other decoders that call `CnfBoolean.declaration`,
   such as the signed role decoder, can use `declarationC` and `declarationC_eq`. -/
import CnfBooleanProblemInput
import ExpandedLexer

namespace Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof

/-- A parse result with the length of the tokens it leaves. -/
def annotate {α : Type} (result : α × List Token) : α × List Token × Nat :=
  (result.1, result.2, result.2.length)

/-! Terms and atoms. -/

mutual
def termC : Nat → Nat → Option (List String) → Nat → List Token → Nat →
    Except Error (Source.Term × List Token × Nat)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, scope, endOffset, tokens, count => do
    if depth > 64 then failure .resource endOffset tokens
    let token :: rest := tokens | failure .invalid endOffset tokens
    match token.kind with
    | .legacy (.variable name) =>
      if let some bound := scope then
        if !bound.contains name then failure .invalid endOffset tokens
      pure (.var name, rest, count - 1)
    | .legacy (.integer _) => failure .unsupported endOffset tokens
    | kind =>
      let some name := FullFof.atomic kind | failure .invalid endOffset tokens
      if isChar '(' rest then
        let (args, tail, tailCount) ← argumentsC fuel (depth + 1) scope endOffset rest.tail (count - 2)
        let (_, final) ← expect ')' endOffset tail
        pure (.app name args, final, tailCount - 1)
      else pure (.app name [], rest, count - 1)

def argumentsC : Nat → Nat → Option (List String) → Nat → List Token → Nat →
    Except Error (List Source.Term × List Token × Nat)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, scope, endOffset, tokens, count => do
    let (first, rest, restCount) ← termC fuel depth scope endOffset tokens count
    if isChar ',' rest then
      let (tail, final, finalCount) ← argumentsC fuel depth scope endOffset rest.tail (restCount - 1)
      pure (first :: tail, final, finalCount)
    else pure ([first], rest, restCount)
end

def atomC (fuel : Nat) (scope : Option (List String)) (endOffset : Nat) (tokens : List Token) (count : Nat) :
    Except Error (Formula × List Token × Nat) := do
  let (head, rest, restCount) ← termC fuel 0 scope endOffset tokens count
  match rest with
  | token :: afterOperator =>
    if let .legacy (.equality positive) := token.kind then
      let (right, final, finalCount) ← termC fuel 0 scope endOffset afterOperator (restCount - 1)
      let equality := Formula.equal head right
      pure (if positive then equality else .neg equality, final, finalCount)
    else
      match head with
      | .var _ => failure .invalid endOffset tokens
      | .app name args => pure (.atom name args, rest, restCount)
  | [] =>
    match head with
    | .var _ => failure .invalid endOffset tokens
    | .app name args => pure (.atom name args, rest, restCount)

/-! Boolean CNF bodies. -/

def atomicC (endOffset : Nat) (tokens : List Token) (count : Nat) : Except Error (Formula × List Token × Nat) :=
  match tokens with
  | token :: rest =>
    match token.kind with
    | .legacy .truth => .ok (.truth, rest, count - 1)
    | .legacy .falsity => .ok (.falsity, rest, count - 1)
    | _ => atomC (2 * count + 1) none endOffset tokens count
  | [] => failure .invalid endOffset tokens

def wrappedAtomC (endOffset : Nat) (tokens : List Token) (count : Nat) : Except Error (Formula × List Token × Nat) := do
  if isChar '(' tokens then
    let (value, rest, restCount) ← atomicC endOffset tokens.tail (count - 1)
    let (_, final) ← expect ')' endOffset rest
    pure (value, final, restCount - 1)
  else atomicC endOffset tokens count

def literalC (endOffset : Nat) (tokens : List Token) (count : Nat) : Except Error (Formula × List Token × Nat) := do
  let negative := isChar '~' tokens
  let body := if negative then tokens.tail else tokens
  let bodyCount := if negative then count - 1 else count
  if isChar '!' body || isChar '?' body then failure .unsupported endOffset body
  if negative then
    let (value, rest, restCount) ← wrappedAtomC endOffset body bodyCount
    let value ← CnfBoolean.negate endOffset body value
    pure (value, rest, restCount)
  else atomicC endOffset body bodyCount

def disjunctionC : Nat → Nat → List Token → Nat → Except Error (List Formula × List Token × Nat)
  | 0, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, endOffset, tokens, count => do
    let (first, rest, restCount) ← literalC endOffset tokens count
    if isChar '|' rest then
      let (tail, final, finalCount) ← disjunctionC fuel endOffset rest.tail (restCount - 1)
      pure (first :: tail, final, finalCount)
    else if rest.head?.map Token.kind == some (.legacy .implies) || isChar '&' rest then
      failure .unsupported endOffset rest
    else pure ([first], rest, restCount)

def clauseC : Nat → Nat → Nat → List Token → Nat → Except Error (List Formula × List Token × Nat)
  | 0, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, endOffset, tokens, count => do
    if depth > 64 then failure .resource endOffset tokens
    if isChar '(' tokens then
      let (values, rest, restCount) ← clauseC fuel (depth + 1) endOffset tokens.tail (count - 1)
      let (_, final) ← expect ')' endOffset rest
      pure (values, final, restCount - 1)
    else disjunctionC (count + 1) endOffset tokens count

/-! FOF bodies. -/

def bindersC : Nat → Nat → List Token → Nat → Except Error (List String × List Token × Nat)
  | 0, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, endOffset, tokens, count => do
    let token :: rest := tokens | failure .invalid endOffset tokens
    let .legacy (.variable name) := token.kind | failure .invalid endOffset tokens
    if isChar ':' rest then failure .unsupported endOffset rest
    if isChar ',' rest then
      let (tail, final, finalCount) ← bindersC fuel endOffset rest.tail (count - 2)
      pure (name :: tail, final, finalCount)
    else pure ([name], rest, count - 1)

def checkedC (depth endOffset : Nat) (original : List Token) (body : Formula) (rest : List Token) (count : Nat) :
    Except Error (Formula × List Token × Nat) :=
  if depth + body.height - 1 > 64 then failure .resource endOffset original
  else .ok (body, rest, count)

mutual
def unitC : Nat → Nat → List String → Nat → List Token → Nat → Except Error (Formula × List Token × Nat)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens, count => do
    if depth > 64 then failure .resource endOffset tokens
    let token :: rest := tokens | failure .invalid endOffset tokens
    match token.kind with
    | .legacy .truth => pure (.truth, rest, count - 1)
    | .legacy .falsity => pure (.falsity, rest, count - 1)
    | .legacy (.punctuation '~') =>
      let (body, final, finalCount) ← unitC fuel (depth + 1) bound endOffset rest (count - 1)
      checkedC depth endOffset tokens (.neg body) final finalCount
    | .legacy (.punctuation '(') =>
      let (body, tail, tailCount) ← formulaC fuel (depth + 1) bound endOffset rest (count - 1)
      let (_, final) ← expect ')' endOffset tail
      pure (body, final, tailCount - 1)
    | .legacy (.punctuation '!') | .legacy (.punctuation '?') =>
      let (_, tail) ← expect '[' endOffset rest
      let (names, tail, tailCount) ← bindersC (count + 1) endOffset tail (count - 2)
      if names.length + depth > 64 then failure .resource endOffset tokens
      let (_, tail) ← expect ']' endOffset tail
      let (_, tail) ← expect ':' endOffset tail
      let (body, final, finalCount) ← unitC fuel (depth + names.length) (names ++ bound) endOffset tail (tailCount - 2)
      checkedC depth endOffset tokens (close (token.kind == .legacy (.punctuation '!')) names body) final finalCount
    | .legacy (.integer _) => failure .unsupported endOffset tokens
    | _ =>
      let (body, rest, restCount) ← atomC (2 * count + 1) (some bound) endOffset tokens count
      checkedC depth endOffset tokens body rest restCount

def formulaC : Nat → Nat → List String → Nat → List Token → Nat → Except Error (Formula × List Token × Nat)
  | 0, _, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens, count => do
    let (left, rest, restCount) ← unitC fuel depth bound endOffset tokens count
    match rest with
    | [] => pure (left, rest, restCount)
    | next :: _ =>
      match binary next.kind with
      | none => pure (left, rest, restCount)
      | some operator => chainC fuel depth bound endOffset operator left rest restCount

def chainC : Nat → Nat → List String → Nat → Binary → Formula → List Token → Nat →
    Except Error (Formula × List Token × Nat)
  | 0, _, _, endOffset, _, _, tokens, _ => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, operator, left, tokens, count => do
    let next :: rest := tokens | failure .invalid endOffset tokens
    if binary next.kind != some operator then failure .internal endOffset tokens
    let (right, tail, tailCount) ← unitC fuel (depth + operator.extra) bound endOffset rest (count - 1)
    let body := Formula.pair operator left right
    let (_, _) ← checked depth endOffset tokens body tail
    if operator.associative && tail.head?.bind (binary ∘ Token.kind) == some operator then
      chainC fuel depth bound endOffset operator body tail tailCount
    else pure (body, tail, tailCount)
end

/-! Declarations. -/

def declarationC (seen : List Name) (endOffset : Nat) (tokens : List Token) (count : Nat) :
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
  let some name := nameKind.name | failure .invalid endOffset (nameToken :: rest)
  if seen.contains name then failure .invalid endOffset (nameToken :: rest)
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
  pure (⟨name, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest, restCount - 2)

def declarationsC : Nat → List Name → Nat → List Token → Nat → Except Error (List Declaration)
  | 0, _, endOffset, tokens, _ => failure .resource endOffset tokens
  | _ + 1, _, _, [], _ => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _), count => do
    if seen.length ≥ 1000 then failure .resource endOffset tokens
    let (first, rest, restCount) ← declarationC seen endOffset tokens count
    let tail ← declarationsC fuel (first.name :: seen) endOffset rest restCount
    pure (first :: tail)

/-- The accepted v8 decoder with the linear lexer and the counted parsers. -/
def decodeBytesLinear (input : List UInt8) (maximumBytes : Nat) : Except Error (List Declaration) :=
  (fastTokenizeBytes input maximumBytes).bind fun tokens =>
    let count := tokens.length
    declarationsC (count + 1) [] input.length tokens count


/-! Equality with the accepted parsers. -/

theorem bind_annotate {α β : Type} (x : Except Error (α × List Token)) (f : α × List Token × Nat → Except Error β) :
    (x.map annotate) >>= f = x >>= fun value => f (annotate value) := by
  cases x <;> rfl

theorem map_bind {α β γ : Type} (x : Except Error α) (f : α → Except Error β) (g : β → γ) :
    (x >>= f).map g = x >>= fun value => (f value).map g := by
  cases x <;> rfl

theorem bind_congr_ok {α β : Type} {x : Except Error α} {f g : α → Except Error β}
    (same : ∀ value, x = .ok value → f value = g value) : x >>= f = x >>= g := by
  cases x with
  | error error => rfl
  | ok value => exact same value rfl

theorem expect_rest {char endOffset tokens token rest}
    (success : expect char endOffset tokens = .ok (token, rest)) : rest.length = tokens.length - 1 := by
  rw [(expect_exact success).1]
  simp

theorem termC_argumentsC_eq : ∀ fuel : Nat,
    (∀ depth scope endOffset tokens count, count = tokens.length →
      termC fuel depth scope endOffset tokens count = (term fuel depth scope endOffset tokens).map annotate) ∧
    (∀ depth scope endOffset tokens count, count = tokens.length →
      argumentsC fuel depth scope endOffset tokens count = (arguments fuel depth scope endOffset tokens).map annotate)
  | 0 => ⟨fun _ _ _ _ _ _ => by unfold termC term; rfl, fun _ _ _ _ _ _ => by unfold argumentsC arguments; rfl⟩
  | fuel + 1 => by
    obtain ⟨termIH, argumentsIH⟩ := termC_argumentsC_eq fuel
    refine ⟨?_, ?_⟩
    · intro depth scope endOffset tokens count counted
      subst counted
      unfold termC term
      by_cases deep : depth > 64
      · simp only [deep, ↓reduceIte]
        rfl
      cases tokens with
      | nil =>
        simp only [deep, ↓reduceIte]
        rfl
      | cons token rest =>
        simp only [deep, ↓reduceIte]
        cases hk : token.kind with
        | legacy k =>
          cases k with
          | «variable» name =>
            cases scope with
            | none => rfl
            | some bound =>
              dsimp only
              by_cases inside : (!bound.contains name) = true
              · simp only [inside]
                rfl
              · simp only [inside]
                rfl
          | lower name | quoted name =>
            dsimp only [FullFof.atomic]
            by_cases paren : isChar '(' rest = true
            · simp only [paren, ↓reduceIte]
              rw [argumentsIH (depth + 1) scope endOffset rest.tail ((token :: rest).length - 2) (by simp),
                bind_annotate, map_bind]
              apply bind_congr_ok
              intro value _
              rw [map_bind]
              apply bind_congr_ok
              intro closing closed
              have shorter := expect_rest closed
              simp only [annotate] at shorter ⊢
              rw [← shorter]
              rfl
            · simp only [paren]
              rfl
          | _ => rfl
        | _ => rfl
    · intro depth scope endOffset tokens count counted
      simp only [argumentsC, arguments]
      rw [termIH depth scope endOffset tokens count counted, bind_annotate, map_bind]
      apply bind_congr_ok
      intro value _
      by_cases comma : isChar ',' value.2 = true
      · simp only [annotate, comma, ↓reduceIte]
        rw [argumentsIH depth scope endOffset value.2.tail (value.2.length - 1) (by simp), bind_annotate, map_bind]
        apply bind_congr_ok
        intro tail _
        rfl
      · simp only [annotate, comma]
        rfl

theorem atomC_eq {fuel scope endOffset tokens count} (counted : count = tokens.length) :
    atomC fuel scope endOffset tokens count = (atom fuel scope endOffset tokens).map annotate := by
  unfold atomC atom
  rw [(termC_argumentsC_eq fuel).1 0 scope endOffset tokens count counted, bind_annotate, map_bind]
  apply bind_congr_ok
  intro value _
  obtain ⟨head, rest⟩ := value
  dsimp only [annotate]
  cases rest with
  | nil => cases head <;> rfl
  | cons token after =>
    dsimp only
    cases hk : token.kind with
    | legacy k =>
      cases k with
      | equality positive =>
        dsimp only
        rw [(termC_argumentsC_eq fuel).1 0 scope endOffset after ((token :: after).length - 1) (by simp),
          bind_annotate, map_bind]
        apply bind_congr_ok
        intro right _
        rfl
      | _ => cases head <;> rfl
    | _ => cases head <;> rfl

theorem atomicC_eq {endOffset tokens count} (counted : count = tokens.length) :
    atomicC endOffset tokens count = (CnfBoolean.atomic endOffset tokens).map annotate := by
  subst counted
  unfold atomicC CnfBoolean.atomic
  cases tokens with
  | nil => rfl
  | cons token rest =>
    dsimp only
    cases hk : token.kind with
    | legacy k =>
      cases k with
      | truth => rfl
      | falsity => rfl
      | _ => exact atomC_eq rfl
    | _ => exact atomC_eq rfl

theorem wrappedAtomC_eq {endOffset tokens count} (counted : count = tokens.length) :
    wrappedAtomC endOffset tokens count = (CnfBoolean.wrappedAtom endOffset tokens).map annotate := by
  unfold wrappedAtomC CnfBoolean.wrappedAtom
  by_cases paren : isChar '(' tokens = true
  · rw [ite_eq_left paren, ite_eq_left paren, atomicC_eq (by simp [counted]), bind_annotate, map_bind]
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
    exact atomicC_eq counted

theorem literalC_eq {endOffset tokens count} (counted : count = tokens.length) :
    literalC endOffset tokens count = (CnfBoolean.literal endOffset tokens).map annotate := by
  unfold literalC CnfBoolean.literal
  dsimp only
  by_cases negative : isChar '~' tokens = true
  · simp only [negative, ↓reduceIte]
    by_cases bang : (isChar '!' tokens.tail || isChar '?' tokens.tail) = true
    · rw [ite_eq_left bang, ite_eq_left bang]
      rfl
    · rw [ite_eq_right bang, ite_eq_right bang, wrappedAtomC_eq (by simp [counted]), bind_annotate, map_bind]
      apply bind_congr_ok
      intro value _
      rw [map_bind]
      apply bind_congr_ok
      intro negated _
      rfl
  · simp only [negative, Bool.false_eq_true, ↓reduceIte]
    by_cases bang : (isChar '!' tokens || isChar '?' tokens) = true
    · rw [ite_eq_left bang, ite_eq_left bang]
      rfl
    · rw [ite_eq_right bang, ite_eq_right bang]
      exact atomicC_eq counted

theorem disjunctionC_eq : ∀ fuel endOffset tokens count, count = tokens.length →
    disjunctionC fuel endOffset tokens count = (CnfBoolean.disjunction fuel endOffset tokens).map annotate
  | 0, _, _, _, _ => by
    unfold disjunctionC CnfBoolean.disjunction
    rfl
  | fuel + 1, endOffset, tokens, count, counted => by
    unfold disjunctionC CnfBoolean.disjunction
    rw [literalC_eq counted, bind_annotate, map_bind]
    apply bind_congr_ok
    intro value _
    dsimp only [annotate]
    by_cases bar : isChar '|' value.2 = true
    · rw [ite_eq_left bar, ite_eq_left bar,
        disjunctionC_eq fuel endOffset value.2.tail (value.2.length - 1) (by simp), bind_annotate, map_bind]
      apply bind_congr_ok
      intro tail _
      rfl
    · rw [ite_eq_right bar, ite_eq_right bar]
      by_cases other : (value.2.head?.map Token.kind == some (.legacy .implies) || isChar '&' value.2) = true
      · rw [ite_eq_left other, ite_eq_left other]
        rfl
      · rw [ite_eq_right other, ite_eq_right other]
        rfl

theorem clauseC_eq : ∀ fuel depth endOffset tokens count, count = tokens.length →
    clauseC fuel depth endOffset tokens count = (CnfBoolean.clause fuel depth endOffset tokens).map annotate
  | 0, _, _, _, _, _ => by
    unfold clauseC CnfBoolean.clause
    rfl
  | fuel + 1, depth, endOffset, tokens, count, counted => by
    unfold clauseC CnfBoolean.clause
    by_cases deep : depth > 64
    · rw [ite_eq_left deep, ite_eq_left deep]
      rfl
    · rw [ite_eq_right deep, ite_eq_right deep]
      by_cases paren : isChar '(' tokens = true
      · rw [ite_eq_left paren, ite_eq_left paren,
          clauseC_eq fuel (depth + 1) endOffset tokens.tail (count - 1) (by simp [counted]), bind_annotate, map_bind]
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

theorem bindersC_eq : ∀ fuel endOffset tokens count, count = tokens.length →
    bindersC fuel endOffset tokens count = (binders fuel endOffset tokens).map annotate
  | 0, _, _, _, _ => by
    unfold bindersC binders
    rfl
  | fuel + 1, endOffset, tokens, count, counted => by
    subst counted
    unfold bindersC binders
    cases tokens with
    | nil => rfl
    | cons token rest =>
      dsimp only
      cases hk : token.kind with
      | legacy k =>
        cases k with
        | «variable» name =>
          dsimp only
          by_cases colon : isChar ':' rest = true
          · simp only [colon, ↓reduceIte]
            rfl
          · simp only [colon, Bool.false_eq_true, ↓reduceIte]
            by_cases comma : isChar ',' rest = true
            · simp only [comma, ↓reduceIte]
              rw [bindersC_eq fuel endOffset rest.tail ((token :: rest).length - 2) (by simp), bind_annotate, map_bind]
              apply bind_congr_ok
              intro value _
              rfl
            · simp only [comma, Bool.false_eq_true, ↓reduceIte]
              rfl
        | _ => rfl
      | _ => rfl

theorem checkedC_eq {depth endOffset original body rest count} (counted : count = rest.length) :
    checkedC depth endOffset original body rest count = (checked depth endOffset original body rest).map annotate := by
  subst counted
  unfold checkedC checked
  by_cases high : depth + body.height - 1 > 64
  · simp only [high]
    rfl
  · simp only [high]
    rfl

theorem unitC_formulaC_chainC_eq : ∀ fuel : Nat,
    (∀ depth bound endOffset tokens count, count = tokens.length →
      unitC fuel depth bound endOffset tokens count = (unit fuel depth bound endOffset tokens).map annotate) ∧
    (∀ depth bound endOffset tokens count, count = tokens.length →
      formulaC fuel depth bound endOffset tokens count = (formula fuel depth bound endOffset tokens).map annotate) ∧
    (∀ depth bound endOffset operator left tokens count, count = tokens.length →
      chainC fuel depth bound endOffset operator left tokens count =
        (chain fuel depth bound endOffset operator left tokens).map annotate)
  | 0 => ⟨fun _ _ _ _ _ _ => by unfold unitC unit; rfl, fun _ _ _ _ _ _ => by unfold formulaC formula; rfl,
      fun _ _ _ _ _ _ _ _ => by unfold chainC chain; rfl⟩
  | fuel + 1 => by
    obtain ⟨unitIH, formulaIH, chainIH⟩ := unitC_formulaC_chainC_eq fuel
    refine ⟨?_, ?_, ?_⟩
    · intro depth bound endOffset tokens count counted
      subst counted
      unfold unitC unit
      by_cases deep : depth > 64
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
          exact checkedC_eq rfl
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
          by_cases wide : names.1.length + depth > 64
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
            exact checkedC_eq rfl
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
          by_cases wide : names.1.length + depth > 64
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
            exact checkedC_eq rfl
        next _ _ _ _ => rfl
        next =>
          rw [atomC_eq rfl, bind_annotate, map_bind]
          apply bind_congr_ok
          intro value _
          exact checkedC_eq rfl
    · intro depth bound endOffset tokens count counted
      unfold formulaC formula
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
      unfold chainC chain
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

theorem declarationC_eq {seen endOffset tokens count} (counted : count = tokens.length) :
    declarationC seen endOffset tokens count = (CnfBoolean.declaration seen endOffset tokens).map annotate := by
  subst counted
  unfold declarationC CnfBoolean.declaration
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
          | some name =>
            dsimp only
            by_cases dup : seen.contains name = true
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
                    | rw [clauseC_eq _ 1 endOffset originalBody originalBody.length rfl]
                    | rw [(unitC_formulaC_chainC_eq _).2.1 1 [] endOffset originalBody originalBody.length rfl]
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


theorem declarationsC_eq : ∀ fuel seen endOffset tokens count, count = tokens.length →
    declarationsC fuel seen endOffset tokens count = CnfBoolean.declarations fuel seen endOffset tokens
  | 0, _, _, _, _, _ => by
    unfold declarationsC CnfBoolean.declarations
    rfl
  | fuel + 1, seen, endOffset, [], _, _ => by
    unfold declarationsC CnfBoolean.declarations
    rfl
  | fuel + 1, seen, endOffset, token :: rest, count, counted => by
    unfold declarationsC CnfBoolean.declarations
    by_cases full : seen.length ≥ 1000
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      rw [declarationC_eq counted, bind_annotate]
      apply bind_congr_ok
      intro value _
      simp only [annotate]
      rw [declarationsC_eq fuel (value.1.name :: seen) endOffset value.2 value.2.length rfl]

/-- The linear decoder returns exactly what the accepted v8 decoder returns. -/
theorem decodeBytesLinear_eq (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesLinear input maximumBytes = CnfBoolean.decodeBytes input maximumBytes := by
  unfold decodeBytesLinear CnfBoolean.decodeBytes
  rw [fastTokenizeBytes_eq]
  cases FullFof.tokenizeBytes input maximumBytes with
  | error error => rfl
  | ok tokens => exact declarationsC_eq _ [] input.length tokens tokens.length rfl

#print axioms Fang.TptpCandidate.FullFof.Integration.bind_annotate
#print axioms Fang.TptpCandidate.FullFof.Integration.map_bind
#print axioms Fang.TptpCandidate.FullFof.Integration.bind_congr_ok
#print axioms Fang.TptpCandidate.FullFof.Integration.expect_rest
#print axioms Fang.TptpCandidate.FullFof.Integration.termC_argumentsC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.atomC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.atomicC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.wrappedAtomC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.literalC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.disjunctionC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.clauseC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.bindersC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.checkedC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.unitC_formulaC_chainC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.declarationsC_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeBytesLinear_eq

end Fang.TptpCandidate.FullFof.Integration
