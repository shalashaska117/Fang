/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.Input
import Fang.FOF.NamedSource

/- Independent checker decoder candidate. No production command imports this
   file. Its relation to an independent byte grammar is an open obligation. -/
namespace Fang.FOFFrontend
open Frontend

def lexAux : Nat → List Char → Nat → Except String (List Token)
  | 0, _, offset => .error s!"resource-exhaustion at byte {offset}: lexer fuel"
  | _ + 1, [], _ => .ok []
  | fuel + 1, c :: cs, offset => do
    if asciiSpace c then
      lexAux fuel cs (offset + 1)
    else if wordChar c then
      let (tail, rest) := cs.span wordChar
      let chars := c :: tail
      let remaining ← lexAux fuel rest (offset + chars.length)
      pure ({ text := String.ofList chars, offset } :: remaining)
    else if c == '=' && cs.head? == some '>' then
      let remaining ← lexAux fuel cs.tail (offset + 2)
      pure ({ text := "=>", offset } :: remaining)
    else if c == '~' && (cs.head? == some '&' || cs.head? == some '|') then
      .error s!"unsupported at byte {offset}: NAND/NOR"
    else if ['(', ')', ',', '.', '|', '~', '&'].contains c then
      let remaining ← lexAux fuel cs (offset + 1)
      pure ({ text := String.singleton c, offset } :: remaining)
    else if ['=', '!', '?', '>', '<', ':', '[', ']', '\'', '"', '%', '/'].contains c then
      .error s!"unsupported at byte {offset}: token outside ground FOF"
    else .error s!"invalid-syntax at byte {offset}: character"

def tokenize (input : String) : Except String (List Token) := do
  if input.toList.any (fun c => c.toNat > 127) then
    .error "invalid-syntax: input must contain ASCII bytes only"
  else lexAux (input.toList.length + 1) input.toList 0

mutual
def groundTerm : Term → Bool
  | .var _ => false
  | .app _ args => groundTerms args
def groundTerms : List Term → Bool
  | [] => true
  | t :: ts => groundTerm t && groundTerms ts
end

def groundFormula : GroundFOF.Formula → Bool
  | .atom a => groundTerms a.args
  | .truth | .falsity => true
  | .neg a => groundFormula a
  | .conj a b | .disj a b | .implies a b => groundFormula a && groundFormula b

def formula : Nat → Parser GroundFOF.Formula
  | 0 => fail "resource-exhaustion: formula decoder fuel"
  | fuel + 1 => do
    let next ← peek
    if next == some "$true" then expect "$true"; pure .truth
    else if next == some "$false" then expect "$false"; pure .falsity
    else if next == some "~" then
      expect "~"
      pure (.neg (← formula fuel))
    else if next == some "(" then
      expect "("
      let left ← formula fuel
      let operator ← peek
      if operator == some "&" || operator == some "|" || operator == some "=>" then
        discard consume
        let right ← formula fuel
        expect ")"
        if operator == some "&" then pure (.conj left right)
        else if operator == some "|" then pure (.disj left right)
        else pure (.implies left right)
      else
        expect ")"
        pure left
    else
      match next with
      | some name =>
        if variableName name then fail "invalid-syntax: free FOF variable"
        else if lowerName name then
          let atom ← literal fuel
          pure (.atom atom.atom)
        else fail "unsupported: expected a ground formula"
      | none => fail "invalid-syntax: expected a ground formula"

def statement (fuel : Nat) : Parser GroundFOF.Declaration := do
  if (← peek) == some "cnf" then
    pure (.cnf (← Frontend.statement fuel))
  else if (← peek) == some "fof" then
    expect "fof"
    expect "("
    let offset ← position
    let name ← consume
    if !lowerName name then failAt offset "invalid-syntax: statement name must be a lower-case identifier"
    let state ← get
    if state.clauseNames.contains name then failAt offset "invalid-syntax: duplicate statement name"
    set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only the axiom role is supported"
    expect "axiom"
    expect ","
    let body ← formula fuel
    if !groundFormula body then fail "invalid-syntax: free FOF variable"
    if (← peek) == some "," then fail "unsupported: TPTP annotations"
    expect ")"
    expect "."
    pure (.fof body)
  else fail "unsupported: only CNF and ground FOF statements are supported"

def statements : Nat → Parser (List GroundFOF.Declaration)
  | 0 => fail "resource-exhaustion: declaration decoder fuel"
  | fuel + 1 => do
    if (← peek).isNone then pure []
    else
      let first ← statement fuel
      pure (first :: (← statements fuel))

structure Decoded where
  declarations : List GroundFOF.Declaration
  state : State

def decode (input : String) : Except String Decoded := do
  let tokens ← tokenize input
  let (declarations, state) ← statements (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize }
  pure { declarations, state }

/- Boolean groundness is a local validator property. It does not establish byte
   parsing, symbol-table correctness or correspondence with the Rust parser. -/
mutual
theorem groundTerm_correct (t : Term) : groundTerm t = true ↔ GroundFOF.GroundTerm t := by
  cases t with
  | var n => simp [groundTerm, GroundFOF.GroundTerm]
  | app f args =>
      simp only [groundTerm, GroundFOF.GroundTerm]
      exact groundTerms_correct args
theorem groundTerms_correct (ts : List Term) : groundTerms ts = true ↔ ∀ t ∈ ts, GroundFOF.GroundTerm t := by
  cases ts with
  | nil => simp [groundTerms]
  | cons t ts => simp only [groundTerms, Bool.and_eq_true, groundTerm_correct,
      groundTerms_correct, List.forall_mem_cons]
end

theorem groundFormula_correct (f : GroundFOF.Formula) : groundFormula f = true ↔ f.Ground := by
  induction f with
  | atom a => exact groundTerms_correct a.args
  | truth => simp [groundFormula, GroundFOF.Formula.Ground]
  | falsity => simp [groundFormula, GroundFOF.Formula.Ground]
  | neg a ih => exact ih
  | conj a b ih₁ ih₂ => simp only [groundFormula, GroundFOF.Formula.Ground, Bool.and_eq_true, ih₁, ih₂]
  | disj a b ih₁ ih₂ => simp only [groundFormula, GroundFOF.Formula.Ground, Bool.and_eq_true, ih₁, ih₂]
  | implies a b ih₁ ih₂ => simp only [groundFormula, GroundFOF.Formula.Ground, Bool.and_eq_true, ih₁, ih₂]

end Fang.FOFFrontend
