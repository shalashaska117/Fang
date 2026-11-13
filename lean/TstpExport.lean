import Fang.CertificateInput

/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent candidate exporter. See PROVENANCE.md and ../../LICENSE.
   This module does not establish a text-to-semantics correspondence theorem. -/

namespace Fang.TstpExport

structure NamedProblem where
  signature : DecodedProblem
  functions : List Frontend.Symbol
  predicates : List Frontend.Symbol
  names : List String

/-- Retain the existing decoder's tables, without introducing another parser. -/
def decodeNamed (input : String) : Except String NamedProblem := do
  let tokens ← Frontend.tokenize input
  let (problem, state) ← Frontend.statements (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize
  }
  pure {
    signature := {
      problem
      functionArities := state.functions.map (fun s => s.arity.getD 0)
      predicateArities := state.predicates.map (fun s => s.arity.getD 0)
    }
    functions := state.functions
    predicates := state.predicates
    names := state.clauseNames
  }

inductive Origin where
  | input (sourceIndex : Nat) (sourceName : String)
  | deduplicate (nodeId sourceIndex : Nat) (parent : String)
  | rename (nodeId : Nat) (right : Bool) (parent : String)
  | factor (nodeId first second : Nat) (parent : String) (substitution : Subst)
  | resolve (nodeId leftPos rightPos : Nat) (left right : String) (substitution : Subst)
  deriving Repr

structure Row where
  name : String
  clause : Clause
  origin : Origin
  deriving Repr

structure Export where
  signature : NamedProblem
  rows : List Row
  finalName : String

def parents : Step → List Nat
  | .input _ => []
  | .factor parent _ _ _ _ => [parent]
  | .resolve left _ right _ _ _ => [left, right]

/-- Parents precede children in a checked certificate. Reverse traversal finds
    exactly the final node's ancestors, including repeated-parent resolution. -/
def ancestors (certificate : Certificate) : List Nat :=
  certificate.steps.zipIdx.reverse.foldl (fun needed entry =>
    if needed.contains entry.2 then needed ++ parents entry.1 else needed) [certificate.final]

def internalName (index : Nat) : String := s!"fang:step:{index}"

def findLabel (labels : List (Nat × String)) (index : Nat) : Except String String :=
  match labels.find? (fun entry => entry.1 == index) with
  | some entry => .ok entry.2
  | none => .error "export-error: missing preceding parent"

/-- All clauses come from the same checker run. Input preprocessing is exposed
    as a separate row whenever stable literal deduplication changes the leaf. -/
def build (problem : NamedProblem) (certificate : Certificate) : Except String Export := do
  if certificate.steps.length > 1000 then
    throw "resource-exhaustion: export supports at most 1000 certificate nodes"
  if !certificateWellFormed problem.signature certificate then
    throw "invalid-certificate: unknown symbol or inconsistent arity"
  if !check (preprocess problem.signature.problem) certificate then
    throw "rejected-certificate"
  let some clauses := checkSteps (preprocess problem.signature.problem) [] certificate.steps
    | throw "export-error: checked clauses unavailable"
  let needed := ancestors certificate
  let mut rows : List Row := []
  let mut labels : List (Nat × String) := []
  let mut emittedInputs : List Nat := []
  for (step, index) in certificate.steps.zipIdx do
    if needed.contains index then
      let some clause := clauses[index]? | throw "export-error: missing checked clause"
      match step with
      | .input sourceIndex =>
        let some raw := problem.signature.problem[sourceIndex]?
          | throw "export-error: input index out of range"
        let some sourceName := problem.names[sourceIndex]?
          | throw "export-error: missing input name"
        if !emittedInputs.contains sourceIndex then
          rows := rows ++ [{ name := sourceName, clause := raw, origin := .input sourceIndex sourceName }]
          emittedInputs := sourceIndex :: emittedInputs
        if raw = clause then
          labels := (index, sourceName) :: labels
        else
          let name := internalName index
          rows := rows ++ [{ name, clause, origin := .deduplicate index sourceIndex sourceName }]
          labels := (index, name) :: labels
      | .factor parent first second substitution _ =>
        let parent ← findLabel labels parent
        let name := internalName index
        rows := rows ++ [{ name, clause, origin := .factor index first second parent substitution }]
        labels := (index, name) :: labels
      | .resolve left leftPos right rightPos substitution _ =>
        let some leftClause := clauses[left]? | throw "export-error: left clause unavailable"
        let some rightClause := clauses[right]? | throw "export-error: right clause unavailable"
        let leftParent ← findLabel labels left
        let rightParent ← findLabel labels right
        let left := s!"fang:left:{index}"
        let right := s!"fang:right:{index}"
        rows := rows ++ [
          { name := left, clause := leftClause.map (Literal.rename leftRename), origin := .rename index false leftParent },
          { name := right, clause := rightClause.map (Literal.rename rightRename), origin := .rename index true rightParent }]
        let name := internalName index
        rows := rows ++ [{ name, clause, origin := .resolve index leftPos rightPos left right substitution }]
        labels := (index, name) :: labels
  let finalName ← findLabel labels certificate.final
  if rows.getLast?.map Row.name != some finalName then
    throw "export-error: final row is not last"
  if rows.getLast?.map Row.clause != some [] then
    throw "export-error: final row is not false"
  pure { signature := problem, rows, finalName }

/-- TPTP quoted atoms permit backslash escaping of quote and backslash. A source
    label is printable ASCII only; it cannot inject a line or SZS status. -/
def quote (text : String) : Except String String := do
  if text.isEmpty || !text.toList.all (fun c => 32 ≤ c.toNat && c.toNat ≤ 126) then
    throw "unsupported: TSTP label must be nonempty printable ASCII"
  let escaped := text.toList.foldl (fun acc c =>
    acc ++ (if c == '\'' || c == '\\' then "\\" else "") ++ String.singleton c) ""
  pure ("'" ++ escaped ++ "'")

def symbol (symbols : List Frontend.Symbol) (index arity : Nat) : Except String String := do
  let some value := symbols[index]? | throw "export-error: unknown symbol"
  if !Frontend.lowerName value.name || value.arity != some arity then
    throw "export-error: symbol name or arity mismatch"
  pure value.name

mutual
  def term (symbols : List Frontend.Symbol) : Term → Except String String
    | .var index => .ok s!"X{index}"
    | .app index arguments => do
      let name ← symbol symbols index arguments.length
      let rendered ← terms symbols arguments
      pure (if arguments.isEmpty then name else name ++ "(" ++ String.intercalate "," rendered ++ ")")
  def terms (symbols : List Frontend.Symbol) : List Term → Except String (List String)
    | [] => .ok []
    | first :: rest => do pure ((← term symbols first) :: (← terms symbols rest))
end

def literal (problem : NamedProblem) (value : Literal) : Except String String := do
  let name ← symbol problem.predicates value.atom.pred value.atom.args.length
  let arguments ← terms problem.functions value.atom.args
  let atom := if arguments.isEmpty then name else name ++ "(" ++ String.intercalate "," arguments ++ ")"
  pure ((if value.positive then "" else "~") ++ atom)

def clause (problem : NamedProblem) (value : Clause) : Except String String := do
  if value.isEmpty then pure "$false"
  else pure (String.intercalate " | " (← value.mapM (literal problem)))

mutual
  def witnessTerm (symbols : List Frontend.Symbol) : Term → Except String String
    | .var index => .ok s!"var({index})"
    | .app index arguments => do
      let name ← symbol symbols index arguments.length
      let rendered ← witnessTerms symbols arguments
      pure ("fun(" ++ name ++ ",[" ++ String.intercalate "," rendered ++ "])")
  def witnessTerms (symbols : List Frontend.Symbol) : List Term → Except String (List String)
    | [] => .ok []
    | first :: rest => do pure ((← witnessTerm symbols first) :: (← witnessTerms symbols rest))
end

def witness (problem : NamedProblem) (substitution : Subst) : Except String String := do
  let bindings ← substitution.mapM fun (index, value) => do
    pure (s!"binding({index}," ++ (← witnessTerm problem.functions value) ++ ")")
  pure ("fang_substitution([" ++ String.intercalate "," bindings ++ "])")

def source (problem : NamedProblem) (fileLabel : String) : Origin → Except String String
  | .input _ sourceName => do
    pure ("file(" ++ (← quote fileLabel) ++ "," ++ (← quote sourceName) ++ ")")
  | .deduplicate nodeId _ parent => do
    pure (s!"inference(fang_deduplicate,[status(thm),fang_node({nodeId})],[" ++ (← quote parent) ++ "])")
  | .rename nodeId right parent => do
    let mapping := if right then "odd" else "even"
    pure (s!"inference(fang_standardize_apart,[status(thm),fang_node({nodeId}),renaming({mapping})],[" ++
      (← quote parent) ++ "])")
  | .factor nodeId first second parent substitution => do
    pure (s!"inference(fang_factoring,[status(thm),fang_node({nodeId}),pivots({first},{second})," ++
      (← witness problem substitution) ++ "],[" ++ (← quote parent) ++ "])")
  | .resolve nodeId leftPos rightPos left right substitution => do
    pure (s!"inference(fang_resolution,[status(thm),fang_node({nodeId}),pivots({leftPos},{rightPos})," ++
      (← witness problem substitution) ++ "],[" ++
      (← quote left) ++ "," ++ (← quote right) ++ "])")

def renderRow (problem : NamedProblem) (fileLabel : String) (row : Row) : Except String String := do
  let role := match row.origin with | .input _ _ => "axiom" | _ => "plain"
  pure ("cnf(" ++ (← quote row.name) ++ "," ++ role ++ ",(" ++
    (← clause problem row.clause) ++ ")," ++ (← source problem fileLabel row.origin) ++ ").\n")

def render (fileLabel : String) (exported : Export) : Except String String := do
  discard (quote fileLabel)
  let lines ← exported.rows.mapM (renderRow exported.signature fileLabel)
  let text := String.join lines
  if text.utf8ByteSize > 16 * 1024 * 1024 then
    throw "resource-exhaustion: TSTP output exceeds 16 MiB"
  pure text

def exportText (input proof fileLabel : String) : Except String String := do
  let problem ← decodeNamed input
  let certificate ← decodeCertificate proof
  render fileLabel (← build problem certificate)

end Fang.TstpExport
