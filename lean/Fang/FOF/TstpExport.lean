/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Experimental FOF exporter. Text/ancestry proofs are required before enabling
   this path in the ATP command. Existing CNF exporter code is reused unchanged. -/
import TstpExport
import Fang.FOF.VersionedCheck

namespace Fang.FofTstpExport

structure Leaf where
  declaration : Nat
  localClause : Nat
  sourceName : String
  rawName : String
  body : GroundFOF.Declaration
  clause : Clause

def leafName (declaration localClause : Nat) : String :=
  s!"fang:clausify:{declaration}:{localClause}"

def declarationLeaves (body : GroundFOF.Declaration) (declaration : Nat)
    (sourceName : String) : List Leaf :=
  body.clauses.zipIdx.map fun (clause, localClause) => {
    declaration, localClause, sourceName, body, clause
    rawName := match body with
      | .cnf _ => sourceName
      | .fof _ => leafName declaration localClause
  }

def collectLeaves : List GroundFOF.Declaration → List String → Nat → Except String (List Leaf)
  | [], [], _ => pure []
  | body :: rest, name :: names, start => do
    if !Frontend.lowerName name then
      throw "export-error: invalid source declaration name"
    pure (declarationLeaves body start name ++ (← collectLeaves rest names (start + 1)))
  | _, _, _ => throw "export-error: source declaration/name count mismatch"

/-- Retain both source and local clause positions before stable deduplication. -/
def leaves (decoded : FOFFrontend.Decoded) : Except String (List Leaf) :=
  collectLeaves decoded.declarations decoded.state.clauseNames 0

def formula (problem : TstpExport.NamedProblem) : GroundFOF.Formula → Except String String
  | .atom atom => TstpExport.literal problem { positive := true, atom }
  | .truth => pure "$true"
  | .falsity => pure "$false"
  | .neg body => do pure ("~(" ++ (← formula problem body) ++ ")")
  | .conj left right => do
    pure ("(" ++ (← formula problem left) ++ " & " ++ (← formula problem right) ++ ")")
  | .disj left right => do
    pure ("(" ++ (← formula problem left) ++ " | " ++ (← formula problem right) ++ ")")
  | .implies left right => do
    pure ("(" ++ (← formula problem left) ++ " => " ++ (← formula problem right) ++ ")")

def sourceFormula (problem : TstpExport.NamedProblem) (fileLabel sourceName : String)
    (body : GroundFOF.Formula) : Except String String := do
  pure ("fof(" ++ (← TstpExport.quote sourceName) ++ ",axiom,(" ++
    (← formula problem body) ++ "),file(" ++ (← TstpExport.quote fileLabel) ++ "," ++
    (← TstpExport.quote sourceName) ++ ")).\n")

def clausifiedRow (problem : TstpExport.NamedProblem) (leaf : Leaf) : Except String String := do
  pure ("cnf(" ++ (← TstpExport.quote leaf.rawName) ++ ",plain,(" ++
    (← TstpExport.clause problem leaf.clause) ++
    s!"),inference(fang_clausify,[status(thm),source_index({leaf.declaration}),clause_index({leaf.localClause})],[" ++
    (← TstpExport.quote leaf.sourceName) ++ "])).\n")

structure Export where
  decoded : FOFFrontend.Decoded
  leaves : List Leaf
  trace : TstpExport.Export

def build (decoded : FOFFrontend.Decoded) (certificate : Certificate) : Except String Export := do
  let leaves ← leaves decoded
  if !decide (leaves.map Leaf.clause = GroundFOF.lowerDeclarations decoded.declarations) then
    throw "export-error: lowered clause positions differ"
  let problem : TstpExport.NamedProblem := {
    signature := FOFVersioned.signature decoded
    functions := decoded.state.functions
    predicates := decoded.state.predicates
    names := leaves.map Leaf.rawName
  }
  let trace ← TstpExport.build problem certificate
  pure { decoded, leaves, trace }

/-- Replace generated input-file leaves with original FOF axioms followed by
    explicit clausification rows. Derived resolution/factoring rows are reused. -/
def render (fileLabel : String) (exported : Export) : Except String String := do
  discard (TstpExport.quote fileLabel)
  let problem := exported.trace.signature
  let mut emittedFormulas : List Nat := []
  let mut lines : List String := []
  for row in exported.trace.rows do
    match row.origin with
    | .input sourceIndex _ =>
      let some leaf := exported.leaves[sourceIndex]?
        | throw "export-error: missing original leaf ancestry"
      if row.name != leaf.rawName || !decide (row.clause = leaf.clause) then
        throw "export-error: trace leaf differs from original ancestry"
      match leaf.body with
      | .cnf _ =>
        lines := lines ++ [← TstpExport.renderRow problem fileLabel row]
      | .fof body =>
        if !emittedFormulas.contains leaf.declaration then
          lines := lines ++ [← sourceFormula problem fileLabel leaf.sourceName body]
          emittedFormulas := leaf.declaration :: emittedFormulas
        lines := lines ++ [← clausifiedRow problem leaf]
    | _ => lines := lines ++ [← TstpExport.renderRow problem fileLabel row]
  let text := String.join lines
  if text.utf8ByteSize > 16 * 1024 * 1024 then
    throw "resource-exhaustion: TSTP output exceeds 16 MiB"
  pure text

def exportText (input proof fileLabel : String) : Except String String := do
  let decoded ← FOFFrontend.decode input
  let certificate ← FOFVersioned.decodeCertificate proof
  render fileLabel (← build decoded certificate)

end Fang.FofTstpExport
