/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Rows of a goal-task document that come from the original input: every
   declaration with its original role, and the negated conjecture for the
   selected goal. Each row is returned only after the accepted lexer reads the
   expected token kinds, and each has one reading in the accepted v8 grammar.
   Also the premise selection and the list of names of the document. -/
import SourceRow
import RoleInput

namespace Fang.TptpCandidate.FullFof.GoalRows
open Fang.TptpCandidate.FullFof.Grammar Fang.TptpCandidate.FullFof.SourceRow

def roleWord : Roles.Role → String
  | .axiomRole => "axiom"
  | .hypothesis => "hypothesis"
  | .definition => "definition"
  | .assumption => "assumption"
  | .lemma => "lemma"
  | .theoremRole => "theorem"
  | .corollary => "corollary"
  | .conjecture => "conjecture"
  | .negatedConjecture => "negated_conjecture"
  | .plain => "plain"
  | .typeRole => "type"
  | .interpretation => "interpretation"
  | .logic => "logic"
  | .unknown => "unknown"

/-- A decoded declaration printed with its original role. -/
def entryRow (file : String) (entry : Roles.Bytes.Entry) : Except String String :=
  sourceRowAs (roleWord entry.role) entry.original file

theorem entryRow_reads {file : String} {entry : Roles.Bytes.Entry} {row : String}
    (success : entryRow file entry = .ok row) :
    RowReads (roleWord entry.role) file row entry.original.name entry.original.body :=
  sourceRowAs_reads success

/-! The negated conjecture: `fof(<label>, negated_conjecture, (~ <goal>),
    inference(negate_conjecture, [status(cth)], [<goal label>])).` -/

def inferencePrefix : List Piece :=
  [wordPiece "inference", punct '(', wordPiece "negate_conjecture", punct ',', punct '[',
   wordPiece "status", punct '(', wordPiece "cth", punct ')', punct ']', punct ',', punct '[']

def inferenceSuffix : List Piece := [punct ']', punct ')', punct ')', punct '.']

def negatedPieces (label : String) (goal : Name) (formula : Formula) : List Piece :=
  wordPiece "fof" :: punct '(' :: atomPiece label :: punct ',' :: wordPiece "negated_conjecture" ::
    punct ',' :: bodyPieces (.fof (.neg formula)) ++ punct ',' :: inferencePrefix ++
    namePiece goal :: inferenceSuffix

def negatedRow (label : String) (goal : Name) (formula : Formula) : Except String String :=
  SourceRow.checked (negatedPieces label goal formula)

inductive NegatedRowTokens : List Token → Name → Name → Formula → Prop where
  | row {keyword opening labelToken label nameComma roleToken roleComma bodyInput value
         comma before parent goal after}
      (keywordKind : keyword.kind = .legacy (.lower "fof")) (openParen : Punct opening '(')
      (labelName : RecordName labelToken label) (commaName : Punct nameComma ',')
      (roleKind : roleToken.kind = .legacy (.lower "negated_conjecture")) (commaRole : Punct roleComma ',')
      (parsed : CnfBoolean.BodyTokens bodyInput (.fof value) (comma :: (before ++ parent :: after)))
      (commaBody : Punct comma ',') (beforeKinds : before.map Token.kind = kinds inferencePrefix)
      (parentName : RecordName parent goal) (afterKinds : after.map Token.kind = kinds inferenceSuffix) :
      NegatedRowTokens (keyword :: opening :: labelToken :: nameComma :: roleToken :: roleComma :: bodyInput)
        label goal value

def NegatedReads (row : String) (label goal : Name) (value : Formula) : Prop :=
  ∃ tokens, FullFof.tokenize row = .ok tokens ∧ NegatedRowTokens tokens label goal value

theorem recordName_unique {token : Token} {name other : Name}
    (first : RecordName token name) (second : RecordName token other) : name = other := by
  obtain ⟨kind, kindSame, nameSome⟩ := first
  obtain ⟨kind', kindSame', nameSome'⟩ := second
  rw [kindSame] at kindSame'
  injection kindSame' with sameKind
  subst sameKind
  rw [nameSome] at nameSome'
  injection nameSome'

theorem negatedRow_reads {label : String} {goal : Name} {formula : Formula} {row : String}
    (success : negatedRow label goal formula = .ok row) :
    NegatedReads row (.atom label) goal (.neg formula) := by
  obtain ⟨_, tokens, lexed, same⟩ := SourceRow.checked_tokens success
  simp only [negatedPieces, kinds, List.map_cons, List.map_append, List.cons_append, List.append_assoc] at same
  obtain ⟨keyword, tail, rfl, keywordKind, rest⟩ := kinds_cons same
  obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons rest
  obtain ⟨labelToken, tail, rfl, labelKind, rest⟩ := kinds_cons rest
  obtain ⟨nameComma, tail, rfl, nameCommaKind, rest⟩ := kinds_cons rest
  obtain ⟨roleToken, tail, rfl, roleKind, rest⟩ := kinds_cons rest
  obtain ⟨roleComma, tail, rfl, roleCommaKind, rest⟩ := kinds_cons rest
  obtain ⟨bodyTokens, trailer, rfl, bodyKind, rest⟩ := kinds_append rest
  obtain ⟨comma, tail, rfl, commaKind, rest⟩ := kinds_cons rest
  obtain ⟨before, tail, rfl, beforeKinds, rest⟩ := kinds_append rest
  obtain ⟨parent, after, rfl, parentKind, afterKinds⟩ := kinds_cons rest
  have parsed := body_grammar (.fof (.neg formula)) rfl bodyTokens (comma :: (before ++ parent :: after)) bodyKind
    (by simp only [nextBinary, List.head?_cons, Option.bind_some, Function.comp_apply]; rw [commaKind]; rfl)
  exact ⟨_, lexed, .row keywordKind openKind (namePiece_record (name := .atom label) labelKind) nameCommaKind
    roleKind roleCommaKind parsed commaKind beforeKinds (namePiece_record parentKind) afterKinds⟩

theorem kinds_length {left right : List Token} {expected : List Kind}
    (first : left.map Token.kind = expected) (second : right.map Token.kind = expected) :
    left.length = right.length := by
  rw [← List.length_map (f := Token.kind), first, ← second, List.length_map]

theorem NegatedRowTokens.unique {tokens : List Token} {label goal label' goal' : Name} {value value' : Formula}
    (first : NegatedRowTokens tokens label goal value) (second : NegatedRowTokens tokens label' goal' value') :
    label = label' ∧ goal = goal' ∧ value = value' := by
  cases first with
  | row _ _ labelName _ _ _ parsed _ beforeKinds parentName _ =>
  cases second with
  | row _ _ labelName' _ _ _ parsed' _ beforeKinds' parentName' _ =>
  obtain ⟨sameBody, sameRest⟩ := CnfBoolean.body_unique (left := .fof value) (right := .fof value') rfl parsed parsed'
  injection sameBody with sameValue
  injection sameRest with _ sameTail
  obtain ⟨-, sameParent⟩ := List.append_inj sameTail (kinds_length beforeKinds beforeKinds')
  injection sameParent with sameParentToken
  subst sameParentToken
  exact ⟨recordName_unique labelName labelName', recordName_unique parentName parentName', sameValue⟩

theorem NegatedReads.unique {row : String} {label goal label' goal' : Name} {value value' : Formula}
    (first : NegatedReads row label goal value) (second : NegatedReads row label' goal' value') :
    label = label' ∧ goal = goal' ∧ value = value' := by
  obtain ⟨tokens, lexed, parsed⟩ := first
  obtain ⟨tokens', lexed', parsed'⟩ := second
  rw [lexed] at lexed'
  cases lexed'
  exact parsed.unique parsed'

/-- The printed negated conjecture has one reading: the negation of the goal's
    formula, under the given label, citing the goal's name. -/
theorem negatedRow_unique {label : String} {goal : Name} {formula : Formula} {row : String}
    (success : negatedRow label goal formula = .ok row)
    {label' goal' : Name} {value : Formula} (other : NegatedReads row label' goal' value) :
    label' = .atom label ∧ goal' = goal ∧ value = .neg formula := by
  obtain ⟨sameLabel, sameGoal, sameValue⟩ := (negatedRow_reads success).unique other
  exact ⟨sameLabel.symm, sameGoal.symm, sameValue.symm⟩

/-! Premises and names. -/

/-- The entries a goal task keeps as premises, by the role policy of `Roles.premises`. -/
def premiseEntries (values : List Roles.Bytes.Entry) : List Roles.Bytes.Entry :=
  values.filter (fun entry => decide (Roles.classify entry.role = .ok .premise))

/-- Every name of a goal document, compared as TPTP names: each declaration, the
    negated goal, the group, then one per clause row. -/
def goalNames (sources : List Name) (negatedLabel groupLabel : String) (labels : List String) : List Name :=
  sources ++ .atom negatedLabel :: .atom groupLabel :: labels.map Name.atom

/-- Two lists related element by element. -/
inductive Paired {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Paired relation [] []
  | cons {value result values results} (head : relation value result) (tail : Paired relation values results) :
      Paired relation (value :: values) (result :: results)

theorem Paired.imp {α β : Type} {first second : α → β → Prop}
    (step : ∀ value result, first value result → second value result) :
    ∀ {values results}, Paired first values results → Paired second values results
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (step _ _ head) (Paired.imp step tail)

theorem mapM_paired {α β : Type} {f : α → Except String β} :
    ∀ {values : List α} {results : List β}, values.mapM f = .ok results →
      Paired (fun value result => f value = .ok result) values results
  | [], results, success => by
    simp [pure, Except.pure] at success
    subst results
    exact .nil
  | first :: rest, results, success => by
    cases headRun : f first with
    | error reason => simp [List.mapM_cons, headRun, bind, Except.bind] at success
    | ok head =>
      cases tailRun : rest.mapM f with
      | error reason => simp [List.mapM_cons, headRun, tailRun, bind, Except.bind] at success
      | ok tail =>
        simp [List.mapM_cons, headRun, tailRun, bind, Except.bind, pure, Except.pure] at success
        subst results
        exact .cons headRun (mapM_paired tailRun)

#print axioms Fang.TptpCandidate.FullFof.GoalRows.entryRow_reads
#print axioms Fang.TptpCandidate.FullFof.GoalRows.recordName_unique
#print axioms Fang.TptpCandidate.FullFof.GoalRows.negatedRow_reads
#print axioms Fang.TptpCandidate.FullFof.GoalRows.kinds_length
#print axioms Fang.TptpCandidate.FullFof.GoalRows.NegatedRowTokens.unique
#print axioms Fang.TptpCandidate.FullFof.GoalRows.NegatedReads.unique
#print axioms Fang.TptpCandidate.FullFof.GoalRows.negatedRow_unique
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Paired.imp
#print axioms Fang.TptpCandidate.FullFof.GoalRows.mapM_paired

end Fang.TptpCandidate.FullFof.GoalRows
