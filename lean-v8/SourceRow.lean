/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   TSTP source rows for decoded version-8 declarations. The renderer emits each
   token's expected kind with its spelling. At export time the accepted byte
   lexer must return exactly those kinds. Any token list with those kinds is a
   derivation in the accepted v8 grammar for the same name and body, and the
   accepted uniqueness theorems make that reading unique. -/
import CnfBooleanUnique

namespace Fang.TptpCandidate.FullFof.SourceRow
open Fang.TptpCandidate.FullFof.Grammar

abbrev Piece := Kind × String

def kinds (pieces : List Piece) : List Kind := pieces.map Prod.fst

def text (pieces : List Piece) : String := String.intercalate " " (pieces.map Prod.snd)

def isLowerWord (value : String) : Bool :=
  match value.toList with
  | first :: rest => TptpCandidate.lower first && rest.all TptpCandidate.word
  | [] => false

def escapeChar (c : Char) : String :=
  if c == '\'' || c == '\\' then "\\" ++ c.toString else c.toString

def quotedText (value : String) : String := "'" ++ String.join (value.toList.map escapeChar) ++ "'"

/-- Lower words print bare; every other name is quoted with escapes. -/
def atomPiece (value : String) : Piece :=
  if isLowerWord value then (.legacy (.lower value), value) else (.legacy (.quoted value), quotedText value)

def namePiece : Name → Piece
  | .atom value => atomPiece value
  | .integer value => (.legacy (.integer value), value)

def punct (c : Char) : Piece := (.legacy (.punctuation c), c.toString)

def variablePiece (value : String) : Piece := (.legacy (.variable value), value)

def wordPiece (value : String) : Piece := (.legacy (.lower value), value)

mutual
def termPieces : Source.Term → List Piece
  | .var name => [variablePiece name]
  | .app name [] => [atomPiece name]
  | .app name arguments => atomPiece name :: punct '(' :: argumentPieces arguments ++ [punct ')']

def argumentPieces : List Source.Term → List Piece
  | [] => []
  | [term] => termPieces term
  | term :: rest => termPieces term ++ punct ',' :: argumentPieces rest
end

def binaryPiece : Binary → Piece
  | .conj => punct '&'
  | .disj => punct '|'
  | .implies => (.legacy .implies, "=>")
  | .reverse => (.reverse, "<=")
  | .iff => (.iff, "<=>")
  | .xor => (.xor, "<~>")
  | .nand => (.nand, "~&")
  | .nor => (.nor, "~|")

def equalityPiece : Piece := (.legacy (.equality true), "=")

/-- A unit: binary formulas carry their own parentheses, so every operand is a unit
    and a quantifier binds exactly the next unit. -/
def unitPieces : Formula → List Piece
  | .truth => [(.legacy .truth, "$true")]
  | .falsity => [(.legacy .falsity, "$false")]
  | .atom name args => termPieces (.app name args)
  | .equal left right => termPieces left ++ equalityPiece :: termPieces right
  | .neg body => punct '~' :: unitPieces body
  | .pair operator left right =>
      punct '(' :: unitPieces left ++ binaryPiece operator :: unitPieces right ++ [punct ')']
  | .all name body => punct '!' :: punct '[' :: variablePiece name :: punct ']' :: punct ':' :: unitPieces body
  | .ex name body => punct '?' :: punct '[' :: variablePiece name :: punct ']' :: punct ':' :: unitPieces body

/-- The formula inside the body parentheses: a top-level binary formula is not
    wrapped twice. -/
def formulaPieces : Formula → List Piece
  | .pair operator left right => unitPieces left ++ binaryPiece operator :: unitPieces right
  | value => unitPieces value

/-- CNF literals the accepted Boolean CNF grammar can read. -/
def literalOk : Formula → Bool
  | .truth | .falsity | .atom _ _ | .equal _ _ => true
  | .neg .truth | .neg .falsity | .neg (.atom _ _) | .neg (.equal _ _) => true
  | _ => false

def literalPieces : Formula → List Piece
  | .neg value => punct '~' :: unitPieces value
  | value => unitPieces value

def disjunctionPieces : List Formula → List Piece
  | [] => []
  | [value] => literalPieces value
  | value :: rest => literalPieces value ++ punct '|' :: disjunctionPieces rest

def bodyOk : Body → Bool
  | .fof _ => true
  | .cnf values => !values.isEmpty && values.all literalOk

def bodyPieces : Body → List Piece
  | .fof value => punct '(' :: formulaPieces value ++ [punct ')']
  | .cnf values => punct '(' :: disjunctionPieces values ++ [punct ')']

def trailerPieces (file : String) (name : Name) : List Piece :=
  [punct ',', wordPiece "file", punct '(', (.legacy (.quoted file), quotedText file), punct ',',
   namePiece name, punct ')', punct ')', punct '.']

/-- The role is a parameter: `axiom` now, conjecture roles for the signed path later. -/
def rowPieces (role file : String) (declaration : Declaration) : List Piece :=
  wordPiece (BodyKind declaration.body) :: punct '(' :: namePiece declaration.name :: punct ',' ::
    wordPiece role :: punct ',' :: bodyPieces declaration.body ++ trailerPieces file declaration.name

/-- Return the text only if the accepted lexer reads exactly the expected kinds. -/
def checked (pieces : List Piece) : Except String String :=
  match FullFof.tokenize (text pieces) with
  | .error _ => .error "export-error: source row does not lex"
  | .ok tokens =>
    if tokens.map Token.kind = kinds pieces then .ok (text pieces)
    else .error "export-error: source row tokens differ from the declaration"

def sourceRowAs (role : String) (declaration : Declaration) (file : String) : Except String String :=
  if bodyOk declaration.body then checked (rowPieces role file declaration)
  else .error "export-error: CNF body is empty or has an unsupported literal"

def sourceRow (declaration : Declaration) (file : String) : Except String String :=
  sourceRowAs "axiom" declaration file

def label (name : Name) : Except String String := checked [namePiece name]

def sourceRowsAs (role file : String) : List Declaration → Except String (List (String × String))
  | [] => .ok []
  | declaration :: rest => do
    let labelText ← label declaration.name
    let row ← sourceRowAs role declaration file
    let tail ← sourceRowsAs role file rest
    pure ((labelText, row) :: tail)

/-- Labels and rows in declaration order. -/
def sourceRows (declarations : List Declaration) (file : String) : Except String (List (String × String)) :=
  sourceRowsAs "axiom" file declarations

/-- The whole row: keyword, name, role, the accepted v8 body grammar, and the
    `file` annotation repeating the name. -/
inductive RowTokens (role file : String) : List Token → Name → Body → Prop where
  | row {keyword opening nameToken name nameComma roleToken roleComma bodyInput body
         bodyComma fileWord fileOpen fileToken fileComma labelToken fileClose closing dot}
      (keywordKind : keyword.kind = .legacy (.lower (BodyKind body)))
      (openParen : Punct opening '(') (recordName : RecordName nameToken name)
      (commaName : Punct nameComma ',') (roleKind : roleToken.kind = .legacy (.lower role))
      (commaRole : Punct roleComma ',')
      (parsed : CnfBoolean.BodyTokens bodyInput body
        [bodyComma, fileWord, fileOpen, fileToken, fileComma, labelToken, fileClose, closing, dot])
      (commaBody : Punct bodyComma ',') (fileKind : fileWord.kind = .legacy (.lower "file"))
      (fileParen : Punct fileOpen '(') (fileName : fileToken.kind = .legacy (.quoted file))
      (commaFile : Punct fileComma ',') (labelName : RecordName labelToken name)
      (fileEnd : Punct fileClose ')') (closeParen : Punct closing ')') (period : Punct dot '.') :
      RowTokens role file (keyword :: opening :: nameToken :: nameComma :: roleToken :: roleComma :: bodyInput)
        name body

def RowReads (role file row : String) (name : Name) (body : Body) : Prop :=
  ∃ tokens, FullFof.tokenize row = .ok tokens ∧ RowTokens role file tokens name body

/-! Splitting a token list by its kinds. -/

theorem kinds_cons {tokens : List Token} {kind : Kind} {rest : List Kind}
    (same : tokens.map Token.kind = kind :: rest) :
    ∃ token tail, tokens = token :: tail ∧ token.kind = kind ∧ tail.map Token.kind = rest :=
  List.map_eq_cons_iff.mp same

theorem kinds_append {tokens : List Token} {left right : List Kind}
    (same : tokens.map Token.kind = left ++ right) :
    ∃ first second, tokens = first ++ second ∧ first.map Token.kind = left ∧ second.map Token.kind = right :=
  List.map_eq_append_iff.mp same

theorem kinds_nil {tokens : List Token} (same : tokens.map Token.kind = []) : tokens = [] :=
  List.map_eq_nil_iff.mp same

theorem atomPiece_atomic (value : String) : atomic (atomPiece value).1 = some value := by
  unfold atomPiece; split <;> rfl

theorem namePiece_record {token : Token} {name : Name} (kind : token.kind = (namePiece name).1) :
    RecordName token name := by
  cases name with
  | atom value =>
    by_cases lowerWord : isLowerWord value = true
    · simp only [namePiece, atomPiece, lowerWord, ↓reduceIte] at kind
      exact ⟨.lower value, kind, rfl⟩
    · simp only [namePiece, atomPiece, lowerWord, Bool.false_eq_true, ↓reduceIte] at kind
      exact ⟨.quoted value, kind, rfl⟩
  | integer value => exact ⟨.integer value, kind, rfl⟩

/-- A token of a given kind is not the start of a given punctuation. -/
theorem isChar_head {c : Char} {token : Token} {rest : List Token} {kind : Kind}
    (same : token.kind = kind) (differs : kind ≠ .legacy (.punctuation c)) :
    isChar c (token :: rest) = false := by
  simp [isChar, same, differs]

theorem punct_head {c d : Char} {token : Token} {rest : List Token}
    (same : Punct token d) (differs : d ≠ c) : isChar c (token :: rest) = false :=
  isChar_head same (by intro equal; exact differs (by injection equal with equal; injection equal))

/-! Terms. -/

mutual
theorem term_grammar (term : Source.Term) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (termPieces term)) (boundary : isChar '(' suffix = false) :
    TermTokens (tokens ++ suffix) term suffix := by
  cases term with
  | var name =>
    simp only [termPieces, kinds, List.map_cons, List.map_nil] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain rfl := kinds_nil rest
    exact .variable kind
  | app name arguments =>
    cases arguments with
    | nil =>
      simp only [termPieces, kinds, List.map_cons, List.map_nil] at same
      obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
      obtain rfl := kinds_nil rest
      exact .constant (by rw [kind]; exact atomPiece_atomic name) boundary
    | cons first others =>
      simp only [termPieces, kinds, List.map_cons, List.map_append, List.map_nil] at same
      obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
      obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons rest
      obtain ⟨args, closingList, rfl, argsKind, closeKind⟩ := kinds_append rest
      obtain ⟨closing, empty, rfl, closingKind, emptyKind⟩ := kinds_cons closeKind
      obtain rfl := kinds_nil emptyKind
      have child := arguments_grammar (first :: others) (by simp) args closing suffix argsKind closingKind
      have parsed := TermTokens.application (by rw [kind]; exact atomPiece_atomic name) openKind child closingKind
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using parsed
termination_by sizeOf term

theorem arguments_grammar (terms : List Source.Term) (nonempty : terms ≠ []) (tokens : List Token)
    (closing : Token) (suffix : List Token)
    (same : tokens.map Token.kind = kinds (argumentPieces terms)) (closingKind : Punct closing ')') :
    ArgumentsTokens (tokens ++ closing :: suffix) terms (closing :: suffix) := by
  cases terms with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    cases rest with
    | nil =>
      have head := term_grammar first tokens (closing :: suffix) (by simpa only [argumentPieces] using same)
        (punct_head closingKind (by decide))
      exact .one head (punct_head closingKind (by decide))
    | cons second tail =>
      simp only [argumentPieces, kinds, List.map_cons, List.map_append] at same
      obtain ⟨firstTokens, others, rfl, firstKind, othersKind⟩ := kinds_append same
      obtain ⟨comma, middle, rfl, commaKind, middleKind⟩ := kinds_cons othersKind
      have child := arguments_grammar (second :: tail) (by simp) middle closing suffix middleKind closingKind
      have head := term_grammar first firstTokens (comma :: (middle ++ closing :: suffix)) firstKind
        (punct_head commaKind (by decide))
      have parsed := ArgumentsTokens.more head commaKind child
      simpa only [List.cons_append, List.append_assoc] using parsed
termination_by sizeOf terms
end

/-! What may follow a unit or a formula in a printed row. -/

def UnitEnd (rest : List Token) : Prop := isChar '(' rest = false ∧ NoEquality rest

def FormulaEnd (rest : List Token) : Prop := UnitEnd rest ∧ nextBinary rest = none

theorem kind_unit_end {token : Token} {rest : List Token} {kind : Kind} (same : token.kind = kind)
    (notOpen : kind ≠ .legacy (.punctuation '(')) (notEquality : ∀ positive, kind ≠ .legacy (.equality positive)) :
    UnitEnd (token :: rest) := by
  refine ⟨isChar_head same notOpen, ?_⟩
  intro other tail positive shape
  obtain ⟨rfl, rfl⟩ := List.cons.inj shape
  rw [same]
  exact notEquality positive

theorem punct_unit_end {token : Token} {rest : List Token} {c : Char} (same : Punct token c)
    (notOpen : c ≠ '(') : UnitEnd (token :: rest) :=
  kind_unit_end same (by intro equal; exact notOpen (by injection equal with equal; injection equal))
    (by intro positive equal; injection equal with equal; cases equal)

theorem punct_formula_end {token : Token} {rest : List Token} {c : Char} (same : Punct token c)
    (notOpen : c ≠ '(') (notOperator : c ≠ '&' ∧ c ≠ '|') : FormulaEnd (token :: rest) := by
  refine ⟨punct_unit_end same notOpen, ?_⟩
  simp only [nextBinary, List.head?_cons, Option.bind_some, Function.comp_apply]
  rw [same]
  simp [binary, notOperator.1, notOperator.2]

theorem binaryPiece_binary {token : Token} {operator : Binary} (same : token.kind = (binaryPiece operator).1) :
    binary token.kind = some operator := by
  rw [same]; cases operator <;> rfl

theorem binaryPiece_end {token : Token} {rest : List Token} {operator : Binary}
    (same : token.kind = (binaryPiece operator).1) : UnitEnd (token :: rest) :=
  kind_unit_end same (by cases operator <;> decide) (by intro positive; cases operator <;> simp [binaryPiece, punct])

/-! Atoms, units and formulas. -/

theorem atom_grammar_predicate (name : String) (args : List Source.Term) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (termPieces (.app name args))) (finish : UnitEnd suffix) :
    AtomTokens (tokens ++ suffix) (.atom name args) suffix :=
  .predicate (term_grammar (.app name args) tokens suffix same finish.1) finish.2

theorem atom_grammar_equal (left right : Source.Term) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (termPieces left ++ equalityPiece :: termPieces right))
    (finish : UnitEnd suffix) :
    AtomTokens (tokens ++ suffix) (.equal left right) suffix := by
  simp only [kinds, List.map_append, List.map_cons] at same
  obtain ⟨leftTokens, others, rfl, leftKind, othersKind⟩ := kinds_append same
  obtain ⟨operator, rightTokens, rfl, operatorKind, rightKind⟩ := kinds_cons othersKind
  have first := term_grammar left leftTokens (operator :: (rightTokens ++ suffix)) leftKind
    (isChar_head operatorKind (by decide))
  have second := term_grammar right rightTokens suffix rightKind finish.1
  have parsed := AtomTokens.equality first operatorKind second
  simpa only [List.cons_append, List.append_assoc, ite_true] using parsed

theorem unit_grammar : ∀ (value : Formula) (tokens suffix : List Token),
    tokens.map Token.kind = kinds (unitPieces value) → UnitEnd suffix →
    UnitTokens (tokens ++ suffix) value suffix
  | .truth, tokens, suffix, same, _ => by
    simp only [unitPieces, kinds, List.map_cons, List.map_nil] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain rfl := kinds_nil rest
    exact .truth kind
  | .falsity, tokens, suffix, same, _ => by
    simp only [unitPieces, kinds, List.map_cons, List.map_nil] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain rfl := kinds_nil rest
    exact .falsity kind
  | .atom name args, tokens, suffix, same, finish =>
    .atom (atom_grammar_predicate name args tokens suffix same finish)
  | .equal left right, tokens, suffix, same, finish =>
    .atom (atom_grammar_equal left right tokens suffix same finish)
  | .neg body, tokens, suffix, same, finish => by
    simp only [unitPieces, kinds, List.map_cons] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    exact .neg kind (unit_grammar body tail suffix rest finish)
  | .pair operator left right, tokens, suffix, same, _ => by
    simp only [unitPieces, kinds, List.map_cons, List.map_append, List.map_nil, List.append_assoc, List.cons_append] at same
    obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons same
    obtain ⟨leftTokens, others, rfl, leftKind, othersKind⟩ := kinds_append rest
    obtain ⟨token, tail, rfl, operatorKind, rest⟩ := kinds_cons othersKind
    obtain ⟨rightTokens, closingList, rfl, rightKind, closeKind⟩ := kinds_append rest
    obtain ⟨closing, empty, rfl, closingKind, emptyKind⟩ := kinds_cons closeKind
    obtain rfl := kinds_nil emptyKind
    have closeEnd := punct_formula_end (rest := suffix) closingKind (by decide) (by decide)
    have second := unit_grammar right rightTokens (closing :: suffix) rightKind closeEnd.1
    have first := unit_grammar left leftTokens (token :: (rightTokens ++ closing :: suffix)) leftKind
      (binaryPiece_end operatorKind)
    have chain := ChainTokens.one (left := left) (binaryPiece_binary operatorKind) second
      (by rw [closeEnd.2]; simp)
    have parsed := UnitTokens.group openKind (FormulaTokens.binary first chain) closingKind
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using parsed
  | .all name body, tokens, suffix, same, finish => by
    simp only [unitPieces, kinds, List.map_cons] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons rest
    obtain ⟨binder, tail, rfl, binderKind, rest⟩ := kinds_cons rest
    obtain ⟨closing, tail, rfl, closingKind, rest⟩ := kinds_cons rest
    obtain ⟨colon, bodyTokens, rfl, colonKind, rest⟩ := kinds_cons rest
    have binders := BindersTokens.one (rest := closing :: colon :: (bodyTokens ++ suffix)) binderKind
      (punct_head closingKind (by decide)) (punct_head closingKind (by decide))
    have parsed := UnitTokens.quantified (universal := true) kind openKind binders closingKind colonKind
      (unit_grammar body bodyTokens suffix rest finish)
    simpa [close] using parsed
  | .ex name body, tokens, suffix, same, finish => by
    simp only [unitPieces, kinds, List.map_cons] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons rest
    obtain ⟨binder, tail, rfl, binderKind, rest⟩ := kinds_cons rest
    obtain ⟨closing, tail, rfl, closingKind, rest⟩ := kinds_cons rest
    obtain ⟨colon, bodyTokens, rfl, colonKind, rest⟩ := kinds_cons rest
    have binders := BindersTokens.one (rest := closing :: colon :: (bodyTokens ++ suffix)) binderKind
      (punct_head closingKind (by decide)) (punct_head closingKind (by decide))
    have parsed := UnitTokens.quantified (universal := false) kind openKind binders closingKind colonKind
      (unit_grammar body bodyTokens suffix rest finish)
    simpa [close] using parsed

theorem formula_grammar (value : Formula) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (formulaPieces value)) (finish : FormulaEnd suffix) :
    FormulaTokens (tokens ++ suffix) value suffix := by
  cases value with
  | pair operator left right =>
    simp only [formulaPieces, kinds, List.map_append, List.map_cons] at same
    obtain ⟨leftTokens, others, rfl, leftKind, othersKind⟩ := kinds_append same
    obtain ⟨token, rightTokens, rfl, operatorKind, rightKind⟩ := kinds_cons othersKind
    have second := unit_grammar right rightTokens suffix rightKind finish.1
    have first := unit_grammar left leftTokens (token :: (rightTokens ++ suffix)) leftKind
      (binaryPiece_end operatorKind)
    have chain := ChainTokens.one (left := left) (binaryPiece_binary operatorKind) second
      (by rw [finish.2]; simp)
    simpa only [List.cons_append, List.append_assoc] using FormulaTokens.binary first chain
  | truth => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2
  | falsity => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2
  | atom name args => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2
  | equal left right => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2
  | neg body => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2
  | all name body => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2
  | ex name body => exact .one (unit_grammar _ tokens suffix same finish.1) finish.2

/-! Boolean CNF literals and clauses. -/

theorem atomic_grammar (value : Formula) (atomic : CnfBoolean.IsAtomic value) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (unitPieces value)) (finish : UnitEnd suffix) :
    CnfBoolean.AtomicTokens (tokens ++ suffix) value suffix := by
  cases value with
  | truth =>
    simp only [unitPieces, kinds, List.map_cons, List.map_nil] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain rfl := kinds_nil rest
    exact .truth kind
  | falsity =>
    simp only [unitPieces, kinds, List.map_cons, List.map_nil] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    obtain rfl := kinds_nil rest
    exact .falsity kind
  | atom name args => exact .ordinary (atom_grammar_predicate name args tokens suffix same finish)
  | equal left right => exact .ordinary (atom_grammar_equal left right tokens suffix same finish)
  | neg _ | pair _ _ _ | all _ _ | ex _ _ => exact False.elim atomic

theorem literal_grammar (value : Formula) (ok : literalOk value = true) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (literalPieces value)) (finish : UnitEnd suffix) :
    CnfBoolean.LiteralTokens (tokens ++ suffix) value suffix := by
  cases value with
  | neg inner =>
    have atomic : CnfBoolean.IsAtomic inner := by
      cases inner <;> simp_all [literalOk, CnfBoolean.IsAtomic]
    simp only [literalPieces, kinds, List.map_cons] at same
    obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
    exact .negative kind (.bare (atomic_grammar inner atomic tail suffix rest finish)) atomic
  | truth => exact .positive (atomic_grammar .truth trivial tokens suffix same finish)
  | falsity => exact .positive (atomic_grammar .falsity trivial tokens suffix same finish)
  | atom name args => exact .positive (atomic_grammar (.atom name args) trivial tokens suffix same finish)
  | equal left right => exact .positive (atomic_grammar (.equal left right) trivial tokens suffix same finish)
  | pair _ _ _ | all _ _ | ex _ _ => simp [literalOk] at ok

theorem disjunction_grammar : ∀ (values : List Formula), values ≠ [] → (∀ value ∈ values, literalOk value = true) →
    ∀ (tokens : List Token) (closing : Token) (suffix : List Token),
    tokens.map Token.kind = kinds (disjunctionPieces values) → Punct closing ')' →
    CnfBoolean.DisjunctionTokens (tokens ++ closing :: suffix) values (closing :: suffix)
  | [], nonempty, _, _, _, _, _, _ => False.elim (nonempty rfl)
  | [value], _, ok, tokens, closing, suffix, same, closingKind => by
    have closeEnd := punct_formula_end (rest := suffix) closingKind (by decide) (by decide)
    exact .one (literal_grammar value (ok value (by simp)) tokens (closing :: suffix) same closeEnd.1)
      (punct_head closingKind (by decide))
  | value :: next :: rest, _, ok, tokens, closing, suffix, same, closingKind => by
    simp only [disjunctionPieces, kinds, List.map_append, List.map_cons] at same
    obtain ⟨first, others, rfl, firstKind, othersKind⟩ := kinds_append same
    obtain ⟨bar, middle, rfl, barKind, middleKind⟩ := kinds_cons othersKind
    have tail := disjunction_grammar (next :: rest) (by simp)
      (fun item member => ok item (by simp_all)) middle closing suffix middleKind closingKind
    have head := literal_grammar value (ok value (by simp)) first (bar :: (middle ++ closing :: suffix))
      firstKind (punct_unit_end barKind (by decide))
    simpa only [List.cons_append, List.append_assoc] using CnfBoolean.DisjunctionTokens.more head barKind tail

theorem body_grammar (value : Body) (ok : bodyOk value = true) (tokens suffix : List Token)
    (same : tokens.map Token.kind = kinds (bodyPieces value)) (finish : nextBinary suffix = none) :
    CnfBoolean.BodyTokens (tokens ++ suffix) value suffix := by
  cases value with
  | fof formula =>
    simp only [bodyPieces, kinds, List.map_cons, List.map_append, List.map_nil, List.cons_append] at same
    obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons same
    obtain ⟨inner, closingList, rfl, innerKind, closeKind⟩ := kinds_append rest
    obtain ⟨closing, empty, rfl, closingKind, emptyKind⟩ := kinds_cons closeKind
    obtain rfl := kinds_nil emptyKind
    have closeEnd := punct_formula_end (rest := suffix) closingKind (by decide) (by decide)
    have parsed := FormulaTokens.one
      (UnitTokens.group openKind (formula_grammar formula inner (closing :: suffix) innerKind closeEnd) closingKind)
      finish
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using CnfBoolean.BodyTokens.fof parsed
  | cnf values =>
    simp only [bodyOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at ok
    simp only [bodyPieces, kinds, List.map_cons, List.map_append, List.map_nil, List.cons_append] at same
    obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons same
    obtain ⟨inner, closingList, rfl, innerKind, closeKind⟩ := kinds_append rest
    obtain ⟨closing, empty, rfl, closingKind, emptyKind⟩ := kinds_cons closeKind
    obtain rfl := kinds_nil emptyKind
    have clause := CnfBoolean.ClauseTokens.paren openKind
      (.bare (disjunction_grammar values ok.1 ok.2 inner closing suffix innerKind closingKind)) closingKind
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using CnfBoolean.BodyTokens.cnf clause

/-! The whole row. -/

theorem row_grammar (role file : String) (declaration : Declaration) (ok : bodyOk declaration.body = true)
    (tokens : List Token) (same : tokens.map Token.kind = kinds (rowPieces role file declaration)) :
    RowTokens role file tokens declaration.name declaration.body := by
  simp only [rowPieces, trailerPieces, kinds, List.map_cons, List.map_append, List.map_nil, List.cons_append] at same
  obtain ⟨keyword, tail, rfl, keywordKind, rest⟩ := kinds_cons same
  obtain ⟨opening, tail, rfl, openKind, rest⟩ := kinds_cons rest
  obtain ⟨nameToken, tail, rfl, nameKind, rest⟩ := kinds_cons rest
  obtain ⟨nameComma, tail, rfl, nameCommaKind, rest⟩ := kinds_cons rest
  obtain ⟨roleToken, tail, rfl, roleKind, rest⟩ := kinds_cons rest
  obtain ⟨roleComma, tail, rfl, roleCommaKind, rest⟩ := kinds_cons rest
  obtain ⟨bodyTokens, trailer, rfl, bodyKind, rest⟩ := kinds_append rest
  obtain ⟨bodyComma, tail, rfl, bodyCommaKind, rest⟩ := kinds_cons rest
  obtain ⟨fileWord, tail, rfl, fileWordKind, rest⟩ := kinds_cons rest
  obtain ⟨fileOpen, tail, rfl, fileOpenKind, rest⟩ := kinds_cons rest
  obtain ⟨fileToken, tail, rfl, fileTokenKind, rest⟩ := kinds_cons rest
  obtain ⟨fileComma, tail, rfl, fileCommaKind, rest⟩ := kinds_cons rest
  obtain ⟨labelToken, tail, rfl, labelKind, rest⟩ := kinds_cons rest
  obtain ⟨fileClose, tail, rfl, fileCloseKind, rest⟩ := kinds_cons rest
  obtain ⟨closing, tail, rfl, closingKind, rest⟩ := kinds_cons rest
  obtain ⟨dot, tail, rfl, dotKind, rest⟩ := kinds_cons rest
  obtain rfl := kinds_nil rest
  have parsed := body_grammar declaration.body ok bodyTokens
    [bodyComma, fileWord, fileOpen, fileToken, fileComma, labelToken, fileClose, closing, dot] bodyKind
    (by simp only [nextBinary, List.head?_cons, Option.bind_some, Function.comp_apply]; rw [bodyCommaKind]; rfl)
  exact .row keywordKind openKind (namePiece_record nameKind) nameCommaKind roleKind roleCommaKind parsed
    bodyCommaKind fileWordKind fileOpenKind fileTokenKind fileCommaKind (namePiece_record labelKind)
    fileCloseKind closingKind dotKind

theorem RowTokens.unique {role file role' file' tokens name body name' body'}
    (first : RowTokens role file tokens name body) (second : RowTokens role' file' tokens name' body') :
    name = name' ∧ body = body' ∧ role = role' ∧ file = file' := by
  cases first with
  | row keywordKind _ recordName _ roleKind _ parsed _ _ _ fileName _ _ _ _ _ =>
  cases second with
  | row keywordKind' _ recordName' _ roleKind' _ parsed' _ _ _ fileName' _ _ _ _ _ =>
  have kindSame : BodyKind body = BodyKind body' := by
    rw [keywordKind] at keywordKind'
    injection keywordKind' with same
    injection same
  obtain ⟨rfl, restSame⟩ := CnfBoolean.body_unique kindSame parsed parsed'
  simp only [List.cons.injEq] at restSame
  obtain ⟨-, -, -, rfl, -, -, -, -, -⟩ := restSame
  obtain ⟨kind, nameKind, nameSome⟩ := recordName
  obtain ⟨kind', nameKind', nameSome'⟩ := recordName'
  rw [nameKind] at nameKind'
  injection nameKind' with sameKind
  subst sameKind
  rw [nameSome] at nameSome'
  injection nameSome' with sameName
  rw [roleKind] at roleKind'
  injection roleKind' with sameRole
  injection sameRole with sameRole
  rw [fileName] at fileName'
  injection fileName' with sameFile
  injection sameFile with sameFile
  exact ⟨sameName, rfl, sameRole, sameFile⟩

theorem RowReads.unique {role file row name body role' file' name' body'}
    (first : RowReads role file row name body) (second : RowReads role' file' row name' body') :
    name = name' ∧ body = body' ∧ role = role' ∧ file = file' := by
  obtain ⟨tokens, lexed, parsed⟩ := first
  obtain ⟨tokens', lexed', parsed'⟩ := second
  rw [lexed] at lexed'
  cases lexed'
  exact parsed.unique parsed'

/-! The export check and the interface. -/

theorem checked_tokens {pieces : List Piece} {row : String} (success : checked pieces = .ok row) :
    row = text pieces ∧ ∃ tokens, FullFof.tokenize row = .ok tokens ∧ tokens.map Token.kind = kinds pieces := by
  unfold checked at success
  split at success
  · cases success
  · rename_i tokens lexed
    split at success
    · rename_i same
      cases success
      exact ⟨rfl, tokens, lexed, same⟩
    · cases success

theorem sourceRowAs_reads {role declaration file row}
    (success : sourceRowAs role declaration file = .ok row) :
    RowReads role file row declaration.name declaration.body := by
  unfold sourceRowAs at success
  split at success
  · rename_i ok
    obtain ⟨_, tokens, lexed, same⟩ := checked_tokens success
    exact ⟨tokens, lexed, row_grammar role file declaration ok tokens same⟩
  · cases success

/-- The printed row has one reading, and it is the declaration's name and body
    (hence the same `Formula`), with the requested role and file label. -/
theorem sourceRowAs_unique {role declaration file row}
    (success : sourceRowAs role declaration file = .ok row)
    {role' file' name body} (other : RowReads role' file' row name body) :
    name = declaration.name ∧ body = declaration.body ∧ role' = role ∧ file' = file := by
  obtain ⟨sameName, sameBody, sameRole, sameFile⟩ := (sourceRowAs_reads success).unique other
  exact ⟨sameName.symm, sameBody.symm, sameRole.symm, sameFile.symm⟩

theorem sourceRow_reads {declaration file row} (success : sourceRow declaration file = .ok row) :
    RowReads "axiom" file row declaration.name declaration.body :=
  sourceRowAs_reads success

theorem sourceRow_formula {declaration file row} (success : sourceRow declaration file = .ok row)
    {role' file' name body} (other : RowReads role' file' row name body) :
    name = declaration.name ∧ body.formula = declaration.body.formula := by
  obtain ⟨sameName, sameBody, _, _⟩ := sourceRowAs_unique success other
  exact ⟨sameName, by rw [sameBody]⟩

theorem label_reads {name : Name} {value : String} (success : label name = .ok value) :
    ∃ token, FullFof.tokenize value = .ok [token] ∧ RecordName token name := by
  obtain ⟨_, tokens, lexed, same⟩ := checked_tokens success
  simp only [kinds, List.map_cons, List.map_nil] at same
  obtain ⟨token, tail, rfl, kind, rest⟩ := kinds_cons same
  obtain rfl := kinds_nil rest
  exact ⟨token, lexed, namePiece_record kind⟩

/-- Each returned label lexes to one token naming its declaration, and each
    returned row reads as that declaration, in declaration order. -/
inductive RowsRead (role file : String) : List Declaration → List (String × String) → Prop where
  | nil : RowsRead role file [] []
  | cons {declaration rest entry rows}
      (labelRead : ∃ token, FullFof.tokenize entry.1 = .ok [token] ∧ RecordName token declaration.name)
      (rowRead : RowReads role file entry.2 declaration.name declaration.body)
      (tail : RowsRead role file rest rows) :
      RowsRead role file (declaration :: rest) (entry :: rows)

theorem sourceRowsAs_spec {role file : String} :
    ∀ {declarations : List Declaration} {rows : List (String × String)},
    sourceRowsAs role file declarations = .ok rows → RowsRead role file declarations rows
  | [], rows, success => by
    simp only [sourceRowsAs] at success
    cases success
    exact .nil
  | declaration :: rest, rows, success => by
    simp only [sourceRowsAs, bind, Except.bind] at success
    split at success
    · cases success
    · rename_i labelText labelRun
      split at success
      · cases success
      · rename_i row rowRun
        split at success
        · cases success
        · rename_i tail tailRun
          cases success
          exact .cons (label_reads labelRun) (sourceRowAs_reads rowRun) (sourceRowsAs_spec tailRun)

theorem sourceRows_spec {declarations : List Declaration} {file : String} {rows : List (String × String)}
    (success : sourceRows declarations file = .ok rows) : RowsRead "axiom" file declarations rows :=
  sourceRowsAs_spec success

#print axioms Fang.TptpCandidate.FullFof.SourceRow.term_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.arguments_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.unit_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.formula_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.literal_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.disjunction_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.body_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.row_grammar
#print axioms Fang.TptpCandidate.FullFof.SourceRow.RowTokens.unique
#print axioms Fang.TptpCandidate.FullFof.SourceRow.RowReads.unique
#print axioms Fang.TptpCandidate.FullFof.SourceRow.checked_tokens
#print axioms Fang.TptpCandidate.FullFof.SourceRow.sourceRowAs_reads
#print axioms Fang.TptpCandidate.FullFof.SourceRow.sourceRowAs_unique
#print axioms Fang.TptpCandidate.FullFof.SourceRow.sourceRow_reads
#print axioms Fang.TptpCandidate.FullFof.SourceRow.sourceRow_formula
#print axioms Fang.TptpCandidate.FullFof.SourceRow.label_reads
#print axioms Fang.TptpCandidate.FullFof.SourceRow.sourceRowsAs_spec
#print axioms Fang.TptpCandidate.FullFof.SourceRow.sourceRows_spec

end Fang.TptpCandidate.FullFof.SourceRow
