/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The finite model document of an accepted model, as `fang-model-tstp` prints it. Each export first runs the entry of
   `ModelEntries.lean` for its path, so nothing is printed for a model the checker does not accept, then builds the rows
   of `ModelDocument.lean` for the model read from the certificate and prints them in TPTP syntax with the roles of the
   finite interpretation format. Before the text is returned, the same rows with the role `axiom` are framed again by
   the bundle framer, must read back as exactly the built formulas, and are evaluated in the named model by the
   checker's step-counted evaluator. `Describes` states what a returned text is, and each `export*_describes` theorem
   adds the meaning of the path and the statements the accepted model satisfies. A failed export changes nothing about
   the status. -/
import ModelDocument
import ModelEntries
import BundleSourceRow

namespace Fang.TptpCandidate.FullFof.Model

open Fang.QuantifiedEqualityTstp.Expanded.Bundle (formulaEq formulaEq_sound objectText)

/-! TPTP text. -/

def printable (text : String) : Bool := text.all fun character => 32 ≤ character.toNat && character.toNat ≤ 126

def lowerWord (label : String) : Bool :=
  match label.toList with
  | first :: rest => ('a' ≤ first && first ≤ 'z') &&
      rest.all fun character => ('a' ≤ character && character ≤ 'z') || ('A' ≤ character && character ≤ 'Z') ||
        ('0' ≤ character && character ≤ '9') || character == '_'
  | [] => false

def quotedText (label : String) : Except String String :=
  if label.isEmpty || !printable label then .error "export-error: a name does not print"
  else .ok ("'" ++ String.join (label.toList.map fun character =>
    if character == '\'' || character == '\\' then "\\" ++ character.toString else character.toString) ++ "'")

/-- A distinct object between double quotes, a lower word as it is, any other name between single quotes. -/
def symbolText (label : String) : Except String String :=
  if isObjectName label then
    if label.length > 1 && printable (String.ofList (label.toList.drop 1)) then .ok (objectText label)
    else .error "export-error: a distinct object does not print"
  else if lowerWord label then .ok label
  else quotedText label

mutual
def termText : Source.Term → Except String String
  | .var label => .ok label
  | .app label arguments =>
    match symbolText label with
    | .error problem => .error problem
    | .ok head =>
      match arguments with
      | [] => .ok head
      | _ :: _ =>
        match termsText arguments with
        | .error problem => .error problem
        | .ok inner => .ok (head ++ "(" ++ inner ++ ")")
def termsText : List Source.Term → Except String String
  | [] => .ok ""
  | [term] => termText term
  | term :: rest =>
    match termText term, termsText rest with
    | .ok first, .ok more => .ok (first ++ "," ++ more)
    | .error problem, _ => .error problem
    | _, .error problem => .error problem
end

def operatorText : Binary → String
  | .conj => "&"
  | .disj => "|"
  | .implies => "=>"
  | .reverse => "<="
  | .iff => "<=>"
  | .xor => "<~>"
  | .nand => "~&"
  | .nor => "~|"

def quantifiedText (binders : List String) (body : String) : String :=
  if binders.isEmpty then body else "! [" ++ ",".intercalate binders ++ "] : " ++ body

/-- Universal binders in a row print as one list. The left operand of an associative connective prints without
    parentheses, as the decoders read a chain. Chains outside a quantifier break the line before each connective. -/
def formulaText (lines : Bool) (within : Option Binary) (binders : List String) : Formula → Except String String
  | .all label body => formulaText false none (binders ++ [label]) body
  | .atom label arguments => (termText (.app label arguments)).map (quantifiedText binders)
  | .equal left right =>
    match termText left, termText right with
    | .ok first, .ok second => .ok (quantifiedText binders (first ++ " = " ++ second))
    | .error problem, _ => .error problem
    | _, .error problem => .error problem
  | .truth => .ok (quantifiedText binders "$true")
  | .falsity => .ok (quantifiedText binders "$false")
  | .neg body => (formulaText lines none [] body).map fun inner => quantifiedText binders ("~ " ++ inner)
  | .ex label body =>
    (formulaText false none [] body).map fun inner => quantifiedText binders ("? [" ++ label ++ "] : " ++ inner)
  | .pair operator left right =>
    match formulaText lines (if operator.associative then some operator else none) [] left,
        formulaText lines none [] right with
    | .ok first, .ok second =>
      let joined := first ++ (if lines then "\n    " else " ") ++ operatorText operator ++ " " ++ second
      .ok (if binders.isEmpty && within == some operator then joined
        else quantifiedText binders ("( " ++ joined ++ " )"))
    | .error problem, _ => .error problem
    | _, .error problem => .error problem

/-- One statement; with `axioms` its role is `axiom`, which the bundle framer reads. -/
def rowText (axioms : Bool) (row : Row) : Except String String :=
  (formulaText true none [] row.formula).map fun body =>
    "fof(" ++ row.label ++ "," ++ (if axioms then "axiom" else row.role) ++ ",\n    " ++ body ++ " ).\n"

def documentText (axioms : Bool) (comment : Option String) (rows : List Row) : Except String String :=
  (rows.mapM (rowText axioms)).map fun texts =>
    (match comment with
      | some line => line ++ "\n"
      | none => "") ++ String.join texts

/-- One byte per character; `exportDocument` prints only ASCII. -/
def textBytes (text : String) : List UInt8 := text.toList.map fun character => character.toNat.toUInt8

/-! Reading the document back. -/

/-- The bodies of framed statements, when each is a formula record with its row's label and formula. -/
def framedFormulas : List Coverage.Statement → List Row → Option (List Formula)
  | [], [] => some []
  | .formula value :: rest, row :: rows =>
    match value.body with
    | .fof formula =>
      if value.name == .atom row.label && formulaEq formula row.formula then
        (framedFormulas rest rows).map (formula :: ·)
      else none
    | .cnf _ => none
  | _, _ => none

theorem framedFormulas_rows : ∀ {statements : List Coverage.Statement} {rows : List Row} {formulas : List Formula},
    framedFormulas statements rows = some formulas → formulas = rows.map Row.formula
  | [], [], _, read => by
    simp only [framedFormulas, Option.some.injEq] at read
    subst read
    rfl
  | [], _ :: _, _, read => by simp [framedFormulas] at read
  | .directive _ _ :: _, _, _, read => by simp [framedFormulas] at read
  | .formula _ :: _, [], _, read => by simp [framedFormulas] at read
  | .formula value :: rest, row :: rows, formulas, read => by
    simp only [framedFormulas] at read
    split at read
    · rename_i formula _
      split at read
      · rename_i matching
        simp only [Bool.and_eq_true] at matching
        cases later : framedFormulas rest rows with
        | none => simp [later] at read
        | some others =>
          simp only [later, Option.map_some, Option.some.injEq] at read
          subst read
          rw [formulaEq_sound matching.2, framedFormulas_rows later]
          rfl
      · cases read
    · cases read

/-- The longest document printed and read back. -/
def maximumDocumentBytes : Nat := 16777216

/-! The document of a model. -/

/-- What a printed document is. `text` prints `rows` with their finite-interpretation roles; the rows are built as
    `DocumentFacts` states, so each holds in the named model, whose names are pairwise different, denote every
    element and leave each input statement its truth value. The same rows with the role `axiom` frame as exactly their
    formulas, and the step-counted evaluator found each framed formula true in the named model. -/
def Describes (layout : Layout) (model : FiniteModel) (statements : List Formula) (comment : Option String)
    (text : String) : Prop :=
  ∃ names rows, DocumentFacts layout model statements names rows ∧ documentText false comment rows = .ok text ∧
    ∃ checked framed formulas, documentText true comment rows = .ok checked ∧
      Coverage.FramerLimit.frameFile Fang.NativeLimits.declarationLimit (textBytes checked) maximumDocumentBytes =
        .ok framed ∧
      framedFormulas framed rows = some formulas ∧ formulas = rows.map Row.formula ∧
      ∀ formula ∈ formulas, ∀ valuation, formula.Holds (model.named names).interpretation valuation

def exportDocument (limits : Limits) (layout : Layout) (model : FiniteModel) (statements : List Formula)
    (objects : List String) (comment : Option String) : Except String String :=
  match buildDocument layout model statements objects with
  | .error problem => .error problem
  | .ok (names, rows) =>
    match documentText false comment rows, documentText true comment rows with
    | .ok printed, .ok checked =>
      if decide (printed.length ≤ maximumDocumentBytes) &&
          printed.all (fun (character : Char) => decide (character.toNat < 128)) then
        match Coverage.FramerLimit.frameFileHashed Fang.NativeLimits.declarationLimit (textBytes checked)
            maximumDocumentBytes with
        | .error _ => .error "export-error: the document does not frame"
        | .ok framed =>
          match framedFormulas framed rows with
          | none => .error "export-error: the document frames as other statements"
          | some formulas =>
            match checkSteps (model.named names) 0 formulas limits.maximumWork with
            | .ok _ => .ok printed
            | .error .work => .error "resource.export.evaluation"
            | .error (.rejected _) => .error "export-error: a statement of the document is false in the model"
      else .error "resource.export.bytes"
    | .error problem, _ => .error problem
    | _, .error problem => .error problem

theorem exportDocument_describes {limits : Limits} {layout : Layout} {model : FiniteModel}
    {statements : List Formula} {objects : List String} {comment : Option String} {text : String}
    (exported : exportDocument limits layout model statements objects comment = .ok text) :
    Describes layout model statements comment text := by
  unfold exportDocument at exported
  split at exported
  · cases exported
  · rename_i names rows built
    split at exported
    · rename_i printed checked printedText checkedText
      split at exported
      · split at exported
        · cases exported
        · rename_i framed framedRun
          split at exported
          · cases exported
          · rename_i formulas readBack
            split at exported
            · rename_i left evaluated
              cases exported
              rw [Coverage.FramerLimit.frameFileHashed_eq] at framedRun
              exact ⟨names, rows, buildDocument_facts built, printedText, checked, framed, formulas, checkedText,
                framedRun, readBack, framedFormulas_rows readBack,
                checkSteps_sound (model.named names) formulas 0 limits.maximumWork left evaluated⟩
            · cases exported
            · cases exported
      · cases exported
    · cases exported
    · cases exported

/-! The document after each entry. -/

inductive ExportFailure where
  /-- The checker did not accept the model. -/
  | check : ModelError → ExportFailure
  /-- The model is accepted but no document is printed. -/
  | document : String → ExportFailure

def nameText : Name → Except String String
  | .atom value => if lowerWord value then .ok value else quotedText value
  | .integer value =>
    if !value.isEmpty && value.all Char.isDigit then .ok value
    else .error "export-error: a conjecture name does not print"

/-- The comment line of a countermodel document. -/
def goalComment (label : Name) : Except String String :=
  (nameText label).map fun text => "% The conjecture " ++ text ++ " is false in this model."

def exportSingle (limits : Limits) (layout : Layout) (declarationLimit : Nat) (bytes : List UInt8)
    (maximumBytes : Nat) (certificate : String) : Except ExportFailure String :=
  match acceptsSingle limits declarationLimit bytes maximumBytes certificate with
  | .error problem => .error (.check problem)
  | .ok () =>
    match Integration.decodeBytesLimited declarationLimit bytes maximumBytes with
    | .error _ => .error (.document "export-error: input")
    | .ok values =>
      match readModel limits certificate (source values) with
      | .error _ => .error (.document "export-error: certificate")
      | .ok model => (exportDocument limits layout model (source values) [] none).mapError .document

def exportBundle (limits : Limits) (layout : Layout) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (certificate : String) : Except ExportFailure String :=
  match acceptsBundle limits Coverage.BundleLimit.limited files maximumBytes certificate with
  | .error problem => .error (.check problem)
  | .ok () =>
    match Coverage.BundleLimit.limited files maximumBytes with
    | .error _ => .error (.document "export-error: input")
    | .ok bundle =>
      match Coverage.expand bundle Coverage.BundleV8.bundleFuel with
      | .error _ => .error (.document "export-error: input")
      | .ok items =>
        match readModel limits certificate (source (Coverage.declarationsOf bundle items)) with
        | .error _ => .error (.document "export-error: certificate")
        | .ok model => (exportDocument limits layout model (source (Coverage.declarationsOf bundle items))
            (Coverage.FramerV2.objectNames (Coverage.declarationsOf bundle items)) none).mapError .document

def exportInputs (limits : Limits) (layout : Layout) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (certificate : String) : Except ExportFailure String :=
  match acceptsInputs limits Roles.Bundle.V3.limited files maximumBytes certificate with
  | .error problem => .error (.check problem)
  | .ok () =>
    match readRoles Roles.Bundle.V3.limited files maximumBytes with
    | .error _ => .error (.document "export-error: input")
    | .ok read =>
      match readModel limits certificate (roleStatements read.1 read.2) with
      | .error _ => .error (.document "export-error: certificate")
      | .ok model => (exportDocument limits layout model (roleStatements read.1 read.2)
          (Roles.Bundle.V2.objectsOf read.1 read.2) none).mapError .document

def exportGoal (limits : Limits) (layout : Layout) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (certificate : String) : Except ExportFailure String :=
  match acceptsGoal limits Roles.Bundle.V3.limited files maximumBytes index certificate with
  | .error problem => .error (.check problem)
  | .ok _ =>
    match readRoles Roles.Bundle.V3.limited files maximumBytes with
    | .error _ => .error (.document "export-error: input")
    | .ok read =>
      match (Roles.Bundle.goalItems read.1 read.2)[index]? with
      | none => .error (.document "export-error: input")
      | some pair =>
        match goalComment pair.2.original.name with
        | .error problem => .error (.document problem)
        | .ok comment =>
          match readModel limits certificate (roleStatements read.1 read.2) with
          | .error _ => .error (.document "export-error: certificate")
          | .ok model => (exportDocument limits layout model (roleStatements read.1 read.2)
              (Roles.Bundle.V2.objectsOf read.1 read.2) (some comment)).mapError .document

/-! What an accepted model's checks proved, recovered for the model the export reads. -/

theorem mapError_ok_of {ε ε' α : Type} {action : Except ε α} {wrap : ε → ε'} {value : α}
    (success : action = .ok value) : action.mapError wrap = .ok value := by
  subst success
  rfl

theorem acceptsSingle_holds {limits : Limits} {declarationLimit : Nat} {bytes : List UInt8} {maximumBytes : Nat}
    {certificate : String} {values : List Declaration} {model : FiniteModel}
    (accepted : acceptsSingle limits declarationLimit bytes maximumBytes certificate = .ok ())
    (decoded : Integration.decodeBytesLimited declarationLimit bytes maximumBytes = .ok values)
    (read : readModel limits certificate (source values) = .ok model) :
    ∀ formula ∈ source values, ∀ valuation, formula.Holds model.interpretation valuation := by
  unfold acceptsSingle at accepted
  obtain ⟨found, decodedRun, rest⟩ := bind_ok accepted
  rw [mapError_ok_of decoded] at decodedRun
  cases decodedRun
  obtain ⟨found, readRun, rest⟩ := bind_ok rest
  rw [read] at readRun
  cases readRun
  obtain ⟨_, checked, _⟩ := bind_ok rest
  exact checkAll_sound checked

theorem acceptsBundle_holds {limits : Limits} {frame : Coverage.FramerLimit.Frame}
    {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {certificate : String}
    {bundle : Coverage.Bundle} {items : List Coverage.Item} {model : FiniteModel}
    (accepted : acceptsBundle limits frame files maximumBytes certificate = .ok ())
    (framed : frame files maximumBytes = .ok bundle)
    (expanded : Coverage.expand bundle Coverage.BundleV8.bundleFuel = .ok items)
    (read : readModel limits certificate (source (Coverage.declarationsOf bundle items)) = .ok model) :
    ∀ formula ∈ source (Coverage.declarationsOf bundle items), ∀ valuation,
      formula.Holds model.interpretation valuation := by
  unfold acceptsBundle at accepted
  simp only [framed, expanded] at accepted
  split at accepted
  · obtain ⟨found, readRun, rest⟩ := bind_ok accepted
    rw [read] at readRun
    cases readRun
    obtain ⟨_, checked, _⟩ := bind_ok rest
    exact checkAll_sound checked
  · cases accepted

theorem acceptsInputs_holds {limits : Limits} {frame : Roles.Bundle.V3.Frame}
    {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {certificate : String}
    {read : Roles.Bundle.RoleBundle × List Coverage.Item} {model : FiniteModel}
    (accepted : acceptsInputs limits frame files maximumBytes certificate = .ok ())
    (readRun : readRoles frame files maximumBytes = .ok read)
    (modelRun : readModel limits certificate (roleStatements read.1 read.2) = .ok model) :
    ∀ formula ∈ (Roles.positiveInputs (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
      Roles.Declaration.original, ∀ valuation, formula.Holds model.interpretation valuation := by
  unfold acceptsInputs at accepted
  obtain ⟨found, readRun', rest⟩ := bind_ok accepted
  rw [readRun] at readRun'
  cases readRun'
  split at rest
  · obtain ⟨found, modelRun', rest⟩ := bind_ok rest
    rw [modelRun] at modelRun'
    cases modelRun'
    obtain ⟨_, checked, _⟩ := bind_ok rest
    exact checkAll_sound checked
  · cases rest

theorem acceptsGoal_holds {limits : Limits} {frame : Roles.Bundle.V3.Frame}
    {files : List (Coverage.Key × List UInt8)} {maximumBytes index : Nat} {certificate : String}
    {item : Coverage.Item} {read : Roles.Bundle.RoleBundle × List Coverage.Item}
    {pair : Coverage.Item × Roles.Bytes.Entry} {model : FiniteModel}
    (accepted : acceptsGoal limits frame files maximumBytes index certificate = .ok item)
    (readRun : readRoles frame files maximumBytes = .ok read)
    (selected : (Roles.Bundle.goalItems read.1 read.2)[index]? = some pair)
    (modelRun : readModel limits certificate (roleStatements read.1 read.2) = .ok model) :
    (∀ formula ∈ (Roles.premises (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
      Roles.Declaration.original, ∀ valuation, formula.Holds model.interpretation valuation) ∧
    ¬ ∀ valuation, pair.2.original.body.formula.Holds model.interpretation valuation := by
  unfold acceptsGoal at accepted
  obtain ⟨found, readRun', rest⟩ := bind_ok accepted
  rw [readRun] at readRun'
  cases readRun'
  rw [selected] at rest
  simp only at rest
  obtain ⟨found, modelRun', rest⟩ := bind_ok rest
  rw [modelRun] at modelRun'
  cases modelRun'
  obtain ⟨left, checked, rest⟩ := bind_ok rest
  split at rest
  · rename_i decided
    refine ⟨checkAll_sound checked, fun holds => ?_⟩
    exact absurd ((sentenceSteps_iff decided).mpr holds) (by decide)
  · cases rest
  · cases rest
  · cases rest

/-! What each printed document is. -/

theorem exportSingle_describes {limits : Limits} {layout : Layout} {declarationLimit : Nat} {bytes : List UInt8}
    {maximumBytes : Nat} {certificate : String} {text : String}
    (exported : exportSingle limits layout declarationLimit bytes maximumBytes certificate = .ok text) :
    CnfBoolean.BytesSatisfiable bytes maximumBytes ∧
      ∃ values model, Integration.decodeBytesLimited declarationLimit bytes maximumBytes = .ok values ∧
        readModel limits certificate (source values) = .ok model ∧
        (∀ formula ∈ source values, ∀ valuation, formula.Holds model.interpretation valuation) ∧
        Describes layout model (source values) none text := by
  unfold exportSingle at exported
  split at exported
  · cases exported
  · rename_i accepted
    split at exported
    · cases exported
    · rename_i values decoded
      split at exported
      · cases exported
      · rename_i model read
        exact ⟨acceptsSingle_satisfiable accepted, values, model, decoded, read,
          acceptsSingle_holds accepted decoded read, exportDocument_describes (mapError_ok exported)⟩

theorem exportBundle_describes {limits : Limits} {layout : Layout} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes : Nat} {certificate : String} {text : String}
    (exported : exportBundle limits layout files maximumBytes certificate = .ok text) :
    Coverage.FramerLimit.ByteBundleSatisfiable Coverage.BundleLimit.limitedSpecification files maximumBytes
        Coverage.BundleV8.bundleFuel ∧
      ∃ bundle items model, Coverage.BundleLimit.limitedSpecification files maximumBytes = .ok bundle ∧
        Coverage.expand bundle Coverage.BundleV8.bundleFuel = .ok items ∧
        readModel limits certificate (source (Coverage.declarationsOf bundle items)) = .ok model ∧
        (∀ formula ∈ source (Coverage.declarationsOf bundle items), ∀ valuation,
          formula.Holds model.interpretation valuation) ∧
        Describes layout model (source (Coverage.declarationsOf bundle items)) none text := by
  unfold exportBundle at exported
  split at exported
  · cases exported
  · rename_i accepted
    split at exported
    · cases exported
    · rename_i bundle framed
      split at exported
      · cases exported
      · rename_i items expanded
        split at exported
        · cases exported
        · rename_i model read
          have specification := framed
          rw [Coverage.BundleLimit.limited_eq] at specification
          exact ⟨acceptsBundleLimited_satisfiable accepted, bundle, items, model, specification, expanded, read,
            acceptsBundle_holds accepted framed expanded read, exportDocument_describes (mapError_ok exported)⟩

theorem exportInputs_describes {limits : Limits} {layout : Layout} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes : Nat} {certificate : String} {text : String}
    (exported : exportInputs limits layout files maximumBytes certificate = .ok text) :
    Roles.Bundle.V3.ByteInputsSatisfiable Roles.Bundle.V3.limitedSpecification files maximumBytes
        Roles.Bundle.bundleFuel ∧
      ∃ read model, readRoles Roles.Bundle.V3.limitedSpecification files maximumBytes = .ok read ∧
        readModel limits certificate (roleStatements read.1 read.2) = .ok model ∧
        (∀ formula ∈ (Roles.positiveInputs (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
          Roles.Declaration.original, ∀ valuation, formula.Holds model.interpretation valuation) ∧
        Describes layout model (roleStatements read.1 read.2) none text := by
  unfold exportInputs at exported
  split at exported
  · cases exported
  · rename_i accepted
    split at exported
    · cases exported
    · rename_i read readRun
      split at exported
      · cases exported
      · rename_i model modelRun
        have specification := readRun
        rw [Roles.Bundle.V3.limited_eq] at specification
        exact ⟨acceptsInputsLimited_satisfiable accepted, read, model, specification, modelRun,
          acceptsInputs_holds accepted readRun modelRun, exportDocument_describes (mapError_ok exported)⟩

theorem exportGoal_describes {limits : Limits} {layout : Layout} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes index : Nat} {certificate : String} {text : String}
    (exported : exportGoal limits layout files maximumBytes index certificate = .ok text) :
    Roles.Bundle.V3.ByteCounterSatisfiable Roles.Bundle.V3.limitedSpecification files maximumBytes
        Roles.Bundle.bundleFuel ∧
      ∃ read pair model comment, readRoles Roles.Bundle.V3.limitedSpecification files maximumBytes = .ok read ∧
        (Roles.Bundle.goalItems read.1 read.2)[index]? = some pair ∧
        goalComment pair.2.original.name = .ok comment ∧
        readModel limits certificate (roleStatements read.1 read.2) = .ok model ∧
        (∀ formula ∈ (Roles.premises (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
          Roles.Declaration.original, ∀ valuation, formula.Holds model.interpretation valuation) ∧
        (¬ ∀ valuation, pair.2.original.body.formula.Holds model.interpretation valuation) ∧
        Describes layout model (roleStatements read.1 read.2) (some comment) text := by
  unfold exportGoal at exported
  split at exported
  · cases exported
  · rename_i item accepted
    split at exported
    · cases exported
    · rename_i read readRun
      split at exported
      · cases exported
      · rename_i pair selected
        split at exported
        · cases exported
        · rename_i comment commented
          split at exported
          · cases exported
          · rename_i model modelRun
            have specification := readRun
            rw [Roles.Bundle.V3.limited_eq] at specification
            obtain ⟨premises, refuted⟩ := acceptsGoal_holds accepted readRun selected modelRun
            exact ⟨acceptsGoalLimited_counterSatisfiable accepted, read, pair, model, comment, specification,
              selected, commented, modelRun, premises, refuted, exportDocument_describes (mapError_ok exported)⟩

end Fang.TptpCandidate.FullFof.Model
