/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The complete version-8 TSTP refutation document: original source rows, one
   SAP group row naming every source, then the annotated clause rows. Names
   come from the checked tables, so the group and the rows share one table. -/
import ExpandedDerivation
import ExpandedFastCertificate
import ExpandedLinearCertificate
import SourceRow

namespace Fang.QuantifiedEqualityTstp.Expanded
open Fang.TptpCandidate Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration TstpText

/-- Candidate value of a digit string. `parentText` keeps it only when it prints
    back to the same text, so the proofs never depend on this parser. -/
def digitsValue : List Char → Option Nat
  | [] => none
  | chars => if chars.all Char.isDigit then
      some (chars.foldl (fun value c => 10 * value + (c.toNat - '0'.toNat)) 0) else none

/-- A reference to a source declaration inside an annotation. Atoms are quoted
    (a quoted atom names the same declaration as its bare spelling); integer
    names print as their digits, which differ from a quoted atom of the same text.
    Signed integers and leading zeros are an export error. -/
def parentText : Name → Except String String
  | .atom value => TstpExport.quote value
  | .integer value =>
    match digitsValue value.toList with
    | some number =>
      if toString number = value then .ok value
      else .error "export-error: integer declaration name is not a plain natural number"
    | none => .error "export-error: integer declaration name is not a plain natural number"

def parentDatum : Name → Datum
  | .atom value => .atom value
  | .integer value => .natural ((digitsValue value.toList).getD 0)

theorem parentText_data {entry : Name} {text : String} (success : parentText entry = .ok text) :
    DataText text (parentDatum entry) := by
  cases entry with
  | atom value =>
    simp only [parentText] at success
    exact quoted_data success
  | integer value =>
    cases parsed : digitsValue value.toList with
    | none =>
      have failed : parentText (.integer value) =
          .error "export-error: integer declaration name is not a plain natural number" := by
        simp only [parentText, parsed]
      rw [failed] at success
      cases success
    | some number =>
      by_cases plain : toString number = value
      · have printed : parentText (.integer value) = .ok value := by
          simp only [parentText, parsed, plain, ↓reduceIte]
        rw [printed] at success
        have same := Except.ok.inj success
        subst same
        have spelled := DataText.natural (natural_spelling number)
        simp only [parentDatum, parsed, Option.getD_some]
        rw [plain] at spelled
        exact spelled
      · have failed : parentText (.integer value) =
            .error "export-error: integer declaration name is not a plain natural number" := by
          simp only [parentText, parsed, plain, ↓reduceIte]
        rw [failed] at success
        cases success

theorem parents_data {names : List Name} :
    ∀ {texts : List String}, names.mapM parentText = .ok texts →
      DataTexts texts (names.map parentDatum) := by
  induction names with
  | nil =>
    intro texts success
    simp [pure, Except.pure] at success
    subst texts
    exact .nil
  | cons first rest ih =>
    intro texts success
    cases headRun : parentText first with
    | error reason => simp [List.mapM_cons, headRun, bind, Except.bind] at success
    | ok head =>
      cases tailRun : rest.mapM parentText with
      | error reason => simp [List.mapM_cons, headRun, tailRun, bind, Except.bind] at success
      | ok tail =>
        simp [List.mapM_cons, headRun, tailRun, bind, Except.bind, pure, Except.pure] at success
        subst texts
        exact .cons (parentText_data headRun) (ih tailRun)

def sapDatum (parents : List Name) : Datum :=
  .function "inference" [.atom "fang_preprocessing", .list [.function "status" [.atom "sap"]],
    .list (parents.map parentDatum)]

theorem sap_annotation {parents : List Name} {texts : List String}
    (printed : parents.mapM parentText = .ok texts) :
    DataText (groupAnnotation texts) (sapDatum parents) := by
  unfold groupAnnotation sapDatum Rows.call Rows.bracket
  exact .function (checked_lower "inference" (by decide)) (by simp)
    (.cons (.atom (checked_lower "fang_preprocessing" (by decide)))
      (.cons (.list (.cons (.function (checked_lower "status" (by decide)) (by simp)
          (.cons (.atom (checked_lower "sap" (by decide))) .nil)) .nil))
        (.cons (.list (parents_data printed)) .nil)))

/-- Every name used in the document, compared as TPTP names (atom or integer). -/
def documentNames (sources : List Name) (groupLabel : String) (labels : List String) : List Name :=
  sources ++ .atom groupLabel :: labels.map Name.atom

def originals (output : Output) : List Declaration :=
  output.prepared.original.rows.map NumericRow.original

def sapRow (names : Body.Names) (problem : Fang.Equality.Problem) (groupLabel : String)
    (parents : List String) : Except String String := do
  let quoted ← TstpExport.quote groupLabel
  let body ← Group.groupText names problem
  pure (groupRowText quoted body (groupAnnotation parents))

def maximumDocumentBytes : Nat := 16 * 1024 * 1024

def capText (text : String) : Except String String :=
  if text.utf8ByteSize ≤ maximumDocumentBytes then .ok text
  else .error "resource-exhaustion: TSTP document exceeds 16 MiB"

theorem capText_ok {text result : String} (success : capText text = .ok result) :
    result = text ∧ text.utf8ByteSize ≤ maximumDocumentBytes := by
  unfold capText at success
  split at success
  · rename_i capped
    exact ⟨(Except.ok.inj success).symm, capped⟩
  · cases success

/-- Body of the document after a successful build. -/
def assemble (output : Output) (functions : List Frontend.Symbol) (file groupLabel : String)
    (labels : List String) : Except String String := do
  let names ← attach output functions
  let sources ← SourceRow.sourceRows (originals output) file
  let parents ← ((originals output).map Declaration.name).mapM parentText
  let group ← sapRow names output.prepared.problem groupLabel parents
  let rowTexts ← Rows.render names groupLabel labels (rows output)
  capText (String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts)

def documentOf (output : Output) (functions : List Frontend.Symbol) (file groupLabel : String)
    (labels : List String) : Except String String :=
  if decide (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup then
    assemble output functions file groupLabel labels
  else .error "export-error: document names are not distinct"

def document (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) (functions : List Frontend.Symbol)
    (file groupLabel : String) (labels : List String) : Except String String :=
  match build bytes maximumBytes proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these bytes"
  | .ok output => documentOf output functions file groupLabel labels

private theorem bind_ok {α β : Type} {action : Except String α}
    {next : α → Except String β} {result : β}
    (success : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem readInput_originals {values : List Declaration} {input : NumericInput}
    (success : readInput values = some input) : input.rows.map NumericRow.original = values :=
  (readInput_tables success).2.2

/-- The source rows restate exactly the declarations decoded from the original bytes. -/
theorem originals_decoded {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (built : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    CnfBoolean.decodeBytes bytes maximumBytes = .ok (originals output) := by
  obtain ⟨values, _, _, _, _, decoded, numericRun, _⟩ := prepare_witness (build_witness built).1
  rw [originals, readInput_originals numericRun]
  exact decoded

structure DocumentFacts (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (functions : List Frontend.Symbol) (file groupLabel : String) (labels : List String)
    (text : String) : Prop where
  facts : ∃ output names sources parents group rowTexts,
    build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
    accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok () ∧
    CnfBoolean.decodeBytes bytes maximumBytes = .ok (originals output) ∧
    attach output functions = .ok names ∧
    SourceRow.RowsRead "axiom" file (originals output) sources ∧
    ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
    sapRow names output.prepared.problem groupLabel parents = .ok group ∧
    Rows.render names groupLabel labels (rows output) = .ok rowTexts ∧
    (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup ∧
    text = String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts ∧
    text.utf8ByteSize ≤ maximumDocumentBytes

theorem document_spec {bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : document bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    DocumentFacts bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
      groupLabel labels text := by
  cases built : build bytes maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason => simp [document, built] at success
  | ok output =>
    by_cases distinct : (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup
    · simp only [document, documentOf, built, distinct, decide_true] at success
      unfold assemble at success
      obtain ⟨names, namesRun, success⟩ := bind_ok success
      obtain ⟨sources, sourcesRun, success⟩ := bind_ok success
      obtain ⟨parents, parentsRun, success⟩ := bind_ok success
      obtain ⟨group, groupRun, success⟩ := bind_ok success
      obtain ⟨rowTexts, rowsRun, success⟩ := bind_ok success
      obtain ⟨same, capped⟩ := capText_ok success
      subst same
      exact ⟨⟨output, names, sources, parents, group, rowTexts, built, build_accepts built,
        originals_decoded built, namesRun, SourceRow.sourceRows_spec sourcesRun, parentsRun, groupRun,
        rowsRun, distinct, rfl, capped⟩⟩
    · simp [document, documentOf, built, distinct] at success

/-- A printed document certifies the original bytes unsatisfiable. -/
theorem document_original_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals
    functions file groupLabel labels text}
    (success : document bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨⟨output, _, _, _, _, _, built, _⟩⟩ := document_spec success
  exact build_original_unsat built

/-- A group row printed by `sapRow`: its unique closed reading, which holds in a
    source model exactly when the problem holds in the table model, and the
    `status(sap)` annotation naming every declaration. SAP for a printed
    document is `document_group_sap`. -/
theorem document_group {names : Body.Names} {problem : Fang.Equality.Problem} {groupLabel : String}
    {declarations : List Declaration} {parents : List String} {group : String}
    (parentsRun : (declarations.map Declaration.name).mapM parentText = .ok parents)
    (groupRun : sapRow names problem groupLabel parents = .ok group) :
    ∃ quoted body formula,
      group = groupRowText quoted body (groupAnnotation parents) ∧
      QuotedAtom quoted.toList groupLabel.toList ∧
      Group.groupFormula names problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧ formula.Within [] ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Fang.Equality.models (tableModel names.view model) problem) ∧
      DataText (groupAnnotation parents) (sapDatum (declarations.map Declaration.name)) := by
  unfold sapRow at groupRun
  obtain ⟨quoted, quotedRun, groupRun⟩ := bind_ok groupRun
  obtain ⟨body, bodyRun, groupRun⟩ := bind_ok groupRun
  have same := Except.ok.inj groupRun
  subst same
  obtain ⟨formula, formulaRun, parsed, closed, unique, meaning⟩ := Group.groupText_spec bodyRun
  exact ⟨quoted, body, formula, rfl, quote_grammar quotedRun, formulaRun, parsed, closed, unique,
    meaning, sap_annotation parentsRun⟩

/-- SAP for the group row of a printed document: the row is printed from the
    attached names and the prepared problem of an accepted pair, it has one
    reading, and if the original bytes have a model then that reading holds in
    some source model. -/
theorem document_group_sap {bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : document bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ∃ output names parents group quoted body formula,
      build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      attach output functions = .ok names ∧
      ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
      sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      group = groupRowText quoted body (groupAnnotation parents) ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (CnfBoolean.BytesSatisfiable bytes maximumBytes →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨⟨output, names, _, parents, group, _, built, _, _, namesRun, _, parentsRun, groupRun, _⟩⟩ :=
    document_spec success
  obtain ⟨quoted, body, formula, printed, _, formulaRun, parsed, _, unique, _⟩ :=
    document_group parentsRun groupRun
  exact ⟨output, names, parents, group, quoted, body, formula, built, namesRun, parentsRun, groupRun,
    printed, parsed, unique, fun satisfiable => build_group_sap built namesRun formulaRun satisfiable⟩

/-- `build` with the linear lexer of the fast checker. -/
def buildFast (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except BuildError Output :=
  match prepareFast bytes maximumBytes limits maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok prepared =>
    match decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if WellFormed prepared certificate then
        match retain prepared.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem buildFast_eq (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    buildFast bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      build bytes maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold buildFast build
  rw [prepareFast_eq]
  -- The two definitions use distinct auxiliary match functions with equal bodies.
  rfl

/-- `build` with the linear lexer and the linear declaration decoder. -/
def buildLinear (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except BuildError Output :=
  match prepareLinear bytes maximumBytes limits maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok prepared =>
    match decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if WellFormed prepared certificate then
        match retain prepared.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem buildLinear_eq (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    buildLinear bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      build bytes maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold buildLinear build
  rw [prepareLinear_eq]
  -- The two definitions use distinct auxiliary match functions with equal bodies.
  rfl

/-- `head`, then `head_`, `head__` and so on, each followed by `tail`, until one is a
    prefix of no taken spelling. A spelling starts with at most one candidate, so
    `taken.length + 1` candidates suffice. The checks below do not rely on this. -/
def freshPrefix (taken : List String) (head tail : String) : String :=
  let candidates := (List.range (taken.length + 1)).map fun count => head ++ "".pushn '_' count ++ tail
  (candidates.find? fun candidate =>
    taken.all fun spelling => !candidate.toList.isPrefixOf spelling.toList).getD head

/-- The original function table, then fresh names for the symbols added by preprocessing. -/
def exportFunctions (output : Output) : List Frontend.Symbol :=
  let original := output.prepared.original
  let stem := freshPrefix (Naming.originalNames original.functions original.predicates) "sk" "f"
  Naming.symbols original.functions ++
    (output.prepared.functionArities.drop original.functions.length).mapIdx
      fun index arity => ⟨stem ++ toString index, some arity⟩

/-- The group label and one label per clause row, avoiding every source atom name. -/
def exportLabels (output : Output) : String × List String :=
  let taken := (originals output).filterMap fun declaration =>
    match declaration.name with
    | .atom value => some value
    | .integer _ => none
  let stem := freshPrefix taken "f" "n"
  (stem ++ "0", (List.range (rows output).length).map fun index => stem ++ toString (index + 1))

/-- The product entry: the linear lexer and decoder, generated names, then the same checks as `document`. -/
def exportDocument (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (file : String) : Except String String :=
  match buildLinear bytes maximumBytes proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these bytes"
  | .ok output => documentOf output (exportFunctions output) file (exportLabels output).1 (exportLabels output).2

theorem exportDocument_spec {bytes maximumBytes proof limits maximumPredicates maximumLiterals file text}
    (success : exportDocument bytes maximumBytes proof limits maximumPredicates maximumLiterals file = .ok text) :
    ∃ output, build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      DocumentFacts bytes maximumBytes proof limits maximumPredicates maximumLiterals (exportFunctions output) file
        (exportLabels output).1 (exportLabels output).2 text := by
  unfold exportDocument at success
  rw [buildLinear_eq] at success
  cases built : build bytes maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason =>
    rw [built] at success
    cases success
  | ok output =>
    rw [built] at success
    refine ⟨output, rfl, document_spec ?_⟩
    unfold document
    rw [built]
    exact success

theorem exportDocument_original_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals file text}
    (success : exportDocument bytes maximumBytes proof limits maximumPredicates maximumLiterals file = .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨output, built, _⟩ := exportDocument_spec success
  exact build_original_unsat built

/-- A product document is the `document` of the generated names. -/
theorem exportDocument_document {bytes maximumBytes proof limits maximumPredicates maximumLiterals file text}
    (success : exportDocument bytes maximumBytes proof limits maximumPredicates maximumLiterals file = .ok text) :
    ∃ output, build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      document bytes maximumBytes proof limits maximumPredicates maximumLiterals (exportFunctions output) file
        (exportLabels output).1 (exportLabels output).2 = .ok text := by
  unfold exportDocument at success
  rw [buildLinear_eq] at success
  cases built : build bytes maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason =>
    rw [built] at success
    cases success
  | ok output =>
    rw [built] at success
    refine ⟨output, rfl, ?_⟩
    unfold document
    rw [built]
    exact success

/-- SAP for the group row of a product document. -/
theorem exportDocument_group_sap {bytes maximumBytes proof limits maximumPredicates maximumLiterals file text}
    (success : exportDocument bytes maximumBytes proof limits maximumPredicates maximumLiterals file = .ok text) :
    ∃ output names parents group quoted body formula,
      build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      attach output (exportFunctions output) = .ok names ∧
      ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
      sapRow names output.prepared.problem (exportLabels output).1 parents = .ok group ∧
      group = groupRowText quoted body (groupAnnotation parents) ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (CnfBoolean.BytesSatisfiable bytes maximumBytes →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨output, built, printed⟩ := exportDocument_document success
  obtain ⟨output', names, parents, group, quoted, body, formula, built', rest⟩ := document_group_sap printed
  rw [built] at built'
  cases built'
  exact ⟨output, names, parents, group, quoted, body, formula, built, rest⟩

/-- Bodies read from printed source rows, one per row, under any role and file. -/
inductive RowBodies : List (String × String) → List Body → Prop where
  | nil : RowBodies [] []
  | cons {entry rows body bodies}
      (read : ∃ role file rowName, SourceRow.RowReads role file entry.2 rowName body)
      (tail : RowBodies rows bodies) :
      RowBodies (entry :: rows) (body :: bodies)

theorem rowBodies_original {role file : String} :
    ∀ {declarations : List Declaration} {rows : List (String × String)} {bodies : List Body},
      SourceRow.RowsRead role file declarations rows → RowBodies rows bodies →
        bodies = declarations.map Declaration.body := by
  intro declarations rows bodies rowsRead read
  induction rowsRead generalizing bodies with
  | nil =>
    cases read
    rfl
  | cons _ rowRead _ ih =>
    cases read with
    | cons other rest =>
      obtain ⟨_, _, _, other⟩ := other
      obtain ⟨_, sameBody, _, _⟩ := rowRead.unique other
      rw [List.map_cons, ← sameBody, ih rest]

/-- SAP against the printed source rows: whatever bodies those rows are read
    as, a model of them gives a model of the group row's reading. -/
theorem document_rows_sap {bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : document bytes maximumBytes proof limits maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ∃ output names sources parents group rowTexts formula,
      build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      attach output functions = .ok names ∧
      SourceRow.RowsRead "axiom" file (originals output) sources ∧
      ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
      sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      text = String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts ∧
      Group.groupFormula names output.prepared.problem = .ok formula ∧
      ∀ bodies, RowBodies sources bodies → Fang.TptpCandidate.FullFof.Satisfiable (bodies.map Body.formula) →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation := by
  obtain ⟨⟨output, names, sources, parents, group, rowTexts, built, _, decoded, namesRun, rowsRead, parentsRun,
    groupRun, _, _, printed, _⟩⟩ := document_spec success
  obtain ⟨_, _, formula, _, _, formulaRun, _⟩ := document_group parentsRun groupRun
  refine ⟨output, names, sources, parents, group, rowTexts, formula, built, namesRun, rowsRead, parentsRun,
    groupRun, printed, formulaRun, ?_⟩
  intro bodies read satisfiable
  rw [rowBodies_original rowsRead read, List.map_map] at satisfiable
  exact build_group_sap built namesRun formulaRun
    ((CnfBoolean.decode_bytes_satisfiable decoded).mpr satisfiable)

#print axioms Fang.QuantifiedEqualityTstp.Expanded.parentText_data
#print axioms Fang.QuantifiedEqualityTstp.Expanded.capText_ok
#print axioms Fang.QuantifiedEqualityTstp.Expanded.parents_data
#print axioms Fang.QuantifiedEqualityTstp.Expanded.sap_annotation
#print axioms Fang.QuantifiedEqualityTstp.Expanded.readInput_originals
#print axioms Fang.QuantifiedEqualityTstp.Expanded.originals_decoded
#print axioms Fang.QuantifiedEqualityTstp.Expanded.document_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.document_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.Expanded.document_group
#print axioms Fang.QuantifiedEqualityTstp.Expanded.document_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.buildFast_eq
#print axioms Fang.QuantifiedEqualityTstp.Expanded.buildLinear_eq
#print axioms Fang.QuantifiedEqualityTstp.Expanded.exportDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.exportDocument_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.Expanded.exportDocument_document
#print axioms Fang.QuantifiedEqualityTstp.Expanded.exportDocument_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.rowBodies_original
#print axioms Fang.QuantifiedEqualityTstp.Expanded.document_rows_sap

end Fang.QuantifiedEqualityTstp.Expanded
