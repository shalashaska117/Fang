/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Annotated rows for the retained ordered equality steps.
   Input steps become group leaves; the group row itself is emitted elsewhere. -/
import EqualityNames
import Product.SourceMetadata

namespace Fang.QuantifiedEqualityTstp.Rows
open TstpText Equality

/-- `name(t1,...,tn)` in exactly the spelling of the datum grammar. -/
def call (rowName : String) (texts : List String) : String :=
  rowName ++ "(" ++ String.intercalate "," texts ++ ")"

def bracket (texts : List String) : String :=
  "[" ++ String.intercalate "," texts ++ "]"

def natText (value : Nat) : String := toString value

def rootText : Ordered.Root → String
  | .argument index => call "argument" [natText index]
  | .equalityLeft => "equality_left"
  | .equalityRight => "equality_right"

def rootDatum : Ordered.Root → Datum
  | .argument index => .function "argument" [.natural index]
  | .equalityLeft => .atom "equality_left"
  | .equalityRight => .atom "equality_right"

def directionText (reverse : Bool) : String := if reverse then "reverse" else "forward"

def positionText (witness : Ordered.Witness) : String :=
  call "fang_paramodulation_position" [natText witness.sourcePivot, natText witness.targetLiteral,
    rootText witness.root, bracket (witness.path.map natText), directionText witness.reverse]

def positionDatum (witness : Ordered.Witness) : Datum :=
  .function "fang_paramodulation_position" [.natural witness.sourcePivot, .natural witness.targetLiteral,
    rootDatum witness.root, .list (witness.path.map .natural), .atom (directionText witness.reverse)]

def substitutionDatum (bindings : List Datum) : Datum :=
  .function "fang_substitution" [.list bindings]

/-- Rule name and printed metadata of one non-input step. -/
def stepInfo (names : Body.Names) : Ordered.Step → Except String (String × List String)
  | .input _ => .error "export-error: an input step is a group leaf"
  | .factor _ first second substitution _ =>
    match TstpExport.witness names.view substitution with
    | .error reason => .error reason
    | .ok bindings => .ok ("fang_factoring",
        ["status(thm)", call "pivots" [natText first, natText second], bindings])
  | .equalityResolution _ before _ _ _ substitution _ =>
    match TstpExport.witness names.view substitution with
    | .error reason => .error reason
    | .ok bindings => .ok ("fang_equality_resolution",
        ["status(thm)", call "literal" [natText before.length], bindings])
  | .resolution _ leftPosition _ rightPosition substitution _ =>
    match TstpExport.witness names.view substitution with
    | .error reason => .error reason
    | .ok bindings => .ok ("fang_resolution",
        ["status(thm)", call "pivots" [natText leftPosition, natText rightPosition], bindings])
  | .paramodulation _ _ witness _ =>
    match TstpExport.witness names.view witness.substitution with
    | .error reason => .error reason
    | .ok bindings => .ok ("fang_paramodulation", ["status(thm)", positionText witness, bindings])

/-- The printed metadata of each rule. Bindings are the accepted witness data. -/
inductive StepInfo (names : Body.Names) : Ordered.Step → String → List Datum → Prop where
  | factor {parent first second substitution claimed bindings}
      (meaning : BindingsMeaning names.functions substitution bindings) :
      StepInfo names (.factor parent first second substitution claimed) "fang_factoring"
        [statusThm, pivotInfo first second, substitutionDatum bindings]
  | equalityResolution {parent before after left right substitution claimed bindings}
      (meaning : BindingsMeaning names.functions substitution bindings) :
      StepInfo names (.equalityResolution parent before after left right substitution claimed)
        "fang_equality_resolution"
        [statusThm, .function "literal" [.natural before.length], substitutionDatum bindings]
  | resolution {left leftPosition right rightPosition substitution claimed bindings}
      (meaning : BindingsMeaning names.functions substitution bindings) :
      StepInfo names (.resolution left leftPosition right rightPosition substitution claimed)
        "fang_resolution" [statusThm, pivotInfo leftPosition rightPosition, substitutionDatum bindings]
  | paramodulation {source target witness claimed bindings}
      (meaning : BindingsMeaning names.functions witness.substitution bindings) :
      StepInfo names (.paramodulation source target witness claimed) "fang_paramodulation"
        [statusThm, positionDatum witness, substitutionDatum bindings]

theorem natural_text (value : Nat) : DataText (natText value) (.natural value) :=
  .natural (natural_spelling value)

theorem naturals_text (values : List Nat) :
    DataTexts (values.map natText) (values.map Datum.natural) := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons (natural_text value) ih

theorem pivots_call (left right : Nat) :
    DataText (call "pivots" [natText left, natText right]) (pivotInfo left right) := by
  unfold call pivotInfo
  exact .function (checked_lower "pivots" (by decide)) (by simp)
    (.cons (natural_text left) (.cons (natural_text right) .nil))

theorem literal_call (index : Nat) :
    DataText (call "literal" [natText index]) (.function "literal" [.natural index]) := by
  unfold call
  exact .function (checked_lower "literal" (by decide)) (by simp) (.cons (natural_text index) .nil)

theorem root_text (root : Ordered.Root) : DataText (rootText root) (rootDatum root) := by
  cases root with
  | argument index =>
    unfold rootText rootDatum call
    exact .function (checked_lower "argument" (by decide)) (by simp) (.cons (natural_text index) .nil)
  | equalityLeft => exact .atom (checked_lower "equality_left" (by decide))
  | equalityRight => exact .atom (checked_lower "equality_right" (by decide))

theorem direction_text (reverse : Bool) :
    DataText (directionText reverse) (.atom (directionText reverse)) := by
  cases reverse
  · exact .atom (checked_lower "forward" (by decide))
  · exact .atom (checked_lower "reverse" (by decide))

theorem position_text (witness : Ordered.Witness) :
    DataText (positionText witness) (positionDatum witness) := by
  unfold positionText positionDatum call
  exact .function (checked_lower "fang_paramodulation_position" (by decide)) (by simp)
    (.cons (natural_text witness.sourcePivot) (.cons (natural_text witness.targetLiteral)
      (.cons (root_text witness.root) (.cons (.list (naturals_text witness.path))
        (.cons (direction_text witness.reverse) .nil)))))

theorem stepInfo_correspondence {names step rule texts}
    (accepted : stepInfo names step = .ok (rule, texts)) :
    Frontend.lowerName rule = true ∧ ∃ infos, StepInfo names step rule infos ∧ DataTexts texts infos := by
  cases step with
  | input index => simp [stepInfo] at accepted
  | factor parent first second substitution claimed =>
    cases witnessRun : TstpExport.witness names.view substitution with
    | error reason => simp [stepInfo, witnessRun] at accepted
    | ok bindings =>
      simp only [stepInfo, witnessRun, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨data, meaning, grammar⟩ := witness_correspondence substitution witnessRun
      exact ⟨by decide, _, .factor meaning,
        .cons status_text (.cons (pivots_call first second) (.cons grammar .nil))⟩
  | equalityResolution parent before after left right substitution claimed =>
    cases witnessRun : TstpExport.witness names.view substitution with
    | error reason => simp [stepInfo, witnessRun] at accepted
    | ok bindings =>
      simp only [stepInfo, witnessRun, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨data, meaning, grammar⟩ := witness_correspondence substitution witnessRun
      exact ⟨by decide, _, .equalityResolution meaning,
        .cons status_text (.cons (literal_call before.length) (.cons grammar .nil))⟩
  | resolution left leftPosition right rightPosition substitution claimed =>
    cases witnessRun : TstpExport.witness names.view substitution with
    | error reason => simp [stepInfo, witnessRun] at accepted
    | ok bindings =>
      simp only [stepInfo, witnessRun, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨data, meaning, grammar⟩ := witness_correspondence substitution witnessRun
      exact ⟨by decide, _, .resolution meaning,
        .cons status_text (.cons (pivots_call leftPosition rightPosition) (.cons grammar .nil))⟩
  | paramodulation source target witness claimed =>
    cases witnessRun : TstpExport.witness names.view witness.substitution with
    | error reason => simp [stepInfo, witnessRun] at accepted
    | ok bindings =>
      simp only [stepInfo, witnessRun, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨data, meaning, grammar⟩ := witness_correspondence witness.substitution witnessRun
      exact ⟨by decide, _, .paramodulation meaning,
        .cons status_text (.cons (position_text witness) (.cons grammar .nil))⟩

/-- Each parent index names an earlier retained row. -/
def parentLabel (labels : List String) (index : Nat) : Except String String :=
  match labels[index]? with
  | some value => TstpExport.quote value
  | none => .error "export-error: parent label is missing"

theorem parentLabels_correspondence {labels : List String} :
    ∀ {parents : List Nat} {texts : List String}, parents.mapM (parentLabel labels) = .ok texts →
      ∃ values : List String, parents.map (fun index => labels[index]?) = values.map some ∧
        DataTexts texts (values.map Datum.atom)
  | [], texts, success => by
    simp [pure, Except.pure] at success
    subst texts
    exact ⟨[], rfl, .nil⟩
  | parent :: rest, texts, success => by
    cases labelAt : labels[parent]? with
    | none => simp [List.mapM_cons, parentLabel, labelAt, bind, Except.bind] at success
    | some value =>
      cases quoted : TstpExport.quote value with
      | error reason => simp [List.mapM_cons, parentLabel, labelAt, quoted, bind, Except.bind] at success
      | ok head =>
        cases tailRun : rest.mapM (parentLabel labels) with
        | error reason =>
          simp [List.mapM_cons, parentLabel, labelAt, quoted, tailRun, bind, Except.bind] at success
        | ok tail =>
          simp [List.mapM_cons, parentLabel, labelAt, quoted, tailRun, bind, Except.bind,
            pure, Except.pure] at success
          subst texts
          obtain ⟨values, same, grammar⟩ := parentLabels_correspondence tailRun
          exact ⟨value :: values, by simp [labelAt, same], .cons (quoted_data quoted) grammar⟩

def rowText (quoted body annotation : String) : String :=
  "cnf(" ++ quoted ++ ",plain,(" ++ body ++ ")," ++ annotation ++ ").\n"

def leafAnnotation (index : Nat) (parent : String) : String :=
  call "inference" ["fang_group_clause",
    bracket ["status(thm)", call "clause_index" [natText index]], bracket [parent]]

def leafDatum (index : Nat) (group : String) : Datum :=
  .function "inference" [.atom "fang_group_clause",
    .list [statusThm, .function "clause_index" [.natural index]], .list [.atom group]]

def leafRow (names : Body.Names) (group rowName : String) (index : Nat)
    (clause : Equality.Clause) : Except String String := do
  let quoted ← TstpExport.quote rowName
  let body ← Body.clause names clause
  let parent ← TstpExport.quote group
  pure (rowText quoted body (leafAnnotation index parent))

def inferenceRow (names : Body.Names) (labels : List String) (rowName : String)
    (step : Ordered.Step) (clause : Equality.Clause) : Except String String := do
  let quoted ← TstpExport.quote rowName
  let body ← Body.clause names clause
  let info ← stepInfo names step
  let parents ← step.parents.mapM (parentLabel labels)
  pure (rowText quoted body (call "inference" [info.1, bracket info.2, bracket parents]))

def renderRow (names : Body.Names) (group : String) (labels : List String) (rowName : String) :
    Derivation.Row → Except String String
  | (.input index, clause) => leafRow names group rowName index clause
  | (step, clause) => inferenceRow names labels rowName step clause

/-- Field grammar and exact framing of one printed row. -/
inductive RowText : String → String → List EqualitySource.Literal → Datum → Prop where
  | row {quoted rowName bodyText body annotation data}
      (label : QuotedAtom quoted.toList rowName.toList)
      (formula : Body.ClauseText bodyText body)
      (source : DataText annotation data) :
      RowText (rowText quoted bodyText annotation) rowName body data

inductive RowMeaning (names : Body.Names) (group : String) (labels : List String) :
    Derivation.Row → Datum → Prop where
  | leaf {index : Nat} {clause : Equality.Clause} :
      RowMeaning names group labels (.input index, clause) (leafDatum index group)
  | inference {step : Ordered.Step} {clause : Equality.Clause} {rule : String} {infos : List Datum}
      {parents : List String}
      (info : StepInfo names step rule infos)
      (labelled : step.parents.map (fun index => labels[index]?) = parents.map some) :
      RowMeaning names group labels (step, clause)
        (.function "inference" [.atom rule, .list infos, .list (parents.map Datum.atom)])

def RowCorrespondence (names : Body.Names) (group : String) (labels : List String)
    (rowName : String) (row : Derivation.Row) (text : String) : Prop :=
  ∃ named data, Body.NamedClause names row.2 named ∧ RowMeaning names group labels row data ∧
    RowText text rowName named data

private theorem bind_ok {α β : Type} {action : Except String α}
    {next : α → Except String β} {result : β}
    (success : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem leaf_annotation (index : Nat) {group parent : String}
    (quoted : TstpExport.quote group = .ok parent) :
    DataText (leafAnnotation index parent) (leafDatum index group) := by
  unfold leafAnnotation leafDatum call bracket
  exact .function (checked_lower "inference" (by decide)) (by simp)
    (.cons (.atom (checked_lower "fang_group_clause" (by decide)))
      (.cons (.list (.cons status_text (.cons
          (.function (checked_lower "clause_index" (by decide)) (by simp)
            (.cons (natural_text index) .nil)) .nil)))
        (.cons (.list (.cons (quoted_data quoted) .nil)) .nil)))

theorem leafRow_correspondence {names group rowName index clause text} {labels : List String}
    (success : leafRow names group rowName index clause = .ok text) :
    RowCorrespondence names group labels rowName (.input index, clause) text := by
  unfold leafRow at success
  obtain ⟨quoted, quotedRun, success⟩ := bind_ok success
  obtain ⟨body, bodyRun, success⟩ := bind_ok success
  obtain ⟨parent, parentRun, success⟩ := bind_ok success
  have same := Except.ok.inj success
  subst same
  obtain ⟨named, sameClause, grammar⟩ := Body.clause_correspondence bodyRun
  exact ⟨named, _, sameClause, .leaf, .row (quote_grammar quotedRun) grammar (leaf_annotation index parentRun)⟩

theorem inferenceRow_correspondence {names labels rowName step clause text} {group : String}
    (success : inferenceRow names labels rowName step clause = .ok text) :
    RowCorrespondence names group labels rowName (step, clause) text := by
  unfold inferenceRow at success
  obtain ⟨quoted, quotedRun, success⟩ := bind_ok success
  obtain ⟨body, bodyRun, success⟩ := bind_ok success
  obtain ⟨info, infoRun, success⟩ := bind_ok success
  obtain ⟨parents, parentsRun, success⟩ := bind_ok success
  have same := Except.ok.inj success
  subst same
  obtain ⟨named, sameClause, grammar⟩ := Body.clause_correspondence bodyRun
  obtain ⟨rule, texts⟩ := info
  obtain ⟨lower, infos, meaning, infoGrammar⟩ := stepInfo_correspondence infoRun
  obtain ⟨values, labelled, parentGrammar⟩ := parentLabels_correspondence parentsRun
  exact ⟨named, _, sameClause, .inference meaning labelled,
    .row (quote_grammar quotedRun) grammar (by
      unfold call bracket
      exact .function (checked_lower "inference" (by decide)) (by simp)
        (.cons (.atom (checked_lower rule lower)) (.cons (.list infoGrammar)
          (.cons (.list parentGrammar) .nil))))⟩

theorem renderRow_correspondence {names group labels rowName row text}
    (success : renderRow names group labels rowName row = .ok text) :
    RowCorrespondence names group labels rowName row text := by
  obtain ⟨step, clause⟩ := row
  cases step with
  | input index => exact leafRow_correspondence success
  | factor parent first second substitution claimed => exact inferenceRow_correspondence success
  | equalityResolution parent before after left right substitution claimed =>
    exact inferenceRow_correspondence success
  | resolution left leftPosition right rightPosition substitution claimed =>
    exact inferenceRow_correspondence success
  | paramodulation source target witness claimed => exact inferenceRow_correspondence success

/-- One label per retained row, in order. Parent labels are looked up in the
    same list, so a parent prints the label of the row it indexes. -/
def render (names : Body.Names) (group : String) (labels : List String)
    (rows : List Derivation.Row) : Except String (List String) :=
  if labels.length = rows.length then
    (labels.zip rows).mapM (fun pair => renderRow names group labels pair.1 pair.2)
  else .error "export-error: row label count differs"

theorem mapM_related {α β : Type} {relation : α → β → Prop} {action : α → Except String β}
    (correct : ∀ {input output}, action input = .ok output → relation input output) :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM action = .ok outputs →
      Source.RelatedLists relation inputs outputs
  | [], outputs, success => by
    simp [pure, Except.pure] at success
    subst outputs
    exact .nil
  | input :: rest, outputs, success => by
    cases headRun : action input with
    | error reason => simp [List.mapM_cons, headRun, bind, Except.bind] at success
    | ok head =>
      cases tailRun : rest.mapM action with
      | error reason => simp [List.mapM_cons, headRun, tailRun, bind, Except.bind] at success
      | ok tail =>
        simp [List.mapM_cons, headRun, tailRun, bind, Except.bind, pure, Except.pure] at success
        subst outputs
        exact .cons (correct headRun) (mapM_related correct tailRun)

theorem render_correspondence {names group labels rows texts}
    (success : render names group labels rows = .ok texts) :
    labels.length = rows.length ∧
      Source.RelatedLists (fun pair text => RowCorrespondence names group labels pair.1 pair.2 text)
        (labels.zip rows) texts := by
  unfold render at success
  split at success
  · rename_i lengths
    exact ⟨lengths, mapM_related
      (relation := fun (pair : String × Derivation.Row) (text : String) =>
        RowCorrespondence names group labels pair.1 pair.2 text)
      (action := fun (pair : String × Derivation.Row) => renderRow names group labels pair.1 pair.2)
      (fun run => renderRow_correspondence run) success⟩
  · cases success

theorem related_member {α β : Type} {first second : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : Source.RelatedLists first inputs outputs) :
    (∀ input ∈ inputs, ∀ output, first input output → second input output) →
      Source.RelatedLists second inputs outputs := by
  induction related with
  | nil => intro _; exact .nil
  | cons head tail ih =>
    intro transfer
    exact .cons (transfer _ List.mem_cons_self _ head)
      (ih (fun input member => transfer input (List.mem_cons_of_mem _ member)))

/-- Every printed row, leaf or inference, has a body that holds in every source
    model whose table reading satisfies the prepared problem. Discharging that
    premise from the group row is the document's obligation. -/
theorem render_valid {input proof limits maximumPredicates maximumLiterals output names group labels texts}
    (built : build input proof limits maximumPredicates maximumLiterals = .ok output)
    (rendered : render names group labels (Derivation.rows output) = .ok texts)
    {D : Type} (model : Source.Interpretation D)
    (prepared : Equality.models (TstpText.tableModel names.view model) output.prepared.problem) :
    Source.RelatedLists (fun pair text => ∃ named data, RowMeaning names group labels pair.2 data ∧
        RowText text pair.1 named data ∧ (EqualitySource.Clause.mk pair.1 named).Valid model)
      (labels.zip (Derivation.rows output)) texts := by
  obtain ⟨_, related⟩ := render_correspondence rendered
  apply related_member related
  intro ⟨label, row⟩ member text correspondence
  obtain ⟨named, data, same, meaning, grammar⟩ := correspondence
  have rowMember : row ∈ Derivation.rows output := (List.of_mem_zip member).2
  exact ⟨named, data, meaning, grammar, same.valid model label
    (Derivation.build_row_valid built (TstpText.tableModel names.view model) prepared rowMember)⟩

/-- Parents of a printed inference row are labels of strictly earlier rows. -/
theorem render_parents_earlier {input proof limits maximumPredicates maximumLiterals output}
    (built : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : Derivation.rows output = leading ++ value :: rest) :
    ∀ parent ∈ value.1.parents, parent < leading.length :=
  Derivation.build_parent_before built position

/-- A leaf restates the prepared clause at its index. -/
theorem render_leaf_exact {input proof limits maximumPredicates maximumLiterals output}
    (built : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {leading index clause rest}
    (position : Derivation.rows output = leading ++ (.input index, clause) :: rest) :
    output.prepared.problem[index]? = some clause :=
  Derivation.build_input_clause built position

#print axioms Fang.QuantifiedEqualityTstp.Rows.stepInfo_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Rows.position_text
#print axioms Fang.QuantifiedEqualityTstp.Rows.parentLabels_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Rows.leaf_annotation
#print axioms Fang.QuantifiedEqualityTstp.Rows.leafRow_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Rows.inferenceRow_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Rows.renderRow_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Rows.mapM_related
#print axioms Fang.QuantifiedEqualityTstp.Rows.render_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Rows.related_member
#print axioms Fang.QuantifiedEqualityTstp.Rows.render_valid
#print axioms Fang.QuantifiedEqualityTstp.Rows.render_parents_earlier
#print axioms Fang.QuantifiedEqualityTstp.Rows.render_leaf_exact

end Fang.QuantifiedEqualityTstp.Rows
