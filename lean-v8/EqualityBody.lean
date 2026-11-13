/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Equality clause bodies over the existing checked term renderer.
   This is independent certificate output, not a model of the Rust engine. -/
import EqualityDerivation
import Product.NamedSemantics

namespace Fang.QuantifiedEqualityTstp.Body

structure Names where
  functions : List Frontend.Symbol
  predicates : List Frontend.Symbol

/-- Only the symbol fields are used by the existing term/literal renderer.
    The empty ordinary problem is not an encoding of an equality problem. -/
def Names.view (names : Names) : TstpExport.NamedProblem where
  signature := { problem := [], functionArities := [], predicateArities := [] }
  functions := names.functions
  predicates := names.predicates
  names := []

def literal (names : Names) (value : Equality.Literal) : Except String String :=
  match value.atom with
  | .predicate atom => TstpExport.literal names.view ⟨value.positive, atom⟩
  | .equal left right => do
      let leftText ← TstpExport.term names.functions left
      let rightText ← TstpExport.term names.functions right
      pure (leftText ++ (if value.positive then " = " else " != ") ++ rightText)

def clause (names : Names) (values : Equality.Clause) : Except String String := do
  if values.isEmpty then pure "$false"
  else pure (String.intercalate " | " (← values.mapM (literal names)))

inductive NamedLiteral (names : Names) : Equality.Literal → EqualitySource.Literal → Prop where
  | predicate {positive atom named}
      (same : TstpText.NamedLiteral names.view ⟨positive, atom⟩ named) :
      NamedLiteral names ⟨positive, .predicate atom⟩
        ⟨named.positive, .predicate named.predicate named.arguments⟩
  | equal {positive left right namedLeft namedRight}
      (leftTerm : TstpText.NamedTerm names.functions left namedLeft)
      (rightTerm : TstpText.NamedTerm names.functions right namedRight) :
      NamedLiteral names ⟨positive, .equal left right⟩
        ⟨positive, .equal namedLeft namedRight⟩

abbrev NamedClause (names : Names) := Source.RelatedLists (NamedLiteral names)

/-- Exact body construction with the accepted term and predicate byte grammars.
    A consuming equality-row grammar is a separate obligation. -/
inductive LiteralText : String → EqualitySource.Literal → Prop where
  | predicate {text named}
      (parsed : TstpText.LiteralBytesParse (Source.Grammar.spelling text) named) :
      LiteralText text ⟨named.positive, .predicate named.predicate named.arguments⟩
  | equal {positive left right leftText rightText}
      (leftParsed : TstpText.TermBytesParse (Source.Grammar.spelling leftText) left)
      (rightParsed : TstpText.TermBytesParse (Source.Grammar.spelling rightText) right) :
      LiteralText (leftText ++ (if positive then " = " else " != ") ++ rightText)
        ⟨positive, .equal left right⟩

inductive ClauseText : String → List EqualitySource.Literal → Prop where
  | falsity : ClauseText "$false" []
  | disjunction {texts named} (nonempty : texts ≠ [])
      (literals : Source.RelatedLists LiteralText texts named) :
      ClauseText (String.intercalate " | " texts) named

theorem literal_correspondence {names value text}
    (printed : literal names value = .ok text) :
    ∃ named, NamedLiteral names value named ∧ LiteralText text named := by
  cases value with
  | mk positive atom =>
    cases atom with
    | predicate atom =>
      obtain ⟨named, same, parsed⟩ := TstpText.literal_byte_correspondence
        ⟨positive, atom⟩ printed
      exact ⟨_, .predicate same, .predicate parsed⟩
    | equal left right =>
      cases leftRun : TstpExport.term names.functions left with
      | error reason => simp [literal, leftRun, Bind.bind, Except.bind] at printed
      | ok leftText =>
        cases rightRun : TstpExport.term names.functions right with
        | error reason => simp [literal, leftRun, rightRun, Bind.bind, Except.bind] at printed
        | ok rightText =>
          simp [literal, leftRun, rightRun, Bind.bind, Except.bind, Pure.pure, Except.pure] at printed
          subst text
          obtain ⟨namedLeft, leftNamed, leftParsed⟩ := TstpText.term_byte_correspondence left leftRun
          obtain ⟨namedRight, rightNamed, rightParsed⟩ := TstpText.term_byte_correspondence right rightRun
          exact ⟨_, .equal leftNamed rightNamed, .equal leftParsed rightParsed⟩

theorem literals_correspondence {names values texts}
    (printed : values.mapM (literal names) = .ok texts) :
    ∃ named, NamedClause names values named ∧ Source.RelatedLists LiteralText texts named := by
  induction values generalizing texts with
  | nil =>
    simp [Pure.pure, Except.pure] at printed
    subst texts
    exact ⟨[], .nil, .nil⟩
  | cons first rest ih =>
    cases headRun : literal names first with
    | error reason => simp [List.mapM_cons, headRun, Bind.bind, Except.bind] at printed
    | ok text =>
      cases tailRun : rest.mapM (literal names) with
      | error reason => simp [List.mapM_cons, headRun, tailRun, Bind.bind, Except.bind] at printed
      | ok tail =>
        simp [List.mapM_cons, headRun, tailRun, Bind.bind, Except.bind, Pure.pure, Except.pure] at printed
        subst texts
        obtain ⟨head, same, parsed⟩ := literal_correspondence headRun
        obtain ⟨named, tailSame, tailParsed⟩ := ih tailRun
        exact ⟨head :: named, .cons same tailSame, .cons parsed tailParsed⟩

theorem clause_correspondence {names values text}
    (printed : clause names values = .ok text) :
    ∃ named, NamedClause names values named ∧ ClauseText text named := by
  cases values with
  | nil =>
    simp [clause, Pure.pure, Except.pure] at printed
    subst text
    exact ⟨[], .nil, .falsity⟩
  | cons first rest =>
    cases listRun : (first :: rest).mapM (literal names) with
    | error reason => simp [clause, listRun, Bind.bind, Except.bind] at printed
    | ok texts =>
      simp [clause, listRun, Bind.bind, Except.bind, Pure.pure, Except.pure] at printed
      subst text
      obtain ⟨named, same, parsed⟩ := literals_correspondence listRun
      have nonempty : texts ≠ [] := by
        intro empty
        subst texts
        cases parsed
        cases same
      exact ⟨named, same, .disjunction nonempty parsed⟩

theorem NamedLiteral.holds {names value named}
    (same : NamedLiteral names value named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.Holds model valuation ↔ value.Holds (TstpText.tableModel names.view model)
      (fun index => valuation s!"X{index}") := by
  cases same with
  | predicate relation =>
    simpa only [EqualitySource.Literal.Holds, EqualitySource.Atom.Holds,
      Equality.Literal.Holds, Equality.Atom.Holds, Source.Literal.Holds, Fang.Literal.Holds]
      using relation.holds model valuation
  | equal leftTerm rightTerm =>
    simp only [EqualitySource.Literal.Holds, EqualitySource.Atom.Holds,
      Equality.Literal.Holds, Equality.Atom.Holds,
      TstpText.NamedTerm.eval (problem := names.view) leftTerm model valuation,
      TstpText.NamedTerm.eval (problem := names.view) rightTerm model valuation]

theorem NamedClause.valid {names values named} (same : NamedClause names values named)
    {D : Type} (model : Source.Interpretation D) (label : String)
    (valid : Equality.clauseValid (TstpText.tableModel names.view model) values) :
    (EqualitySource.Clause.mk label named).Valid model := by
  intro valuation
  obtain ⟨value, member, holds⟩ := valid (fun index => valuation s!"X{index}")
  obtain ⟨namedValue, namedMember, relation⟩ := same.member_left member
  exact ⟨namedValue, namedMember, (relation.holds model valuation).mpr holds⟩

/-- This premise concerns the prepared model under the supplied name tables.
    Connecting those tables to original symbols and fresh Skolem names remains
    an explicit enclosing-adapter obligation. -/
theorem rendered_row_valid {input proof limits maximumPredicates maximumLiterals output}
    (built : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {value : Derivation.Row} (member : value ∈ Derivation.rows output)
    {names text} (printed : clause names value.2 = .ok text)
    {D : Type} (model : Source.Interpretation D) (label : String)
    (prepared : Equality.models (TstpText.tableModel names.view model) output.prepared.problem) :
    ∃ named, ClauseText text named ∧ (EqualitySource.Clause.mk label named).Valid model := by
  obtain ⟨named, same, parsed⟩ := clause_correspondence printed
  exact ⟨named, parsed, same.valid model label
    (Derivation.build_row_valid built (TstpText.tableModel names.view model) prepared member)⟩

#print axioms Fang.QuantifiedEqualityTstp.Body.literal_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Body.literals_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Body.clause_correspondence
#print axioms Fang.QuantifiedEqualityTstp.Body.NamedLiteral.holds
#print axioms Fang.QuantifiedEqualityTstp.Body.NamedClause.valid
#print axioms Fang.QuantifiedEqualityTstp.Body.rendered_row_valid

end Fang.QuantifiedEqualityTstp.Body
