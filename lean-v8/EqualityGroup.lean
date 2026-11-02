/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The closed conjunction of the prepared equality clauses, named by the
   checked export tables and printed in the version-7 formula grammar. -/
import EqualityFormulaText
import EqualityRows

namespace Fang.QuantifiedEqualityTstp.Group
open TstpText

mutual
def namedTerm (symbols : List Frontend.Symbol) : Fang.Term → Except String Source.Term
  | .var index => .ok (.var s!"X{index}")
  | .app index arguments =>
    match TstpExport.symbol symbols index arguments.length, namedTerms symbols arguments with
    | .ok symbol, .ok named => .ok (.app symbol named)
    | .error reason, _ => .error reason
    | .ok _, .error reason => .error reason

def namedTerms (symbols : List Frontend.Symbol) : List Fang.Term → Except String (List Source.Term)
  | [] => .ok []
  | first :: rest =>
    match namedTerm symbols first, namedTerms symbols rest with
    | .ok head, .ok tail => .ok (head :: tail)
    | .error reason, _ => .error reason
    | .ok _, .error reason => .error reason
end

mutual
theorem namedTerm_spec {symbols : List Frontend.Symbol} :
    ∀ {term : Fang.Term} {named : Source.Term}, namedTerm symbols term = .ok named →
      NamedTerm symbols term named ∧ FormulaText.TermNames named
  | .var index, named, success => by
    simp only [namedTerm, Except.ok.injEq] at success
    subst named
    exact ⟨.variable index, by simpa [FormulaText.TermNames] using variable_name_grammar index⟩
  | .app index arguments, named, success => by
    cases symbolRun : TstpExport.symbol symbols index arguments.length with
    | error reason => simp [namedTerm, symbolRun] at success
    | ok symbol =>
      cases childRun : namedTerms symbols arguments with
      | error reason => simp [namedTerm, symbolRun, childRun] at success
      | ok children =>
        simp only [namedTerm, symbolRun, childRun, Except.ok.injEq] at success
        subst named
        have text := symbol_correspondence symbolRun
        obtain ⟨related, valid⟩ := namedTerms_spec childRun
        refine ⟨.application text related, ?_⟩
        simp only [FormulaText.TermNames]
        exact ⟨text.grammar, valid⟩

theorem namedTerms_spec {symbols : List Frontend.Symbol} :
    ∀ {terms : List Fang.Term} {named : List Source.Term}, namedTerms symbols terms = .ok named →
      NamedTerms symbols terms named ∧ ∀ term ∈ named, FormulaText.TermNames term
  | [], named, success => by
    simp only [namedTerms, Except.ok.injEq] at success
    subst named
    exact ⟨.nil, by simp⟩
  | first :: rest, named, success => by
    cases headRun : namedTerm symbols first with
    | error reason => simp [namedTerms, headRun] at success
    | ok head =>
      cases tailRun : namedTerms symbols rest with
      | error reason => simp [namedTerms, headRun, tailRun] at success
      | ok tail =>
        simp only [namedTerms, headRun, tailRun, Except.ok.injEq] at success
        subst named
        obtain ⟨headRelated, headValid⟩ := namedTerm_spec headRun
        obtain ⟨tailRelated, tailValid⟩ := namedTerms_spec tailRun
        refine ⟨.cons headRelated tailRelated, ?_⟩
        intro term member
        rcases List.mem_cons.mp member with same | later
        · exact same ▸ headValid
        · exact tailValid term later
end

def namedLiteral (names : Body.Names) (value : Equality.Literal) :
    Except String EqualitySource.Literal :=
  match value.atom with
  | .predicate atom =>
    match TstpExport.symbol names.predicates atom.pred atom.args.length,
        namedTerms names.functions atom.args with
    | .ok symbol, .ok arguments => .ok ⟨value.positive, .predicate symbol arguments⟩
    | .error reason, _ => .error reason
    | .ok _, .error reason => .error reason
  | .equal left right =>
    match namedTerm names.functions left, namedTerm names.functions right with
    | .ok leftNamed, .ok rightNamed => .ok ⟨value.positive, .equal leftNamed rightNamed⟩
    | .error reason, _ => .error reason
    | .ok _, .error reason => .error reason

def LiteralNames (literal : EqualitySource.Literal) : Prop :=
  match literal.atom with
  | .predicate symbol arguments => FormulaText.TermNames (.app symbol arguments)
  | .equal left right => FormulaText.TermNames left ∧ FormulaText.TermNames right

theorem namedLiteral_spec {names : Body.Names} {value : Equality.Literal} {named : EqualitySource.Literal}
    (success : namedLiteral names value = .ok named) :
    Body.NamedLiteral names value named ∧ LiteralNames named := by
  obtain ⟨positive, atom⟩ := value
  cases atom with
  | predicate atom =>
    cases symbolRun : TstpExport.symbol names.predicates atom.pred atom.args.length with
    | error reason => simp [namedLiteral, symbolRun] at success
    | ok symbol =>
      cases argumentsRun : namedTerms names.functions atom.args with
      | error reason => simp [namedLiteral, symbolRun, argumentsRun] at success
      | ok arguments =>
        simp only [namedLiteral, symbolRun, argumentsRun, Except.ok.injEq] at success
        subst named
        have text := symbol_correspondence symbolRun
        obtain ⟨related, valid⟩ := namedTerms_spec argumentsRun
        refine ⟨.predicate (named := ⟨positive, symbol, arguments⟩) ⟨rfl, text, related⟩, ?_⟩
        simp only [LiteralNames, FormulaText.TermNames]
        exact ⟨text.grammar, valid⟩
  | equal left right =>
    cases leftRun : namedTerm names.functions left with
    | error reason => simp [namedLiteral, leftRun] at success
    | ok leftNamed =>
      cases rightRun : namedTerm names.functions right with
      | error reason => simp [namedLiteral, leftRun, rightRun] at success
      | ok rightNamed =>
        simp only [namedLiteral, leftRun, rightRun, Except.ok.injEq] at success
        subst named
        obtain ⟨leftRelated, leftValid⟩ := namedTerm_spec leftRun
        obtain ⟨rightRelated, rightValid⟩ := namedTerm_spec rightRun
        refine ⟨.equal leftRelated rightRelated, ?_⟩
        simp only [LiteralNames]
        exact ⟨leftValid, rightValid⟩

def literalFormula (literal : EqualitySource.Literal) : NamedQuantifiedEquality.Formula :=
  let base : NamedQuantifiedEquality.Formula :=
    match literal.atom with
    | .predicate symbol arguments => .atom (.predicate symbol arguments)
    | .equal left right => .atom (.equal left right)
  if literal.positive then base else .neg base

theorem literalFormula_holds (literal : EqualitySource.Literal) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    (literalFormula literal).Holds model valuation ↔ literal.Holds model valuation := by
  obtain ⟨positive, atom⟩ := literal
  cases atom <;> cases positive <;>
    simp [literalFormula, NamedQuantifiedEquality.Formula.Holds, NamedQuantifiedEquality.Atom.Holds,
      EqualitySource.Literal.Holds, EqualitySource.Atom.Holds]

theorem literalFormula_names {literal : EqualitySource.Literal} (valid : LiteralNames literal) :
    FormulaText.FormulaNames (literalFormula literal) := by
  obtain ⟨positive, atom⟩ := literal
  cases atom <;> cases positive <;>
    simpa [literalFormula, LiteralNames, FormulaText.FormulaNames, FormulaText.AtomNames] using valid

def disjunction : List NamedQuantifiedEquality.Formula → NamedQuantifiedEquality.Formula
  | [] => .falsity
  | [single] => single
  | first :: rest => .disj first (disjunction rest)

def conjunction : List NamedQuantifiedEquality.Formula → NamedQuantifiedEquality.Formula
  | [] => .truth
  | [single] => single
  | first :: rest => .conj first (conjunction rest)

theorem disjunction_holds (formulas : List NamedQuantifiedEquality.Formula) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    (disjunction formulas).Holds model valuation ↔ ∃ formula ∈ formulas, formula.Holds model valuation := by
  induction formulas with
  | nil => simp [disjunction, NamedQuantifiedEquality.Formula.Holds]
  | cons first rest ih =>
    cases rest with
    | nil => simp [disjunction]
    | cons second tail =>
      simp only [disjunction, NamedQuantifiedEquality.Formula.Holds] at ih ⊢
      rw [ih]
      simp

theorem conjunction_holds (formulas : List NamedQuantifiedEquality.Formula) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    (conjunction formulas).Holds model valuation ↔ ∀ formula ∈ formulas, formula.Holds model valuation := by
  induction formulas with
  | nil => simp [conjunction, NamedQuantifiedEquality.Formula.Holds]
  | cons first rest ih =>
    cases rest with
    | nil => simp [conjunction]
    | cons second tail =>
      simp only [conjunction, NamedQuantifiedEquality.Formula.Holds] at ih ⊢
      rw [ih]
      simp

theorem disjunction_names {formulas : List NamedQuantifiedEquality.Formula}
    (valid : ∀ formula ∈ formulas, FormulaText.FormulaNames formula) :
    FormulaText.FormulaNames (disjunction formulas) := by
  induction formulas with
  | nil => simp [disjunction, FormulaText.FormulaNames]
  | cons first rest ih =>
    cases rest with
    | nil => simpa [disjunction] using valid
    | cons second tail =>
      exact ⟨valid first (by simp), ih (fun formula member => valid formula (by simp_all))⟩

theorem conjunction_names {formulas : List NamedQuantifiedEquality.Formula}
    (valid : ∀ formula ∈ formulas, FormulaText.FormulaNames formula) :
    FormulaText.FormulaNames (conjunction formulas) := by
  induction formulas with
  | nil => simp [conjunction, FormulaText.FormulaNames]
  | cons first rest ih =>
    cases rest with
    | nil => simpa [conjunction] using valid
    | cons second tail =>
      exact ⟨valid first (by simp), ih (fun formula member => valid formula (by simp_all))⟩

-- Variable names of a source term, in order of occurrence (duplicates kept).
mutual
def termVariables : Source.Term → List String
  | .var binder => [binder]
  | .app _ arguments => termsVariables arguments

def termsVariables : List Source.Term → List String
  | [] => []
  | first :: rest => termVariables first ++ termsVariables rest
end

def literalVariables (literal : EqualitySource.Literal) : List String :=
  match literal.atom with
  | .predicate _ arguments => termsVariables arguments
  | .equal left right => termVariables left ++ termVariables right

def addFresh (seen : List String) (binder : String) : List String :=
  if binder ∈ seen then seen else seen ++ [binder]

/-- Each variable of the clause once, in order of first occurrence. -/
def clauseBinders (literals : List EqualitySource.Literal) : List String :=
  (literals.flatMap literalVariables).foldl addFresh []

def closeOver (binders : List String) (body : NamedQuantifiedEquality.Formula) :
    NamedQuantifiedEquality.Formula :=
  binders.foldr (fun binder tail => .all binder tail) body

theorem update_self {D : Type} (valuation : String → D) (binder : String) :
    NamedQuantified.update valuation binder (valuation binder) = valuation := by
  funext other
  by_cases same : other = binder
  · subst same; simp [NamedQuantified.update]
  · simp [NamedQuantified.update, same]

theorem closeOver_valid (binders : List String) (body : NamedQuantifiedEquality.Formula) {D : Type}
    (model : Source.Interpretation D) :
    (∀ valuation, (closeOver binders body).Holds model valuation) ↔
      ∀ valuation, body.Holds model valuation := by
  induction binders with
  | nil => rfl
  | cons binder rest ih =>
    simp only [closeOver, List.foldr_cons, NamedQuantifiedEquality.Formula.Holds] at ih ⊢
    rw [← ih]
    constructor
    · intro holds valuation
      have := holds valuation (valuation binder)
      rwa [update_self] at this
    · intro holds valuation value
      exact holds _

theorem closeOver_names {binders : List String} {body : NamedQuantifiedEquality.Formula}
    (valid : ∀ binder ∈ binders, Source.Grammar.VariableName binder) (bodyValid : FormulaText.FormulaNames body) :
    FormulaText.FormulaNames (closeOver binders body) := by
  induction binders with
  | nil => exact bodyValid
  | cons binder rest ih =>
    exact ⟨valid binder (by simp), ih (fun other member => valid other (by simp [member]))⟩

def clauseFormula (names : Body.Names) (clause : Equality.Clause) :
    Except String NamedQuantifiedEquality.Formula :=
  match clause.mapM (namedLiteral names) with
  | .ok literals => .ok (closeOver (clauseBinders literals) (disjunction (literals.map literalFormula)))
  | .error reason => .error reason

def groupFormula (names : Body.Names) (problem : Equality.Problem) :
    Except String NamedQuantifiedEquality.Formula :=
  match problem.mapM (clauseFormula names) with
  | .ok formulas => .ok (conjunction formulas)
  | .error reason => .error reason

def groupText (names : Body.Names) (problem : Equality.Problem) : Except String String :=
  match groupFormula names problem with
  | .ok formula => FormulaText.render formula
  | .error reason => .error reason

/-! ### Closedness -/

theorem addFresh_mem {seen : List String} {binder other : String} :
    other ∈ addFresh seen binder ↔ other ∈ seen ∨ other = binder := by
  by_cases present : binder ∈ seen
  · have same : addFresh seen binder = seen := by simp [addFresh, present]
    rw [same]
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · have same : addFresh seen binder = seen ++ [binder] := by simp [addFresh, present]
    rw [same]
    simp

theorem foldl_addFresh_mem (values : List String) :
    ∀ (seen : List String) (other : String),
      other ∈ values.foldl addFresh seen ↔ other ∈ seen ∨ other ∈ values := by
  induction values with
  | nil => intro seen other; simp
  | cons first rest ih =>
    intro seen other
    simp only [List.foldl_cons]
    rw [ih, addFresh_mem]
    simp only [List.mem_cons]
    tauto

theorem clauseBinders_mem {literals : List EqualitySource.Literal} {other : String} :
    other ∈ clauseBinders literals ↔ other ∈ literals.flatMap literalVariables := by
  unfold clauseBinders
  rw [foldl_addFresh_mem]
  simp

mutual
theorem term_within {bound : List String} :
    ∀ (term : Source.Term), (∀ binder ∈ termVariables term, binder ∈ bound) →
      NamedQuantified.TermWithin bound term
  | .var binder, covered => by
    simpa [termVariables, NamedQuantified.TermWithin] using covered
  | .app symbol arguments, covered => by
    simp only [NamedQuantified.TermWithin]
    exact terms_within arguments (by simpa [termVariables] using covered)

theorem terms_within {bound : List String} :
    ∀ (terms : List Source.Term), (∀ binder ∈ termsVariables terms, binder ∈ bound) →
      ∀ term ∈ terms, NamedQuantified.TermWithin bound term
  | [], _ => by simp
  | first :: rest, covered => by
    intro term member
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact term_within term (fun binder occurs =>
        covered binder (by simp [termsVariables, occurs]))
    · exact terms_within rest (fun binder occurs =>
        covered binder (by simp [termsVariables, occurs])) term later
end

theorem literalFormula_within {bound : List String} {literal : EqualitySource.Literal}
    (covered : ∀ binder ∈ literalVariables literal, binder ∈ bound) :
    (literalFormula literal).Within bound := by
  obtain ⟨positive, atom⟩ := literal
  cases atom with
  | predicate symbol arguments =>
    have within := terms_within (bound := bound) arguments (by simpa [literalVariables] using covered)
    cases positive <;>
      simpa [literalFormula, NamedQuantifiedEquality.Formula.Within, NamedQuantifiedEquality.Atom.Within]
        using within
  | equal left right =>
    have leftWithin := term_within (bound := bound) left (fun binder occurs =>
      covered binder (by simp [literalVariables, occurs]))
    have rightWithin := term_within (bound := bound) right (fun binder occurs =>
      covered binder (by simp [literalVariables, occurs]))
    cases positive <;>
      simp [literalFormula, NamedQuantifiedEquality.Formula.Within, NamedQuantifiedEquality.Atom.Within,
        leftWithin, rightWithin]

theorem disjunction_within {bound : List String} {formulas : List NamedQuantifiedEquality.Formula}
    (within : ∀ formula ∈ formulas, formula.Within bound) : (disjunction formulas).Within bound := by
  induction formulas with
  | nil => simp [disjunction, NamedQuantifiedEquality.Formula.Within]
  | cons first rest ih =>
    cases rest with
    | nil => simpa [disjunction] using within
    | cons second tail =>
      exact ⟨within first (by simp), ih (fun formula member => within formula (by simp_all))⟩

theorem conjunction_within {bound : List String} {formulas : List NamedQuantifiedEquality.Formula}
    (within : ∀ formula ∈ formulas, formula.Within bound) : (conjunction formulas).Within bound := by
  induction formulas with
  | nil => simp [conjunction, NamedQuantifiedEquality.Formula.Within]
  | cons first rest ih =>
    cases rest with
    | nil => simpa [conjunction] using within
    | cons second tail =>
      exact ⟨within first (by simp), ih (fun formula member => within formula (by simp_all))⟩

theorem closeOver_within (binders : List String) (body : NamedQuantifiedEquality.Formula) :
    ∀ (bound : List String), (closeOver binders body).Within bound ↔ body.Within (binders.reverse ++ bound) := by
  induction binders with
  | nil => intro bound; simp [closeOver]
  | cons binder rest ih =>
    intro bound
    simp only [closeOver, List.foldr_cons, NamedQuantifiedEquality.Formula.Within] at ih ⊢
    rw [ih]
    simp

mutual
theorem term_variables_valid :
    ∀ (term : Source.Term), FormulaText.TermNames term →
      ∀ binder ∈ termVariables term, Source.Grammar.VariableName binder
  | .var binder, valid => by
    intro other member
    simp only [termVariables, List.mem_singleton] at member
    subst member
    simpa [FormulaText.TermNames] using valid
  | .app symbol arguments, valid => by
    intro other member
    simp only [FormulaText.TermNames] at valid
    exact terms_variables_valid arguments valid.2 other (by simpa [termVariables] using member)

theorem terms_variables_valid :
    ∀ (terms : List Source.Term), (∀ term ∈ terms, FormulaText.TermNames term) →
      ∀ binder ∈ termsVariables terms, Source.Grammar.VariableName binder
  | [], _ => by simp [termsVariables]
  | first :: rest, valid => by
    intro other member
    simp only [termsVariables, List.mem_append] at member
    rcases member with here | later
    · exact term_variables_valid first (valid first (by simp)) other here
    · exact terms_variables_valid rest (fun term member => valid term (by simp [member])) other later
end

theorem literal_variables_valid {literal : EqualitySource.Literal} (valid : LiteralNames literal) :
    ∀ binder ∈ literalVariables literal, Source.Grammar.VariableName binder := by
  obtain ⟨positive, atom⟩ := literal
  cases atom with
  | predicate symbol arguments =>
    simp only [LiteralNames, FormulaText.TermNames] at valid
    simpa [literalVariables] using terms_variables_valid arguments valid.2
  | equal left right =>
    simp only [LiteralNames] at valid
    intro binder member
    simp only [literalVariables, List.mem_append] at member
    rcases member with here | there
    · exact term_variables_valid left valid.1 binder here
    · exact term_variables_valid right valid.2 binder there

/-! ### Named clauses -/

theorem namedClause_spec {names : Body.Names} {clause : Equality.Clause}
    {literals : List EqualitySource.Literal}
    (success : clause.mapM (namedLiteral names) = .ok literals) :
    Body.NamedClause names clause literals ∧ ∀ literal ∈ literals, LiteralNames literal := by
  have related := Rows.mapM_related
    (relation := fun (value : Equality.Literal) (named : EqualitySource.Literal) =>
      Body.NamedLiteral names value named ∧ LiteralNames named)
    (action := namedLiteral names) (fun run => namedLiteral_spec run) success
  refine ⟨related.imp (fun _ _ both => both.1), ?_⟩
  intro literal member
  obtain ⟨_, _, both⟩ := related.member_right member
  exact both.2

/-- A valuation of names that reads `X{i}` as `σ i`. -/
noncomputable def indexValuation {D : Type} (σ : Nat → D) : String → D := fun binder =>
  haveI := Classical.propDecidable (∃ index : Nat, binder = s!"X{index}")
  if found : ∃ index : Nat, binder = s!"X{index}" then σ (Classical.choose found) else σ 0

theorem indexValuation_at {D : Type} (σ : Nat → D) (index : Nat) :
    indexValuation σ s!"X{index}" = σ index := by
  have found : ∃ other : Nat, s!"X{index}" = s!"X{other}" := ⟨index, rfl⟩
  unfold indexValuation
  split
  · rename_i present
    exact congrArg σ (variable_name_injective (Classical.choose_spec present)).symm
  · rename_i absent
    exact absurd found absent

theorem indexValuation_spec {D : Type} (σ : Nat → D) :
    (fun index => indexValuation σ s!"X{index}") = σ := by
  funext index
  exact indexValuation_at σ index

theorem namedClause_valid_iff {names : Body.Names} {clause : Equality.Clause}
    {literals : List EqualitySource.Literal} (same : Body.NamedClause names clause literals)
    {D : Type} (model : Source.Interpretation D) (label : String) :
    (EqualitySource.Clause.mk label literals).Valid model ↔
      Equality.clauseValid (tableModel names.view model) clause := by
  constructor
  · intro valid σ
    obtain ⟨literal, member, holds⟩ := valid (indexValuation σ)
    obtain ⟨value, valueMember, relation⟩ := same.member_right member
    have numeric := (relation.holds model (indexValuation σ)).mp holds
    rw [indexValuation_spec] at numeric
    exact ⟨value, valueMember, numeric⟩
  · exact same.valid model label

/-! ### Clause and group formulas -/

theorem clauseFormula_spec {names : Body.Names} {clause : Equality.Clause}
    {formula : NamedQuantifiedEquality.Formula} (success : clauseFormula names clause = .ok formula) :
    FormulaText.FormulaNames formula ∧ formula.Within [] ∧
      ∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Equality.clauseValid (tableModel names.view model) clause := by
  cases literalsRun : clause.mapM (namedLiteral names) with
  | error reason => simp [clauseFormula, literalsRun] at success
  | ok literals =>
    simp only [clauseFormula, literalsRun, Except.ok.injEq] at success
    subst formula
    obtain ⟨same, valid⟩ := namedClause_spec literalsRun
    refine ⟨?_, ?_, ?_⟩
    · apply closeOver_names
      · intro binder member
        rw [clauseBinders_mem] at member
        obtain ⟨literal, literalMember, occurs⟩ := List.mem_flatMap.mp member
        exact literal_variables_valid (valid literal literalMember) binder occurs
      · exact disjunction_names (fun formula member => by
          obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
          exact literalFormula_names (valid literal literalMember))
    · rw [closeOver_within]
      apply disjunction_within
      intro formula member
      obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
      apply literalFormula_within
      intro binder occurs
      have : binder ∈ clauseBinders literals :=
        clauseBinders_mem.mpr (List.mem_flatMap.mpr ⟨literal, literalMember, occurs⟩)
      simpa using this
    · intro D model
      rw [closeOver_valid, ← namedClause_valid_iff same model ""]
      simp only [EqualitySource.Clause.Valid, disjunction_holds, List.mem_map]
      constructor
      · intro holds valuation
        obtain ⟨formula, ⟨literal, member, rfl⟩, formulaHolds⟩ := holds valuation
        exact ⟨literal, member, (literalFormula_holds literal model valuation).mp formulaHolds⟩
      · intro holds valuation
        obtain ⟨literal, member, literalHolds⟩ := holds valuation
        exact ⟨literalFormula literal, ⟨literal, member, rfl⟩,
          (literalFormula_holds literal model valuation).mpr literalHolds⟩

theorem groupFormula_spec {names : Body.Names} {problem : Equality.Problem}
    {formula : NamedQuantifiedEquality.Formula} (success : groupFormula names problem = .ok formula) :
    FormulaText.FormulaNames formula ∧ formula.Within [] ∧
      ∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Equality.models (tableModel names.view model) problem := by
  cases formulasRun : problem.mapM (clauseFormula names) with
  | error reason => simp [groupFormula, formulasRun] at success
  | ok formulas =>
    simp only [groupFormula, formulasRun, Except.ok.injEq] at success
    subst formula
    have related := Rows.mapM_related
      (relation := fun (clause : Equality.Clause) (formula : NamedQuantifiedEquality.Formula) =>
        FormulaText.FormulaNames formula ∧ formula.Within [] ∧
          ∀ {D : Type} (model : Source.Interpretation D),
            (∀ valuation, formula.Holds model valuation) ↔
              Equality.clauseValid (tableModel names.view model) clause)
      (action := clauseFormula names) (fun run => clauseFormula_spec run) formulasRun
    refine ⟨conjunction_names ?_, conjunction_within ?_, ?_⟩
    · intro formula member
      obtain ⟨_, _, both⟩ := related.member_right member
      exact both.1
    · intro formula member
      obtain ⟨_, _, both⟩ := related.member_right member
      exact both.2.1
    · intro D model
      unfold Equality.models
      simp only [conjunction_holds]
      constructor
      · intro holds clause member
        obtain ⟨formula, formulaMember, both⟩ := related.member_left member
        exact (both.2.2 model).mp (fun valuation => holds valuation formula formulaMember)
      · intro holds valuation formula member
        obtain ⟨clause, clauseMember, both⟩ := related.member_right member
        exact (both.2.2 model).mpr (holds clause clauseMember) valuation

/-- The printed group has exactly one reading in the accepted version-7 formula
    grammar. That reading is closed and holds exactly when the prepared problem
    holds under the table reading of the source model. -/
theorem groupText_spec {names : Body.Names} {problem : Equality.Problem} {text : String}
    (success : groupText names problem = .ok text) :
    ∃ formula, groupFormula names problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling text) formula ∧ formula.Within [] ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling text) other → other = formula) ∧
      ∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Equality.models (tableModel names.view model) problem := by
  cases formulaRun : groupFormula names problem with
  | error reason => simp [groupText, formulaRun] at success
  | ok formula =>
    simp only [groupText, formulaRun] at success
    obtain ⟨valid, closed, meaning⟩ := groupFormula_spec formulaRun
    exact ⟨formula, rfl, FormulaText.render_formula valid success, closed,
      fun other parsed => (FormulaText.render_unique valid success parsed).symm, meaning⟩

theorem group_empty_control : groupText ⟨[], []⟩ [] = .ok "$true" := rfl

#print axioms Fang.QuantifiedEqualityTstp.Group.namedTerm_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.namedTerms_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.namedLiteral_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.literalFormula_holds
#print axioms Fang.QuantifiedEqualityTstp.Group.literalFormula_names
#print axioms Fang.QuantifiedEqualityTstp.Group.disjunction_holds
#print axioms Fang.QuantifiedEqualityTstp.Group.conjunction_holds
#print axioms Fang.QuantifiedEqualityTstp.Group.disjunction_names
#print axioms Fang.QuantifiedEqualityTstp.Group.conjunction_names
#print axioms Fang.QuantifiedEqualityTstp.Group.update_self
#print axioms Fang.QuantifiedEqualityTstp.Group.closeOver_valid
#print axioms Fang.QuantifiedEqualityTstp.Group.closeOver_names
#print axioms Fang.QuantifiedEqualityTstp.Group.addFresh_mem
#print axioms Fang.QuantifiedEqualityTstp.Group.foldl_addFresh_mem
#print axioms Fang.QuantifiedEqualityTstp.Group.clauseBinders_mem
#print axioms Fang.QuantifiedEqualityTstp.Group.term_within
#print axioms Fang.QuantifiedEqualityTstp.Group.terms_within
#print axioms Fang.QuantifiedEqualityTstp.Group.literalFormula_within
#print axioms Fang.QuantifiedEqualityTstp.Group.disjunction_within
#print axioms Fang.QuantifiedEqualityTstp.Group.conjunction_within
#print axioms Fang.QuantifiedEqualityTstp.Group.closeOver_within
#print axioms Fang.QuantifiedEqualityTstp.Group.term_variables_valid
#print axioms Fang.QuantifiedEqualityTstp.Group.terms_variables_valid
#print axioms Fang.QuantifiedEqualityTstp.Group.literal_variables_valid
#print axioms Fang.QuantifiedEqualityTstp.Group.namedClause_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.indexValuation_at
#print axioms Fang.QuantifiedEqualityTstp.Group.indexValuation_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.namedClause_valid_iff
#print axioms Fang.QuantifiedEqualityTstp.Group.clauseFormula_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.groupFormula_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.groupText_spec
#print axioms Fang.QuantifiedEqualityTstp.Group.group_empty_control

end Fang.QuantifiedEqualityTstp.Group
