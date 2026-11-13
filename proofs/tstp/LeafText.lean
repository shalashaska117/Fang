/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import NamedSemantics
import ExportProvenance

namespace Fang.TstpExport.BuilderProof
open Fang.TstpText

def printedVariable (variables : Source.Variables) (name : String) : String :=
  s!"X{variables.id name}"

mutual
def renameTerm (rename : String → String) : Source.Term → Source.Term
  | .var name => .var (rename name)
  | .app name arguments => .app name (renameTerms rename arguments)
def renameTerms (rename : String → String) : List Source.Term → List Source.Term
  | [] => []
  | term :: terms => renameTerm rename term :: renameTerms rename terms
end

def renameLiteral (rename : String → String) (literal : Source.Literal) : Source.Literal :=
  ⟨literal.positive, literal.predicate, renameTerms rename literal.arguments⟩

mutual
inductive TermOccurs (name : String) : Source.Term → Prop where
  | variable : TermOccurs name (.var name)
  | application {symbol arguments} (child : TermsOccurs name arguments) :
      TermOccurs name (.app symbol arguments)
inductive TermsOccurs (name : String) : List Source.Term → Prop where
  | head {term terms} (found : TermOccurs name term) : TermsOccurs name (term :: terms)
  | tail {term terms} (found : TermsOccurs name terms) : TermsOccurs name (term :: terms)
end

def ClauseOccurs (name : String) (clause : Source.Clause) : Prop :=
  ∃ literal ∈ clause.literals, TermsOccurs name literal.arguments

/-- Exact syntactic renaming, injective on all variables occurring in the clause. -/
def AlphaRenamedBy (rename : String → String) (original printed : Source.Clause) : Prop :=
  printed.name = original.name ∧
  printed.literals = original.literals.map (renameLiteral rename) ∧
  ∀ left right, ClauseOccurs left original → ClauseOccurs right original →
    rename left = rename right → left = right

mutual
theorem term_encoding_named {signature symbols variables original encoded printed table}
    (encoding : Source.TermEncoding signature symbols variables original encoded)
    (named : NamedTerm table encoded printed)
    (functions : ∀ index, Frontend.tableName table index = symbols.functionName index) :
    printed = renameTerm (printedVariable variables) original := by
  cases encoding with
  | var name _ =>
      cases named
      rfl
  | app name arguments encoded roundtrip arity children =>
      cases named with
      | application symbol namedChildren =>
          have same := symbol.table_name.symm.trans ((functions _).trans roundtrip)
          have argumentsSame := terms_encoding_named children namedChildren functions
          cases same
          simp only [renameTerm, argumentsSame]
theorem terms_encoding_named {signature symbols variables originals encoded printed table}
    (encoding : Source.TermsEncoding signature symbols variables originals encoded)
    (named : NamedTerms table encoded printed)
    (functions : ∀ index, Frontend.tableName table index = symbols.functionName index) :
    printed = renameTerms (printedVariable variables) originals := by
  cases encoding with
  | nil => cases named; rfl
  | cons head tail =>
      cases named with
      | cons namedHead namedTail =>
          simp only [renameTerms, term_encoding_named head namedHead functions,
            terms_encoding_named tail namedTail functions]
end

mutual
theorem term_occurs_roundtrip {signature symbols variables original encoded name}
    (encoding : Source.TermEncoding signature symbols variables original encoded)
    (occurs : TermOccurs name original) : variables.name (variables.id name) = name := by
  cases encoding with
  | var _ roundtrip => cases occurs; exact roundtrip
  | app _ _ _ _ _ children =>
      cases occurs with
      | application child => exact terms_occurs_roundtrip children child
theorem terms_occurs_roundtrip {signature symbols variables originals encoded name}
    (encoding : Source.TermsEncoding signature symbols variables originals encoded)
    (occurs : TermsOccurs name originals) : variables.name (variables.id name) = name := by
  cases encoding with
  | nil => cases occurs
  | cons head tail =>
      cases occurs with
      | head found => exact term_occurs_roundtrip head found
      | tail found => exact terms_occurs_roundtrip tail found
end

theorem literal_encoding_named {signature symbols variables original encoded printed problem}
    (encoding : Source.LiteralEncoding signature symbols variables original encoded)
    (named : NamedLiteral problem encoded printed)
    (functions : ∀ index, Frontend.tableName problem.functions index = symbols.functionName index)
    (predicates : ∀ index, Frontend.tableName problem.predicates index = symbols.predicateName index) :
    printed = renameLiteral (printedVariable variables) original := by
  have polarity := named.polarity.trans encoding.polarity
  have predicate : printed.predicate = original.predicate := by
    calc
      printed.predicate = Frontend.tableName problem.predicates encoded.atom.pred :=
        named.predicate.table_name.symm
      _ = symbols.predicateName (symbols.predicateId original.predicate) := by
        rw [encoding.predicate, predicates]
      _ = original.predicate := encoding.roundtrip
  have arguments := terms_encoding_named encoding.arguments named.arguments functions
  change Source.Literal.mk printed.positive printed.predicate printed.arguments =
    Source.Literal.mk original.positive original.predicate
      (renameTerms (printedVariable variables) original.arguments)
  rw [polarity, predicate, arguments]

theorem clause_encoding_named {signature symbols variables original encoded printed problem}
    (encoding : Source.ClauseEncoding signature symbols variables original encoded)
    (named : NamedClause problem encoded printed)
    (functions : ∀ index, Frontend.tableName problem.functions index = symbols.functionName index)
    (predicates : ∀ index, Frontend.tableName problem.predicates index = symbols.predicateName index) :
    printed = original.literals.map (renameLiteral (printedVariable variables)) := by
  unfold Source.ClauseEncoding at encoding
  generalize original.literals = originals at encoding ⊢
  induction encoding generalizing printed with
  | nil => cases named; rfl
  | cons head tail ih =>
      cases named with
      | cons namedHead namedTail =>
          simp only [List.map_cons, literal_encoding_named head namedHead functions predicates,
            ih namedTail]

theorem clause_occurs_roundtrip {signature symbols variables original encoded name}
    (encoding : Source.ClauseEncoding signature symbols variables original encoded)
    (occurs : ClauseOccurs name original) : variables.name (variables.id name) = name := by
  obtain ⟨literal, member, inArguments⟩ := occurs
  obtain ⟨_, _, related⟩ := encoding.member_left member
  exact terms_occurs_roundtrip related.arguments inArguments

theorem printed_variable_injective {signature symbols variables original encoded}
    (encoding : Source.ClauseEncoding signature symbols variables original encoded)
    (left right : String) (leftOccurs : ClauseOccurs left original)
    (rightOccurs : ClauseOccurs right original)
    (equal : printedVariable variables left = printedVariable variables right) : left = right := by
  have ids := variable_name_injective equal
  have names := congrArg variables.name ids
  simpa only [clause_occurs_roundtrip encoding leftOccurs,
    clause_occurs_roundtrip encoding rightOccurs] using names

theorem clause_encoding_alpha {signature symbols variables original encoded printed problem}
    (encoding : Source.ClauseEncoding signature symbols variables original encoded)
    (named : NamedClause problem encoded printed)
    (functions : ∀ index, Frontend.tableName problem.functions index = symbols.functionName index)
    (predicates : ∀ index, Frontend.tableName problem.predicates index = symbols.predicateName index) :
    AlphaRenamedBy (printedVariable variables) original ⟨original.name, printed⟩ :=
  ⟨rfl, clause_encoding_named encoding named functions predicates,
    printed_variable_injective encoding⟩

/-- Every raw input row is exactly a clause-local injective renaming of the
    original indexed source clause, using the same rendered row witnesses. -/
def RawLeafText (input : String) (problem : NamedProblem) (fileLabel : String)
    (row : Row) (text : String) : Prop :=
  ∀ source name, row.origin = .input source name →
    ∃ original clause variables named metadata,
      Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      original[source]? = some clause ∧ clause.name = name ∧
      NamedClause problem row.clause named ∧
      SourceMeaning problem fileLabel row.origin metadata ∧
      AnnotatedRowText text row.name (originRole row.origin) named metadata ∧
      AlphaRenamedBy (printedVariable variables) clause ⟨row.name, named⟩

theorem built_row_alpha {input : String} {problem : NamedProblem} {certificate : Certificate}
    {output : Export} {row : Row} {fileLabel text : String}
    (decoded : decodeNamed input = .ok problem) (built : build problem certificate = .ok output)
    (member : row ∈ output.rows)
    (correspondence : RowCorrespondence output.signature fileLabel row text) :
    RawLeafText input problem fileLabel row text := by
  have signature := (build_endpoint built).1
  rw [signature] at correspondence
  obtain ⟨named, metadata, namedClause, meaning, grammar⟩ := correspondence
  intro source name tag
  obtain ⟨rowName, original, state, clause, variables, parsed, indexed, clauseName,
    functions, predicates, encoding⟩ :=
    build_input_leaf input problem certificate output row source name decoded built member tag
  have alpha := clause_encoding_alpha encoding namedClause
    (fun index => by simp only [functions, Frontend.symbolsFrom])
    (fun index => by simp only [predicates, Frontend.symbolsFrom])
  refine ⟨original, clause, variables, named, metadata, parsed, indexed, clauseName,
    namedClause, meaning, grammar, ?_⟩
  simpa only [rowName, clauseName] using alpha

theorem rendered_leaves_alpha {input : String} {problem : NamedProblem} {certificate : Certificate}
    {output : Export} {text : String} (fileLabel : String)
    (decoded : decodeNamed input = .ok problem) (built : build problem certificate = .ok output)
    (rendered : render fileLabel output = .ok text) :
    ∃ lines, text = String.join lines ∧
      Source.RelatedLists
        (fun row line => RowCorrespondence output.signature fileLabel row line ∧
          RawLeafText input problem fileLabel row line) output.rows lines ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  obtain ⟨lines, joined, correspondence, size⟩ := render_correspondence fileLabel output rendered
  refine ⟨lines, joined, ?_, size⟩
  have strengthen : ∀ rows lines,
      Source.RelatedLists (RowCorrespondence output.signature fileLabel) rows lines →
      (∀ row ∈ rows, row ∈ output.rows) →
      Source.RelatedLists
        (fun row line => RowCorrespondence output.signature fileLabel row line ∧
          RawLeafText input problem fileLabel row line) rows lines := by
    intro rows lines relation
    induction relation with
    | nil => intro _; exact .nil
    | cons head tail ih =>
      intro members
      exact .cons ⟨head, built_row_alpha decoded built (members _ (by simp)) head⟩
        (ih (fun row member => members row (List.mem_cons_of_mem _ member)))
  exact strengthen _ _ correspondence (fun _ member => member)

end Fang.TstpExport.BuilderProof
