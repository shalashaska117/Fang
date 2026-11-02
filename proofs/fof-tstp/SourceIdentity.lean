/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.FofRows
import Fang.FOF.FOFEncodingBase

namespace Fang.FofTstpText
open TstpText

private theorem congr_two {α β γ : Sort _} (f : α → β → γ)
    {a a' : α} {b b' : β} (first : a = a') (second : b = b') : f a b = f a' b' := by
  cases first
  cases second
  rfl

mutual
theorem ground_term_identity {state : Frontend.State} {source numeric printed}
    (encoded : Frontend.TableTermEncoding state source numeric)
    (ground : NamedFOF.GroundTerm source)
    (rendered : NamedTerm state.functions numeric printed) : printed = source := by
  cases encoded with
  | var name id found => simp only [NamedFOF.GroundTerm] at ground
  | app name id arguments encoded found checked children =>
    simp only [NamedFOF.GroundTerm] at ground
    cases rendered with
    | application symbol printedChildren =>
      apply congr_two Source.Term.app
      · exact (symbol_name symbol).symm.trans (Frontend.table_found found).2
      · exact ground_terms_identity children ground printedChildren
termination_by sizeOf source

theorem ground_terms_identity {state : Frontend.State} {source numeric printed}
    (encoded : Frontend.TableTermsEncoding state source numeric)
    (ground : ∀ term ∈ source, NamedFOF.GroundTerm term)
    (rendered : NamedTerms state.functions numeric printed) : printed = source := by
  cases encoded with
  | nil => cases rendered; rfl
  | cons head tail =>
    cases rendered with
    | cons first rest =>
      exact congr_two List.cons
        (ground_term_identity head (ground _ List.mem_cons_self) first)
        (ground_terms_identity tail (fun term member => ground term (List.mem_cons_of_mem _ member)) rest)
termination_by sizeOf source
end

theorem ground_formula_identity {state : Frontend.State} {problem : TstpExport.NamedProblem}
    {source numeric printed} (functions : problem.functions = state.functions)
    (predicates : problem.predicates = state.predicates)
    (encoded : FOFFrontend.TableFormulaEncoding state source numeric)
    (ground : source.Ground) (rendered : NamedFormula problem numeric printed) : printed = source := by
  induction encoded generalizing printed with
  | atom name id args encoded found arity terms =>
    cases rendered with
    | atom symbol children =>
      rw [predicates] at symbol
      rw [functions] at children
      exact congr_two NamedFOF.Formula.atom
        ((symbol_name symbol).symm.trans (Frontend.table_found found).2)
        (ground_terms_identity terms ground children)
  | truth => cases rendered; rfl
  | falsity => cases rendered; rfl
  | neg child ih =>
    cases rendered with
    | neg relation => exact congrArg NamedFOF.Formula.neg (ih ground relation)
  | conj first second leftIH rightIH =>
    cases rendered with
    | conj left right => exact congr_two NamedFOF.Formula.conj (leftIH ground.1 left) (rightIH ground.2 right)
  | disj first second leftIH rightIH =>
    cases rendered with
    | disj left right => exact congr_two NamedFOF.Formula.disj (leftIH ground.1 left) (rightIH ground.2 right)
  | implies first second leftIH rightIH =>
    cases rendered with
    | implies left right => exact congr_two NamedFOF.Formula.implies (leftIH ground.1 left) (rightIH ground.2 right)

/-- Ground source formulas retain their exact names and term trees. The
    declaration encoding must come from the separately checked input decoder. -/
theorem source_row_identity {state : Frontend.State} {problem : TstpExport.NamedProblem}
    {source numeric fileLabel sourceName text}
    (functions : problem.functions = state.functions)
    (predicates : problem.predicates = state.predicates)
    (encoded : FOFFrontend.TableFormulaEncoding state source numeric)
    (ground : source.Ground)
    (rendered : FofTstpExport.sourceFormula problem fileLabel sourceName numeric = .ok text) :
    FormulaRowText text sourceName source (.function "file" [.atom fileLabel, .atom sourceName]) := by
  obtain ⟨printed, relation, grammar⟩ := source_formula_correspondence rendered
  have same := ground_formula_identity functions predicates encoded ground relation
  simpa only [same] using grammar

end Fang.FofTstpText
