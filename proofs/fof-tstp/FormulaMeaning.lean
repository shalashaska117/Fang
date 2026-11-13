/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.FormulaText

namespace Fang.FofTstpText
open TstpText

/-- Same table interpretation as the CNF text proof; no source parser premise. -/
def tableModel {D : Type} (problem : TstpExport.NamedProblem)
    (model : Source.Interpretation D) : Fang.Interpretation D where
  function index := model.function (Frontend.tableName problem.functions index)
  predicate index := model.predicate (Frontend.tableName problem.predicates index)

theorem symbol_name {symbols index arity name} (symbol : SymbolText symbols index arity name) :
    Frontend.tableName symbols index = name := by
  obtain ⟨value, found, same, _⟩ := symbol.entry
  simp [Frontend.tableName, found, same]

mutual
theorem term_meaning {problem : TstpExport.NamedProblem} {value named}
    (relation : NamedTerm problem.functions value named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.eval model valuation =
      value.eval (tableModel problem model) (fun index => valuation s!"X{index}") := by
  cases relation with
  | «variable» index => simp only [Source.Term.eval, Fang.Term.eval]
  | application symbol children =>
    simp only [Source.Term.eval, Fang.Term.eval, tableModel]
    rw [symbol_name symbol]
    exact congrArg _ (terms_meaning children model valuation)
termination_by sizeOf value

theorem terms_meaning {problem : TstpExport.NamedProblem} {values named}
    (relation : NamedTerms problem.functions values named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.map (Source.Term.eval model valuation) =
      values.map (Fang.Term.eval (tableModel problem model) (fun index => valuation s!"X{index}")) := by
  cases relation with
  | nil => rfl
  | cons head tail =>
    simp only [List.map_cons, term_meaning head model valuation, terms_meaning tail model valuation]
termination_by sizeOf values
end

theorem NamedFormula.holds {problem : TstpExport.NamedProblem} {value named}
    (relation : NamedFormula problem value named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.Holds model valuation ↔
      value.Holds (tableModel problem model) (fun index => valuation s!"X{index}") := by
  induction relation with
  | atom symbol children =>
    simp only [NamedFOF.Formula.Holds, GroundFOF.Formula.Holds, Atom.Holds, tableModel]
    rw [symbol_name symbol, terms_meaning children model valuation]
    rfl
  | truth => rfl
  | falsity => rfl
  | neg child ih => exact not_congr ih
  | conj left right leftIH rightIH => exact and_congr leftIH rightIH
  | disj left right leftIH rightIH => exact or_congr leftIH rightIH
  | implies left right leftIH rightIH => exact imp_congr leftIH rightIH

theorem printed_formula_meaning {problem : TstpExport.NamedProblem}
    {value : GroundFOF.Formula} {text : String}
    (printed : FofTstpExport.formula problem value = .ok text) :
    ∃ named, FormulaText text named ∧ ∀ (D : Type) (model : Source.Interpretation D)
      (valuation : String → D), named.Holds model valuation ↔
        value.Holds (tableModel problem model) (fun index => valuation s!"X{index}") := by
  obtain ⟨named, relation, grammar⟩ := formula_correspondence value printed
  exact ⟨named, grammar, fun _ model valuation => relation.holds model valuation⟩

end Fang.FofTstpText
