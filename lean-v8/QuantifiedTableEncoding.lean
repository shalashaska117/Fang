/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual decoder-table witnesses, without a global variable-table bijection. -/
import QuantifiedScope
import Fang.FrontendSymbolExtension

namespace Fang.QuantifiedFrontend
open Frontend

inductive TableFormulaEncoding (state : State) : NamedQuantified.Formula → QuantifiedFOF.Formula → Prop where
  | atom (name : String) (id : Nat) (args : List Source.Term) (encoded : List Fang.Term)
      (found : symbolIndex name state.predicates 0 = some id)
      (arity : (state.predicates[id]?).map Symbol.arity = some (some args.length))
      (terms : TableTermsEncoding state args encoded) :
      TableFormulaEncoding state (.atom name args) (.atom ⟨id, encoded⟩)
  | truth : TableFormulaEncoding state .truth .truth
  | falsity : TableFormulaEncoding state .falsity .falsity
  | neg {body output} (child : TableFormulaEncoding state body output) :
      TableFormulaEncoding state (.neg body) (.neg output)
  | conj {left right l r} (first : TableFormulaEncoding state left l)
      (second : TableFormulaEncoding state right r) :
      TableFormulaEncoding state (.conj left right) (.conj l r)
  | disj {left right l r} (first : TableFormulaEncoding state left l)
      (second : TableFormulaEncoding state right r) :
      TableFormulaEncoding state (.disj left right) (.disj l r)
  | implies {left right l r} (first : TableFormulaEncoding state left l)
      (second : TableFormulaEncoding state right r) :
      TableFormulaEncoding state (.implies left right) (.implies l r)
  | all (name : String) (id : Nat) {body output}
      (found : namedIndex name state.variables 0 = some id)
      (child : TableFormulaEncoding state body output) :
      TableFormulaEncoding state (.all name body) (.all id output)
  | ex (name : String) (id : Nat) {body output}
      (found : namedIndex name state.variables 0 = some id)
      (child : TableFormulaEncoding state body output) :
      TableFormulaEncoding state (.ex name body) (.ex id output)

theorem TableFormulaEncoding.toSource {state named encoded}
    (encoding : TableFormulaEncoding state named encoded) :
    NamedQuantified.Encoding (signatureFrom state) (symbolsFrom state)
      (variablesFrom state.variables) named encoded := by
  induction encoding with
  | atom name id args encoded found arity terms =>
    obtain ⟨assigned, recovered⟩ := table_found found
    have roundtrip : (symbolsFrom state).predicateName ((symbolsFrom state).predicateId name) = name := by
      change tableName state.predicates (tableId state.predicates name) = name
      rw [assigned, recovered]
    have checked : (signatureFrom state).predicateArity name = some args.length :=
      table_arity_of_found found arity
    simpa only [symbolsFrom, assigned] using
      NamedQuantified.Encoding.atom name args encoded roundtrip checked terms.toSource
  | truth => exact .truth
  | falsity => exact .falsity
  | neg child ih => exact .neg ih
  | conj first second ihl ihr => exact .conj ihl ihr
  | disj first second ihl ihr => exact .disj ihl ihr
  | implies first second ihl ihr => exact .implies ihl ihr
  | all name id found child ih =>
    obtain ⟨assigned, recovered⟩ := variablesFrom_found found
    have roundtrip : (variablesFrom state.variables).name ((variablesFrom state.variables).id name) = name := by
      rw [assigned, recovered]
    simpa only [assigned] using NamedQuantified.Encoding.all name roundtrip ih
  | ex name id found child ih =>
    obtain ⟨assigned, recovered⟩ := variablesFrom_found found
    have roundtrip : (variablesFrom state.variables).name ((variablesFrom state.variables).id name) = name := by
      rw [assigned, recovered]
    simpa only [assigned] using NamedQuantified.Encoding.ex name roundtrip ih

theorem TableFormulaEncoding.extend {before after named encoded}
    (encoding : TableFormulaEncoding before named encoded) (extension : TableExtension before after) :
    TableFormulaEncoding after named encoded := by
  induction encoding with
  | atom name id args encoded found arity terms =>
    exact .atom name id args encoded (extension.symbols true name id found)
      (extension.arities true id args.length arity) (terms.extend extension)
  | truth => exact .truth
  | falsity => exact .falsity
  | neg child ih => exact .neg ih
  | conj first second ihl ihr => exact .conj ihl ihr
  | disj first second ihl ihr => exact .disj ihl ihr
  | implies first second ihl ihr => exact .implies ihl ihr
  | all name id found child ih => exact .all name id (extension.variables name id found) ih
  | ex name id found child ih => exact .ex name id (extension.variables name id found) ih

theorem TableFormulaEncoding.freeze_variables {before after named encoded}
    (encoding : TableFormulaEncoding before named encoded) (extension : SymbolExtension before after) :
    TableFormulaEncoding { after with variables := before.variables } named encoded :=
  encoding.extend (extension.withVariables before.variables)

/-- The current lexical scope names and IDs are related by actual successful
    lookups. Lists may repeat names/IDs to represent lexical shadowing. -/
inductive BoundEncoding (state : State) : List String → List Nat → Prop where
  | nil : BoundEncoding state [] []
  | cons {name id names ids} (found : namedIndex name state.variables 0 = some id)
      (tail : BoundEncoding state names ids) : BoundEncoding state (name :: names) (id :: ids)

theorem BoundEncoding.ofRelated {state names ids}
    (related : Source.RelatedLists (fun name id => namedIndex name state.variables 0 = some id) names ids) :
    BoundEncoding state names ids := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

theorem BoundEncoding.toRelated {state names ids} (encoding : BoundEncoding state names ids) :
    Source.RelatedLists (fun name id => namedIndex name state.variables 0 = some id) names ids := by
  induction encoding with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

theorem BoundEncoding.extend {before after names ids}
    (encoding : BoundEncoding before names ids) (extension : TableExtension before after) :
    BoundEncoding after names ids := by
  induction encoding with
  | nil => exact .nil
  | cons found tail ih => exact .cons (extension.variables _ _ found) ih

theorem TableFormulaEncoding.bind {state named encoded names ids}
    (encoding : TableFormulaEncoding state named encoded) (universal : Bool)
    (bound : BoundEncoding state names ids) :
    TableFormulaEncoding state
      (names.foldr (fun name body => if universal then .all name body else .ex name body) named)
      (bindFormula universal ids encoded) := by
  induction bound with
  | nil => exact encoding
  | @cons name id names ids found tail ih =>
    cases universal with
    | false => exact .ex name id found ih
    | true => exact .all name id found ih

/-- First-occurrence lookup can repeat a spelling, but distinct represented
    spellings cannot share an ID. No global table uniqueness is assumed. -/
theorem namedIndex_id_eq_iff {state : State} {first second : String} {firstId secondId : Nat}
    (left : namedIndex first state.variables 0 = some firstId)
    (right : namedIndex second state.variables 0 = some secondId) :
    firstId = secondId ↔ first = second := by
  constructor
  · intro same
    obtain ⟨_, firstName⟩ := variablesFrom_found left
    obtain ⟨_, secondName⟩ := variablesFrom_found right
    exact firstName.symm.trans ((congrArg (variablesFrom state.variables).name same).trans secondName)
  · intro same
    subst second
    exact Option.some.inj (left.symm.trans right)

theorem BoundEncoding.mem_iff {state names ids name id}
    (encoding : BoundEncoding state names ids)
    (found : namedIndex name state.variables 0 = some id) : id ∈ ids ↔ name ∈ names := by
  induction encoding with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mem_cons, namedIndex_id_eq_iff found head, ih]

mutual
theorem tableTerm_within_iff {state named encoded names ids}
    (encoding : TableTermEncoding state named encoded) (bound : BoundEncoding state names ids) :
    QuantifiedFOF.TermWithin ids encoded ↔ NamedQuantified.TermWithin names named := by
  cases encoding with
  | var name id found =>
    simpa only [QuantifiedFOF.TermWithin, NamedQuantified.TermWithin] using bound.mem_iff found
  | app name id args encoded found arity children =>
    simpa only [QuantifiedFOF.TermWithin, NamedQuantified.TermWithin] using
      tableTerms_within_iff children bound

theorem tableTerms_within_iff {state named encoded names ids}
    (encoding : TableTermsEncoding state named encoded) (bound : BoundEncoding state names ids) :
    (∀ term ∈ encoded, QuantifiedFOF.TermWithin ids term) ↔
      (∀ term ∈ named, NamedQuantified.TermWithin names term) := by
  cases encoding with
  | nil => simp
  | cons head tail =>
    simp only [List.forall_mem_cons, tableTerm_within_iff head bound, tableTerms_within_iff tail bound]
end

theorem TableFormulaEncoding.within_iff {state named encoded names ids}
    (encoding : TableFormulaEncoding state named encoded) (bound : BoundEncoding state names ids) :
    encoded.Within ids ↔ named.Within names := by
  induction encoding generalizing names ids with
  | atom name id args encoded found arity terms => exact tableTerms_within_iff terms bound
  | truth => rfl
  | falsity => rfl
  | neg child ih => exact ih bound
  | conj first second ihl ihr => exact and_congr (ihl bound) (ihr bound)
  | disj first second ihl ihr => exact and_congr (ihl bound) (ihr bound)
  | implies first second ihl ihr => exact and_congr (ihl bound) (ihr bound)
  | all name id found child ih => exact ih (.cons found bound)
  | ex name id found child ih => exact ih (.cons found bound)

theorem TableFormulaEncoding.closed_iff {state named encoded}
    (encoding : TableFormulaEncoding state named encoded) : encoded.Within [] ↔ named.Within [] :=
  encoding.within_iff .nil

/-- Successful numeric closure testing certifies closure of the same named AST,
    including binders whose names were unused, repeated or shadowed. -/
theorem TableFormulaEncoding.closed_of_formulaWithin {state named encoded}
    (encoding : TableFormulaEncoding state named encoded) (closed : formulaWithin [] encoded = true) :
    named.Within [] := encoding.closed_iff.mp ((formulaWithin_correct [] encoded).mp closed)

theorem TableFormulaEncoding.holds_toNumeric {state named encoded}
    (encoding : TableFormulaEncoding state named encoded)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    encoded.Holds (model.toNumeric (symbolsFrom state)) valuation ↔
      named.Holds model (fun name => valuation ((variablesFrom state.variables).id name)) :=
  encoding.toSource.holds_toNumeric model valuation

theorem TableFormulaEncoding.holds_toNamed {state named encoded}
    (encoding : TableFormulaEncoding state named encoded)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    named.Holds (Source.numericToNamed model (symbolsFrom state)) valuation ↔
      encoded.Holds model (fun id => valuation ((variablesFrom state.variables).name id)) :=
  encoding.toSource.holds_toNamed model valuation

end Fang.QuantifiedFrontend
