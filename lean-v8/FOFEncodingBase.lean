/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FOFInput
import Fang.FrontendSymbolExtension

namespace Fang.FOFFrontend
open Frontend

/- These relations specify names represented by the actual decoder tables.
   They do not define another parser or assume that arbitrary table entries exist. -/
inductive TableFormulaEncoding (state : State) : NamedFOF.Formula → GroundFOF.Formula → Prop where
  | atom (name : String) (id : Nat) (args : List Source.Term) (encoded : List Fang.Term)
      (found : symbolIndex name state.predicates 0 = some id)
      (arity : (state.predicates[id]?).map Symbol.arity = some (some args.length))
      (terms : TableTermsEncoding state args encoded) :
      TableFormulaEncoding state (.atom name args) (.atom ⟨id, encoded⟩)
  | truth : TableFormulaEncoding state .truth .truth
  | falsity : TableFormulaEncoding state .falsity .falsity
  | neg {a encoded} (child : TableFormulaEncoding state a encoded) :
      TableFormulaEncoding state (.neg a) (.neg encoded)
  | conj {a b left right} (first : TableFormulaEncoding state a left)
      (second : TableFormulaEncoding state b right) :
      TableFormulaEncoding state (.conj a b) (.conj left right)
  | disj {a b left right} (first : TableFormulaEncoding state a left)
      (second : TableFormulaEncoding state b right) :
      TableFormulaEncoding state (.disj a b) (.disj left right)
  | implies {a b left right} (first : TableFormulaEncoding state a left)
      (second : TableFormulaEncoding state b right) :
      TableFormulaEncoding state (.implies a b) (.implies left right)

theorem TableFormulaEncoding.toSource {state named encoded}
    (encoding : TableFormulaEncoding state named encoded) :
    NamedFOF.Encoding (signatureFrom state) (symbolsFrom state)
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
        NamedFOF.Encoding.atom name args encoded roundtrip checked terms.toSource
  | truth => exact .truth
  | falsity => exact .falsity
  | neg child ih => exact .neg ih
  | conj first second ih₁ ih₂ => exact .conj ih₁ ih₂
  | disj first second ih₁ ih₂ => exact .disj ih₁ ih₂
  | implies first second ih₁ ih₂ => exact .implies ih₁ ih₂

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
  | conj first second ih₁ ih₂ => exact .conj ih₁ ih₂
  | disj first second ih₁ ih₂ => exact .disj ih₁ ih₂
  | implies first second ih₁ ih₂ => exact .implies ih₁ ih₂

theorem TableFormulaEncoding.freeze_variables {before after named encoded}
    (encoding : TableFormulaEncoding before named encoded) (extension : SymbolExtension before after) :
    TableFormulaEncoding { after with variables := before.variables } named encoded :=
  encoding.extend (extension.withVariables before.variables)

mutual
theorem tableTerm_ground_iff {state named encoded}
    (encoding : TableTermEncoding state named encoded) :
    GroundFOF.GroundTerm encoded ↔ NamedFOF.GroundTerm named := by
  cases encoding with
  | var name id found => simp only [GroundFOF.GroundTerm, NamedFOF.GroundTerm]
  | app name id args encoded found arity children =>
      simp only [GroundFOF.GroundTerm, NamedFOF.GroundTerm]
      exact tableTerms_ground_iff children
theorem tableTerms_ground_iff {state named encoded}
    (encoding : TableTermsEncoding state named encoded) :
    (∀ t ∈ encoded, GroundFOF.GroundTerm t) ↔ (∀ t ∈ named, NamedFOF.GroundTerm t) := by
  cases encoding with
  | nil => simp
  | cons head tail =>
      simp only [List.forall_mem_cons, tableTerm_ground_iff head, tableTerms_ground_iff tail]
end

theorem TableFormulaEncoding.ground_iff {state named encoded}
    (encoding : TableFormulaEncoding state named encoded) : encoded.Ground ↔ named.Ground := by
  induction encoding with
  | atom name id args encoded found arity terms => exact tableTerms_ground_iff terms
  | truth => rfl
  | falsity => rfl
  | neg child ih => exact ih
  | conj first second ih₁ ih₂ => exact and_congr ih₁ ih₂
  | disj first second ih₁ ih₂ => exact and_congr ih₁ ih₂
  | implies first second ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem TableFormulaEncoding.holds_toNumeric {state named encoded}
    (encoding : TableFormulaEncoding state named encoded)
    {D : Type} (M : Source.Interpretation D) (ρ : Nat → D) :
    encoded.Holds (M.toNumeric (symbolsFrom state)) ρ ↔
      named.Holds M (fun n => ρ ((variablesFrom state.variables).id n)) :=
  encoding.toSource.holds_toNumeric M ρ

theorem TableFormulaEncoding.holds_toNamed {state named encoded}
    (encoding : TableFormulaEncoding state named encoded)
    {D : Type} (M : Fang.Interpretation D) (ρ : String → D) :
    named.Holds (Source.numericToNamed M (symbolsFrom state)) ρ ↔
      encoded.Holds M (fun n => ρ ((variablesFrom state.variables).name n)) :=
  encoding.toSource.holds_toNamed M ρ

end Fang.FOFFrontend
