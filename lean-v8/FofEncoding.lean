/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofSyntax

namespace Fang.TptpCandidate.FullFof

structure ModelAgreement {D : Type} (functions predicates : Arity.Table)
    (named : Source.Interpretation D) (numeric : Interpretation D) : Prop where
  function : ∀ name args, (name, args.length) ∈ functions →
    numeric.function (Arity.id functions (name, args.length)) args = named.function name args
  predicate : ∀ name args, (name, args.length) ∈ predicates →
    (numeric.predicate (Arity.id predicates (name, args.length)) args ↔ named.predicate name args)
  equality : ∀ left right, numeric.predicate predicates.length [left, right] ↔ left = right

theorem model_toNumeric {D : Type} (model : Source.Interpretation D)
    (functions predicates : Arity.Table) : ModelAgreement functions predicates model
      (toNumeric model functions predicates) := by
  constructor
  · intro name args member
    simp [toNumeric, reserve, Arity.toNumeric, Arity.id_roundtrip member]
  · intro name args member
    have below := Arity.id_bound member
    simp [toNumeric, reserve, Arity.toNumeric, Arity.id_roundtrip member, Nat.ne_of_lt below]
  · intro left right
    simp [toNumeric, reserve]

theorem model_toNamed {D : Type} (model : Interpretation D)
    (functions predicates : Arity.Table) : ModelAgreement functions predicates
      (Arity.toNamed model functions predicates) (reserve predicates.length model) := by
  constructor
  · intro name args _; rfl
  · intro name args member
    have below := Arity.id_bound member
    simp [Arity.toNamed, reserve, Nat.ne_of_lt below]
  · intro left right
    simp [reserve]

theorem term_eval (term : Source.Term) (functions predicates : Arity.Table)
    (variables : Source.Variables) (functionsCovered : Arity.TermCovered functions term)
    (variablesCovered : Arity.VariablesCovered variables term)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric)
    {namedValuation : String → D} {numericValuation : Nat → D}
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    (Arity.encodeTerm functions variables term).eval numeric numericValuation =
      term.eval named namedValuation := by
  cases term with
  | var name =>
    simpa only [Arity.encodeTerm, Term.eval, Source.Term.eval] using
      (values name (variablesCovered name (by simp [Arity.termVariables]))).symm
  | app name args =>
    have root : (name, args.length) ∈ functions := functionsCovered _ (by simp [Arity.termFunctions])
    simp only [Arity.encodeTerm, Term.eval, Source.Term.eval, List.map_map, Function.comp_def]
    have children : args.map (fun child => (Arity.encodeTerm functions variables child).eval numeric numericValuation) =
        args.map (fun child => child.eval named namedValuation) := by
      apply List.map_congr_left
      intro child member
      apply term_eval child functions predicates variables ?_ ?_ models values
      · intro symbol present
        apply functionsCovered
        simpa only [Arity.termFunctions] using
          (List.mem_cons_of_mem (name, args.length) (List.mem_flatMap.mpr ⟨child, member, present⟩))
      · intro variableName present
        apply variablesCovered variableName
        simpa only [Arity.termVariables] using (List.mem_flatMap.mpr ⟨child, member, present⟩)
    rw [children]
    simpa only [List.length_map] using models.function name (args.map (Source.Term.eval named namedValuation))
      (by simpa only [List.length_map] using root)
termination_by sizeOf term

structure Formula.Covered (functions predicates : Arity.Table) (variables : Source.Variables)
    (formula : Formula) : Prop where
  functions : ∀ symbol ∈ formula.functions, symbol ∈ functions
  predicates : ∀ symbol ∈ formula.predicates, symbol ∈ predicates
  variables : ∀ name ∈ formula.variableNames, variables.name (variables.id name) = name

theorem encode_holds {formula : Formula} {functions predicates : Arity.Table}
    {variables : Source.Variables} (covered : formula.Covered functions predicates variables)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric)
    (namedValuation : String → D) (numericValuation : Nat → D)
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    (formula.encode functions predicates variables).Holds numeric numericValuation ↔
      formula.Holds named namedValuation := by
  induction formula generalizing namedValuation numericValuation with
  | atom name args =>
    have children : (args.map (Arity.encodeTerm functions variables)).map (Term.eval numeric numericValuation) =
        args.map (Source.Term.eval named namedValuation) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro child member
      apply term_eval child functions predicates variables ?_ ?_ models values
      · intro symbol present
        exact covered.functions symbol (List.mem_flatMap.mpr ⟨child, member, present⟩)
      · intro variableName present
        exact covered.variables variableName (List.mem_flatMap.mpr ⟨child, member, present⟩)
    simp only [Formula.encode, QuantifiedFOF.Formula.Holds, Atom.Holds, Formula.Holds]
    rw [children]
    simpa only [List.length_map] using models.predicate name (args.map (Source.Term.eval named namedValuation))
      (by simpa [Formula.predicates] using covered.predicates (name, args.length) (by simp [Formula.predicates]))
  | equal left right =>
    have l := term_eval left functions predicates variables
      (fun symbol member => covered.functions symbol (List.mem_append_left _ member))
      (fun name member => covered.variables name (List.mem_append_left _ member)) models values
    have r := term_eval right functions predicates variables
      (fun symbol member => covered.functions symbol (List.mem_append_right _ member))
      (fun name member => covered.variables name (List.mem_append_right _ member)) models values
    simpa only [Formula.encode, QuantifiedFOF.Formula.Holds, Atom.Holds, List.map_cons,
      List.map_nil, Formula.Holds, l, r] using models.equality (left.eval named namedValuation) (right.eval named namedValuation)
  | truth | falsity => rfl
  | neg body ih =>
    exact not_congr (ih ⟨covered.functions, covered.predicates, covered.variables⟩ _ _ values)
  | pair operator left right ihl ihr =>
    have lc : left.Covered functions predicates variables := ⟨
      fun s h => covered.functions s (List.mem_append_left _ h),
      fun s h => covered.predicates s (List.mem_append_left _ h),
      fun s h => covered.variables s (List.mem_append_left _ h)⟩
    have rc : right.Covered functions predicates variables := ⟨
      fun s h => covered.functions s (List.mem_append_right _ h),
      fun s h => covered.predicates s (List.mem_append_right _ h),
      fun s h => covered.variables s (List.mem_append_right _ h)⟩
    rw [Formula.encode, binary_holds]
    have l := ihl lc namedValuation numericValuation values
    have r := ihr rc namedValuation numericValuation values
    cases operator <;> simp only [Formula.Holds, Binary.meaning] <;> simp_all
  | all name body ih =>
    have bodyCovered : body.Covered functions predicates variables := ⟨covered.functions, covered.predicates,
      fun s h => covered.variables s (List.mem_cons_of_mem name h)⟩
    have represented := covered.variables name (by simp [Formula.variableNames])
    exact forall_congr' (fun value => ih bodyCovered _ _ (values.update name represented value))
  | ex name body ih =>
    have bodyCovered : body.Covered functions predicates variables := ⟨covered.functions, covered.predicates,
      fun s h => covered.variables s (List.mem_cons_of_mem name h)⟩
    have represented := covered.variables name (by simp [Formula.variableNames])
    exact exists_congr (fun value => ih bodyCovered _ _ (values.update name represented value))

def functionTable (problem : List Formula) : Arity.Table :=
  Arity.collect [] (problem.flatMap Formula.functions)

def predicateTable (problem : List Formula) : Arity.Table :=
  Arity.collect [] (problem.flatMap Formula.predicates)

theorem collected_covered {problem : List Formula} {formula : Formula} (member : formula ∈ problem) :
    formula.Covered (functionTable problem) (predicateTable problem) formula.variables := by
  constructor
  · intro symbol present
    exact (Arity.collect_mem [] _ _).mpr (Or.inr (List.mem_flatMap.mpr ⟨formula, member, present⟩))
  · intro symbol present
    exact (Arity.collect_mem [] _ _).mpr (Or.inr (List.mem_flatMap.mpr ⟨formula, member, present⟩))
  · intro name present
    exact variable_roundtrip formula present

def Models {D : Type} (problem : List Formula) (model : Source.Interpretation D) : Prop :=
  ∀ formula ∈ problem, ∀ valuation, formula.Holds model valuation

def EncodedModels {D : Type} (problem : List Formula) (model : Interpretation D) : Prop :=
  ∀ formula ∈ problem, ∀ valuation,
    (formula.encode (functionTable problem) (predicateTable problem) formula.variables).Holds
      (reserve (predicateTable problem).length model) valuation

theorem models_toNumeric {problem : List Formula} {D : Type} (model : Source.Interpretation D)
    (models : Models problem model) :
    EncodedModels problem (Arity.toNumeric model (functionTable problem) (predicateTable problem)) := by
  intro formula member valuation
  apply (encode_holds (collected_covered member) (model_toNumeric model _ _)
    (fun name => valuation (formula.variables.id name)) valuation (fun _ _ => rfl)).mpr
  exact models formula member _

theorem models_toNamed {problem : List Formula} {D : Type} (model : Interpretation D)
    (models : EncodedModels problem model) :
    Models problem (Arity.toNamed model (functionTable problem) (predicateTable problem)) := by
  intro formula member valuation
  apply (encode_holds (collected_covered member) (model_toNamed model _ _)
    valuation (fun id => valuation (formula.variables.name id)) ?_).mp
  · exact models formula member _
  · intro name represented
    simp only [represented]

def Satisfiable (problem : List Formula) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), Models problem model

def EncodedSatisfiable (problem : List Formula) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Interpretation D), EncodedModels problem model

theorem satisfiable_iff (problem : List Formula) : Satisfiable problem ↔ EncodedSatisfiable problem := by
  constructor
  · rintro ⟨domain, nonempty, model, models⟩
    exact ⟨domain, nonempty, Arity.toNumeric model _ _, models_toNumeric model models⟩
  · rintro ⟨domain, nonempty, model, models⟩
    exact ⟨domain, nonempty, Arity.toNamed model _ _, models_toNamed model models⟩

end Fang.TptpCandidate.FullFof
