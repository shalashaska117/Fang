/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotationGrammar

namespace Fang.TstpText

mutual
inductive WitnessMeaning (symbols : List Frontend.Symbol) : Fang.Term → Datum → Prop where
  | variable (index : Nat) :
      WitnessMeaning symbols (.var index) (.function "var" [.natural index])
  | application {index arguments named name}
      (symbol : SymbolText symbols index arguments.length name)
      (children : WitnessesMeaning symbols arguments named) :
      WitnessMeaning symbols (.app index arguments) (.function "fun" [.atom name, .list named])
inductive WitnessesMeaning (symbols : List Frontend.Symbol) :
    List Fang.Term → List Datum → Prop where
  | nil : WitnessesMeaning symbols [] []
  | cons {value named rest names} (head : WitnessMeaning symbols value named)
      (tail : WitnessesMeaning symbols rest names) :
      WitnessesMeaning symbols (value :: rest) (named :: names)
end

mutual
theorem witness_term_correspondence {symbols : List Frontend.Symbol} (value : Fang.Term)
    {text : String} (accepted : TstpExport.witnessTerm symbols value = .ok text) :
    ∃ named, WitnessMeaning symbols value named ∧ DataText text named := by
  cases value with
  | var index =>
    simp [TstpExport.witnessTerm] at accepted
    subst text
    refine ⟨.function "var" [.natural index], .variable index, ?_⟩
    exact (function_one "var" (by decide) (.natural (natural_spelling index))).spelling_eq
      (by string_shape)
  | app index arguments =>
    cases hs : TstpExport.symbol symbols index arguments.length with
    | error e => simp [TstpExport.witnessTerm, hs, bind, Except.bind] at accepted
    | ok name =>
      cases ht : TstpExport.witnessTerms symbols arguments with
      | error e => simp [TstpExport.witnessTerm, hs, ht, bind, Except.bind] at accepted
      | ok rendered =>
        have symbol := symbol_correspondence hs
        obtain ⟨names, meaning, grammar⟩ := witness_terms_correspondence arguments ht
        simp [TstpExport.witnessTerm, hs, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst text
        refine ⟨.function "fun" [.atom name, .list names], .application symbol meaning, ?_⟩
        exact (function_two "fun" (by decide)
          (.atom (.lower symbol.grammar)) (.list grammar)).spelling_eq (by string_shape)
termination_by sizeOf value

theorem witness_terms_correspondence {symbols : List Frontend.Symbol} (values : List Fang.Term)
    {texts : List String} (accepted : TstpExport.witnessTerms symbols values = .ok texts) :
    ∃ named, WitnessesMeaning symbols values named ∧ DataTexts texts named := by
  cases values with
  | nil =>
    simp [TstpExport.witnessTerms] at accepted
    subst texts
    exact ⟨[], .nil, .nil⟩
  | cons first rest =>
    cases hf : TstpExport.witnessTerm symbols first with
    | error e => simp [TstpExport.witnessTerms, hf, bind, Except.bind] at accepted
    | ok text =>
      cases ht : TstpExport.witnessTerms symbols rest with
      | error e => simp [TstpExport.witnessTerms, hf, ht, bind, Except.bind] at accepted
      | ok tail =>
        simp [TstpExport.witnessTerms, hf, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst texts
        obtain ⟨name, meaning, grammar⟩ := witness_term_correspondence first hf
        obtain ⟨names, meanings, grammars⟩ := witness_terms_correspondence rest ht
        exact ⟨name :: names, .cons meaning meanings, .cons grammar grammars⟩
termination_by sizeOf values
end

inductive BindingMeaning (symbols : List Frontend.Symbol) : Nat × Fang.Term → Datum → Prop where
  | binding {index value named} (term : WitnessMeaning symbols value named) :
      BindingMeaning symbols (index, value) (.function "binding" [.natural index, named])

abbrev BindingsMeaning (symbols : List Frontend.Symbol) (substitution : Subst)
    (bindings : List Datum) : Prop :=
  Source.RelatedLists (BindingMeaning symbols) substitution bindings

theorem binding_list_correspondence {problem : TstpExport.NamedProblem} (substitution : Subst)
    {texts : List String}
    (accepted : (substitution.mapM fun (index, value) => do
      pure (s!"binding({index}," ++ (← TstpExport.witnessTerm problem.functions value) ++ ")")) =
      (Except.ok texts : Except String (List String))) :
    ∃ named, BindingsMeaning problem.functions substitution named ∧ DataTexts texts named := by
  induction substitution generalizing texts with
  | nil =>
    simp [pure, Except.pure] at accepted
    subst texts
    exact ⟨[], .nil, .nil⟩
  | cons first rest ih =>
    obtain ⟨index, value⟩ := first
    cases hf : TstpExport.witnessTerm problem.functions value with
    | error e => simp [List.mapM_cons, hf, bind, Except.bind] at accepted
    | ok text =>
      cases ht : (rest.mapM fun (index, value) => do
          pure (s!"binding({index}," ++ (← TstpExport.witnessTerm problem.functions value) ++ ")")) with
      | error e =>
        simp [bind, Except.bind, pure, Except.pure] at ht
        simp [List.mapM_cons, hf, ht, bind, Except.bind, pure, Except.pure] at accepted
      | ok tail =>
        simp [bind, Except.bind, pure, Except.pure] at ht
        simp [List.mapM_cons, hf, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst texts
        obtain ⟨name, meaning, grammar⟩ := witness_term_correspondence value hf
        obtain ⟨names, meanings, grammars⟩ := ih ht
        refine ⟨.function "binding" [.natural index, name] :: names,
          .cons (.binding meaning) meanings, .cons ?_ grammars⟩
        exact (function_two "binding" (by decide)
          (.natural (natural_spelling index)) grammar).spelling_eq (by string_shape)

theorem witness_correspondence {problem : TstpExport.NamedProblem} (substitution : Subst)
    {text : String} (accepted : TstpExport.witness problem substitution = .ok text) :
    ∃ bindings, BindingsMeaning problem.functions substitution bindings ∧
      DataText text (.function "fang_substitution" [.list bindings]) := by
  cases ht : (substitution.mapM fun (index, value) => do
      pure (s!"binding({index}," ++ (← TstpExport.witnessTerm problem.functions value) ++ ")")) with
  | error e =>
    simp [bind, Except.bind, pure, Except.pure] at ht
    simp [TstpExport.witness, ht, bind, Except.bind, pure, Except.pure] at accepted
  | ok texts =>
    simp [bind, Except.bind, pure, Except.pure] at ht
    simp [TstpExport.witness, ht, bind, Except.bind, pure, Except.pure] at accepted
    subst text
    obtain ⟨bindings, meaning, grammar⟩ := binding_list_correspondence substitution ht
    refine ⟨bindings, meaning, ?_⟩
    exact (function_one "fang_substitution" (by decide) (.list grammar)).spelling_eq
      (by string_shape)

end Fang.TstpText
