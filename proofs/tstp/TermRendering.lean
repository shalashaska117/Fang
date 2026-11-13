/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import TstpExport
import Fang.FrontendTokenView

namespace Fang.TstpText

/-- Declarative symbol lookup: the printed name is the source table entry at
the exact numeric ID, with the declared arity and the independent lower-word
byte grammar. No uniqueness assumption about an arbitrary table is hidden. -/
structure SymbolText (symbols : List Frontend.Symbol) (index arity : Nat)
    (name : String) : Prop where
  entry : ∃ value, symbols[index]? = some value ∧ value.name = name ∧ value.arity = some arity
  grammar : Source.Grammar.LowerName name

theorem symbol_correspondence {symbols : List Frontend.Symbol} {index arity : Nat}
    {name : String} (accepted : TstpExport.symbol symbols index arity = .ok name) :
    SymbolText symbols index arity name := by
  cases found : symbols[index]? with
  | none => simp [TstpExport.symbol, found, throw] at accepted
  | some value =>
    by_cases lower : Frontend.lowerName value.name = true
    · by_cases arityOk : value.arity = some arity
      · simp [TstpExport.symbol, found, lower, arityOk, pure, Except.pure] at accepted
        subst name
        exact ⟨⟨value, found, rfl, arityOk⟩,
          (Frontend.lowerName_iff value.name (Frontend.lowerName_ascii lower)).mp lower⟩
      · simp [TstpExport.symbol, found, lower, arityOk, throw, bind, Except.bind] at accepted
    · simp [TstpExport.symbol, found, lower, throw, bind, Except.bind] at accepted

/- This relation fixes recursive tree shape, table IDs, child order and exact
punctuation. The variable spelling uses Lean's Nat formatter. A separate proof
that this formatter gives an injective TPTP variable token is still required,
as is a complete byte-parser round trip for compound terms. -/
mutual
inductive TermText (symbols : List Frontend.Symbol) : Term → String → Prop where
  | variable (index : Nat) : TermText symbols (.var index) s!"X{index}"
  | constant {index name} (symbol : SymbolText symbols index 0 name) :
      TermText symbols (.app index []) name
  | application {index arguments rendered name}
      (nonempty : arguments ≠ [])
      (symbol : SymbolText symbols index arguments.length name)
      (children : TermsText symbols arguments rendered) :
      TermText symbols (.app index arguments)
        (name ++ "(" ++ String.intercalate "," rendered ++ ")")
inductive TermsText (symbols : List Frontend.Symbol) : List Term → List String → Prop where
  | nil : TermsText symbols [] []
  | cons {term text rest texts} (head : TermText symbols term text)
      (tail : TermsText symbols rest texts) :
      TermsText symbols (term :: rest) (text :: texts)
end

theorem TermsText.length {symbols terms rendered} (h : TermsText symbols terms rendered) :
    rendered.length = terms.length := by
  cases h with
  | nil => rfl
  | cons _ tail => simpa using congrArg Nat.succ tail.length
termination_by terms

mutual
theorem term_correspondence {symbols : List Frontend.Symbol} (value : Term) {text : String}
    (accepted : TstpExport.term symbols value = .ok text) : TermText symbols value text := by
  cases value with
  | var index =>
    simp [TstpExport.term] at accepted
    subst text
    exact .variable index
  | app index arguments =>
    cases hs : TstpExport.symbol symbols index arguments.length with
    | error e => simp [TstpExport.term, hs, bind, Except.bind] at accepted
    | ok name =>
      cases ht : TstpExport.terms symbols arguments with
      | error e => simp [TstpExport.term, hs, ht, bind, Except.bind] at accepted
      | ok rendered =>
        have symbol := symbol_correspondence hs
        have children := terms_correspondence arguments ht
        simp [TstpExport.term, hs, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst text
        cases arguments with
        | nil => simpa using TermText.constant symbol
        | cons first rest => simpa using TermText.application (by simp) symbol children
termination_by sizeOf value

theorem terms_correspondence {symbols : List Frontend.Symbol} (values : List Term)
    {texts : List String} (accepted : TstpExport.terms symbols values = .ok texts) :
    TermsText symbols values texts := by
  cases values with
  | nil =>
    simp [TstpExport.terms] at accepted
    subst texts
    exact .nil
  | cons first rest =>
    cases hf : TstpExport.term symbols first with
    | error e => simp [TstpExport.terms, hf, bind, Except.bind] at accepted
    | ok text =>
      cases ht : TstpExport.terms symbols rest with
      | error e => simp [TstpExport.terms, hf, ht, bind, Except.bind] at accepted
      | ok tail =>
        simp [TstpExport.terms, hf, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst texts
        exact .cons (term_correspondence first hf) (terms_correspondence rest ht)
termination_by sizeOf values
end

inductive AtomText (problem : TstpExport.NamedProblem) : Atom → String → Prop where
  | nullary {predicate name} (symbol : SymbolText problem.predicates predicate 0 name) :
      AtomText problem ⟨predicate, []⟩ name
  | application {predicate arguments rendered name}
      (nonempty : arguments ≠ [])
      (symbol : SymbolText problem.predicates predicate arguments.length name)
      (children : TermsText problem.functions arguments rendered) :
      AtomText problem ⟨predicate, arguments⟩
        (name ++ "(" ++ String.intercalate "," rendered ++ ")")

inductive LiteralText (problem : TstpExport.NamedProblem) : Literal → String → Prop where
  | positive {atom text} (body : AtomText problem atom text) :
      LiteralText problem ⟨true, atom⟩ text
  | negative {atom text} (body : AtomText problem atom text) :
      LiteralText problem ⟨false, atom⟩ ("~" ++ text)

theorem literal_correspondence {problem : TstpExport.NamedProblem} (value : Literal)
    {text : String} (accepted : TstpExport.literal problem value = .ok text) :
    LiteralText problem value text := by
  cases value with
  | mk positive atom =>
    cases atom with
    | mk predicate arguments =>
      cases hs : TstpExport.symbol problem.predicates predicate arguments.length with
      | error e => simp [TstpExport.literal, hs, bind, Except.bind] at accepted
      | ok name =>
        cases ht : TstpExport.terms problem.functions arguments with
        | error e => simp [TstpExport.literal, hs, ht, bind, Except.bind] at accepted
        | ok rendered =>
          have symbol := symbol_correspondence hs
          have children := terms_correspondence arguments ht
          have body : AtomText problem ⟨predicate, arguments⟩
              (if rendered.isEmpty then name else
                name ++ "(" ++ String.intercalate "," rendered ++ ")") := by
            cases arguments with
            | nil =>
              have length := children.length
              have empty : rendered = [] := by cases rendered <;> simp_all
              simp [empty]
              exact .nullary symbol
            | cons first rest =>
              have nonempty : rendered ≠ [] := by
                intro empty
                have length := children.length
                simp [empty] at length
              simpa [nonempty] using AtomText.application (by simp) symbol children
          simp [TstpExport.literal, hs, ht, bind, Except.bind, pure, Except.pure] at accepted
          subst text
          cases positive
          · simpa using LiteralText.negative body
          · simpa using LiteralText.positive body

end Fang.TstpText
