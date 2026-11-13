/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import LiteralParsing

namespace Fang.TstpText

open Source.Grammar

@[simp] theorem spelling_disjoin : spelling " | " = [32, 124, 32] := rfl

abbrev NamedClause (problem : TstpExport.NamedProblem) (value : Fang.Clause)
    (named : List Source.Literal) : Prop :=
  Source.RelatedLists (NamedLiteral problem) value named

inductive LiteralsText (problem : TstpExport.NamedProblem) : Fang.Clause → List String → Prop where
  | nil : LiteralsText problem [] []
  | cons {value text rest texts} (head : LiteralText problem value text)
      (tail : LiteralsText problem rest texts) :
      LiteralsText problem (value :: rest) (text :: texts)

theorem LiteralsText.length {problem values texts} (h : LiteralsText problem values texts) :
    texts.length = values.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem literals_correspondence {problem : TstpExport.NamedProblem} (values : Fang.Clause)
    {texts : List String} (accepted : values.mapM (TstpExport.literal problem) = .ok texts) :
    LiteralsText problem values texts := by
  induction values generalizing texts with
  | nil =>
    simp [pure, Except.pure] at accepted
    subst texts
    exact .nil
  | cons first rest ih =>
    cases hf : TstpExport.literal problem first with
    | error e => simp [List.mapM_cons, hf, bind, Except.bind] at accepted
    | ok text =>
      cases ht : rest.mapM (TstpExport.literal problem) with
      | error e => simp [List.mapM_cons, hf, ht, bind, Except.bind] at accepted
      | ok tail =>
        simp [List.mapM_cons, hf, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst texts
        exact .cons (literal_correspondence first hf) (ih ht)

theorem literals_tokens {problem : TstpExport.NamedProblem} {values : Fang.Clause} {texts : List String}
    (h : LiteralsText problem values texts) :
    ∃ names tokens, NamedClause problem values names ∧
      Tokenization (spelling (String.intercalate " | " texts)) tokens ∧
      ∀ suffix, values ≠ [] →
        DisjunctionTokens (tokens ++ .rparen :: suffix) names suffix := by
  induction h with
  | nil =>
    refine ⟨[], [], .nil, ?_, ?_⟩
    · simpa using Tokenization.empty
    · intros; contradiction
  | @cons first text rest texts head tail ih =>
    obtain ⟨name, firstTokens, namedHead, lexicalHead, parsedHead⟩ := literal_tokens head
    obtain ⟨names, tailTokens, namedTail, lexicalTail, parsedTail⟩ := ih
    cases rest with
    | nil =>
      have len := tail.length
      have empty : texts = [] := by cases texts <;> simp_all
      subst texts
      cases namedTail
      refine ⟨[name], firstTokens, .cons namedHead .nil, ?_, ?_⟩
      · simpa using lexicalHead
      · intro suffix _
        exact .last (parsedHead (.rparen :: suffix) (by simp))
    | cons next remaining =>
      have nonempty : texts ≠ [] := by
        intro empty
        have len := tail.length
        simp [empty] at len
      have separator : Tokenization (32 :: 124 :: 32 :: spelling (String.intercalate " | " texts))
          (.disjoin :: tailTokens) :=
        .whitespace (by simp [IsSpace])
          (.token (.punctuation .disjoin) (.whitespace (by simp [IsSpace]) lexicalTail))
      have boundary : StartsBoundary (32 :: 124 :: 32 :: spelling (String.intercalate " | " texts)) := by
        intro byte bytes equal
        have same := (List.cons.inj equal).1
        subst byte
        simp [IsWord, IsLower, IsUpper, IsDigit]
      have whole := tokenization_append lexicalHead separator boundary
      refine ⟨name :: names, firstTokens ++ .disjoin :: tailTokens,
        .cons namedHead namedTail, ?_, ?_⟩
      · simpa [String.intercalate_cons_of_ne_nil nonempty, spelling_append,
          List.append_assoc] using whole
      · intro suffix _
        have first := parsedHead (.disjoin :: (tailTokens ++ .rparen :: suffix)) (by simp)
        have rest := parsedTail suffix (by simp)
        simpa [List.append_assoc] using DisjunctionTokens.more first rest

/-- A clause body is parsed in its actual row context: the following closing
parenthesis belongs to the BodyTokens grammar and is consumed by it. -/
def ClauseBytesParse (bytes : Bytes) (literals : List Source.Literal) : Prop :=
  ∃ tokens, Tokenization (bytes ++ [41]) tokens ∧ BodyTokens tokens literals []

theorem ClauseBytesParse.unique {bytes left right}
    (hl : ClauseBytesParse bytes left) (hr : ClauseBytesParse bytes right) : left = right := by
  obtain ⟨tokens, lexical, parsed⟩ := hl
  obtain ⟨other, otherLexical, otherParsed⟩ := hr
  have same := lexical.unique otherLexical
  subst other
  exact (parsed.unique otherParsed).1

theorem clause_byte_correspondence {problem : TstpExport.NamedProblem} (value : Fang.Clause)
    {text : String} (accepted : TstpExport.clause problem value = .ok text) :
    ∃ named, NamedClause problem value named ∧ ClauseBytesParse (spelling text) named := by
  cases value with
  | nil =>
    simp [TstpExport.clause, pure, Except.pure] at accepted
    subst text
    refine ⟨[], .nil, [.falseLiteral, .rparen], ?_, .falsity []⟩
    exact tokenization_append (word_tokenization (.falsity rfl))
      (.token (.punctuation .rparen) .empty) (punctuation_boundary Punctuation.rparen)
  | cons first rest =>
    cases hm : (first :: rest).mapM (TstpExport.literal problem) with
    | error e => simp [TstpExport.clause, hm, bind, Except.bind] at accepted
    | ok texts =>
      simp [TstpExport.clause, hm, bind, Except.bind, pure, Except.pure] at accepted
      subst text
      obtain ⟨names, tokens, named, lexical, parsed⟩ :=
        literals_tokens (literals_correspondence (first :: rest) hm)
      refine ⟨names, named, tokens ++ [.rparen], ?_, ?_⟩
      · exact tokenization_append lexical (.token (.punctuation .rparen) .empty)
          (punctuation_boundary Punctuation.rparen)
      · exact .disjunction (parsed [] (by simp))

end Fang.TstpText
