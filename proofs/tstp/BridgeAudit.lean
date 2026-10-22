/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import SourceLexerBridge
import BodyBridge
import RowUniqueness
import SequenceUniqueness
open Fang.Source.Grammar

example {bytes token rest} (lexeme : Lexeme bytes token rest)
    (ascii : ∀ b ∈ bytes, b.toNat < 128)
    (suffix : List Char) (boundary : Fang.TstpUnique.WordBoundary suffix) :
    Fang.TstpUnique.readToken (bytes.map byteChar ++ suffix) =
      some (Fang.TstpText.sourceToken token, rest.map byteChar ++ suffix) :=
  Fang.TstpText.source_lexeme lexeme ascii suffix boundary
example {bytes tokens} (lexical : Tokenization bytes tokens)
    (suffix : List Char) (boundary : Fang.TstpUnique.WordBoundary suffix) :
    Fang.TstpText.SourcePrefix (bytes.map byteChar ++ suffix)
      (tokens.map Fang.TstpText.sourceToken) suffix :=
  Fang.TstpText.source_tokenization lexical suffix boundary
example {input token tokens rest}
    (h : Fang.TstpText.SourcePrefix input (token :: tokens) rest) :
    ∃ middle, Fang.TstpUnique.readToken input = some (token, middle) ∧
      Fang.TstpText.SourcePrefix middle tokens rest :=
  h.head

#print axioms Fang.TstpText.source_lexeme
#print axioms Fang.TstpText.source_tokenization
#print axioms Fang.TstpText.SourcePrefix.head

example {tokens values rest input suffix}
    (parsed : BodyTokens tokens values rest)
    (lexical : Fang.TstpText.SourcePrefix input (tokens.map Fang.TstpText.sourceToken) suffix) :
    ∃ middle, Fang.TstpBody.BodyPrefix input values middle ∧
      Fang.TstpText.SourcePrefix middle (rest.map Fang.TstpText.sourceToken) suffix :=
  Fang.TstpText.body_prefix parsed lexical
example {text : String} {values : List Fang.Source.Literal}
    (parsed : Fang.TstpText.ClauseBytesParse (spelling text) values)
    (suffix : List Char) (boundary : Fang.TstpUnique.WordBoundary suffix) :
    ∃ middle, Fang.TstpBody.BodyPrefix (text.toList ++ ')' :: suffix) values middle ∧
      Fang.TstpUnique.readToken middle = Fang.TstpUnique.readToken suffix :=
  Fang.TstpText.clause_prefix parsed suffix boundary

#print axioms Fang.TstpText.body_prefix
#print axioms Fang.TstpText.clause_prefix

example {input leftName rightName leftRole rightRole leftClause rightClause
    leftData rightData leftRest rightRest}
    (first : Fang.TstpText.ParsedRow input leftName leftRole leftClause leftData leftRest)
    (second : Fang.TstpText.ParsedRow input rightName rightRole rightClause rightData rightRest) :
    leftName = rightName ∧ leftRole = rightRole ∧ leftClause = rightClause ∧
      leftData = rightData ∧ leftRest = rightRest := first.unique second
example {text name role clause metadata}
    (grammar : Fang.TstpText.AnnotatedRowText text name role clause metadata) (suffix : List Char) :
    Fang.TstpText.ParsedRow (text.toList ++ suffix) name role clause metadata suffix := grammar.prefix suffix
example {left right leftName rightName leftRole rightRole leftClause rightClause
    leftData rightData leftSuffix rightSuffix}
    (first : Fang.TstpText.AnnotatedRowText left leftName leftRole leftClause leftData)
    (second : Fang.TstpText.AnnotatedRowText right rightName rightRole rightClause rightData)
    (same : left.toList ++ leftSuffix = right.toList ++ rightSuffix) :
    leftName = rightName ∧ leftRole = rightRole ∧ leftClause = rightClause ∧
      leftData = rightData ∧ leftSuffix = rightSuffix := first.prefix_unique second same
example {text leftName rightName leftRole rightRole leftClause rightClause leftData rightData}
    (first : Fang.TstpText.AnnotatedRowText text leftName leftRole leftClause leftData)
    (second : Fang.TstpText.AnnotatedRowText text rightName rightRole rightClause rightData) :
    leftName = rightName ∧ leftRole = rightRole ∧ leftClause = rightClause ∧ leftData = rightData :=
  first.functional second

#print axioms Fang.TstpText.ParsedRow.unique
#print axioms Fang.TstpText.AnnotatedRowText.prefix
#print axioms Fang.TstpText.AnnotatedRowText.prefix_unique
#print axioms Fang.TstpText.AnnotatedRowText.functional

example {input left right} (first : Fang.TstpText.ParsedRows input left)
    (second : Fang.TstpText.ParsedRows input right) : left = right := first.unique second
example {lines : List String} {rows : List Fang.TstpText.PrintedRow}
    (grammar : Fang.Source.RelatedLists Fang.TstpText.PrintedRowText lines rows) :
    Fang.TstpText.ParsedRows (String.join lines).toList rows := Fang.TstpText.printed_rows_parse grammar
example {leftLines rightLines : List String} {left right : List Fang.TstpText.PrintedRow}
    (first : Fang.Source.RelatedLists Fang.TstpText.PrintedRowText leftLines left)
    (second : Fang.Source.RelatedLists Fang.TstpText.PrintedRowText rightLines right)
    (same : String.join leftLines = String.join rightLines) : left = right :=
  Fang.TstpText.printed_rows_unique first second same

#print axioms Fang.TstpText.ParsedRows.unique
#print axioms Fang.TstpText.printed_rows_parse
#print axioms Fang.TstpText.printed_rows_unique
#print axioms Fang.TstpText.correspondence_printed_rows
