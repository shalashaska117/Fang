/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import TstpExport

namespace Fang.TstpText

/-- The ASCII subset of the official `sq_char` production: octal 040..046,
050..0133, 0135..0176, or an escaped quote/backslash. The payload is separate
from the spelling. This is a grammar relation, not a replacement printer. -/
inductive SqChar : List Char → Char → Prop where
  | plain (c : Char) (lo : 32 ≤ c.toNat) (hi : c.toNat ≤ 126)
      (quote : c ≠ '\'') (slash : c ≠ '\\') : SqChar [c] c
  | quote : SqChar ['\\', '\''] '\''
  | slash : SqChar ['\\', '\\'] '\\'

inductive SqBody : List Char → List Char → Prop where
  | nil : SqBody [] []
  | cons {code : List Char} {c : Char} {tail payload : List Char}
      (head : SqChar code c) (rest : SqBody tail payload) :
      SqBody (code ++ tail) (c :: payload)

inductive QuotedAtom : List Char → List Char → Prop where
  | atom {body payload : List Char} (nonempty : payload ≠ [])
      (grammar : SqBody body payload) :
      QuotedAtom ('\'' :: body ++ ['\'']) payload

theorem SqBody.append {left right payload₁ payload₂ : List Char}
    (h₁ : SqBody left payload₁) (h₂ : SqBody right payload₂) :
    SqBody (left ++ right) (payload₁ ++ payload₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons head rest ih => simpa [List.append_assoc] using SqBody.cons head ih

theorem quote_piece (c : Char) (h : 32 ≤ c.toNat ∧ c.toNat ≤ 126) :
    SqChar ((if c == '\'' || c == '\\' then "\\" else "") ++ String.singleton c).toList c := by
  by_cases hq : c = '\''
  · subst c; exact SqChar.quote
  by_cases hs : c = '\\'
  · subst c; exact SqChar.slash
  simpa [hq, hs] using SqChar.plain c h.1 h.2 hq hs

theorem quote_fold (chars : List Char) (acc : String) (payload : List Char)
    (hacc : SqBody acc.toList payload)
    (valid : ∀ c ∈ chars, 32 ≤ c.toNat ∧ c.toNat ≤ 126) :
    SqBody (chars.foldl (fun acc c =>
      acc ++ (if c == '\'' || c == '\\' then "\\" else "") ++ String.singleton c) acc).toList
      (payload ++ chars) := by
  induction chars generalizing acc payload with
  | nil => simpa using hacc
  | cons c rest ih =>
    have one := SqBody.cons (quote_piece c (valid c (by simp))) SqBody.nil
    have next := hacc.append one
    simp only [List.append_nil] at next
    have next' : SqBody
        (acc ++ (if c == '\'' || c == '\\' then "\\" else "") ++ String.singleton c).toList
        (payload ++ [c]) := by
      simpa [String.toList_append, List.append_assoc] using next
    simpa [List.foldl, List.append_assoc] using
      ih _ _ next' (fun x hx => valid x (by simp [hx]))

theorem quote_grammar {input output : String}
    (accepted : TstpExport.quote input = .ok output) :
    QuotedAtom output.toList input.toList := by
  unfold TstpExport.quote at accepted
  split at accepted
  · simp [throw, bind, Except.bind] at accepted
  · rename_i valid
    have nonempty : input.toList ≠ [] := by
      intro empty
      have : input = "" := by simpa using congrArg String.ofList empty
      subst input
      simp at valid
    have printable : ∀ c ∈ input.toList, 32 ≤ c.toNat ∧ c.toNat ≤ 126 := by
      exact (show input ≠ "" ∧ ∀ c ∈ input.toList, 32 ≤ c.toNat ∧ c.toNat ≤ 126 by
        simpa using valid).2
    have body := quote_fold input.toList "" [] SqBody.nil printable
    simp only [List.nil_append] at body
    have grammar := QuotedAtom.atom nonempty body
    simp [pure, Except.pure] at accepted
    subst output
    simpa [String.toList_append] using grammar

/-- A decoder for the separately stated quoted-body grammar. It rejects bare
quotes, control characters and unsupported escapes. It is used only in proofs. -/
def decodeBody : List Char → Option (List Char)
  | [] => some []
  | c :: rest =>
    if c = '\\' then
      match rest with
      | [] => none
      | escaped :: tail =>
        if escaped = '\'' ∨ escaped = '\\' then
          (escaped :: ·) <$> decodeBody tail
        else none
    else if 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '\'' then
      (c :: ·) <$> decodeBody rest
    else none

theorem decodeBody_correct {code payload : List Char} (grammar : SqBody code payload) :
    decodeBody code = some payload := by
  induction grammar with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | plain c lo hi quote slash =>
      simp only [List.cons_append, List.nil_append]
      rw [decodeBody.eq_def]
      simp [lo, hi, quote, slash, ih]
    | quote => simp [decodeBody, ih]
    | slash => simp [decodeBody, ih]

/-- Consume both delimiters and require a nonempty decoded payload, as required
by `single_quoted ::= single_quote sq_char sq_char* single_quote`. -/
def decodeQuoted : List Char → Option (List Char)
  | '\'' :: rest =>
    match rest.reverse with
    | '\'' :: body => do
      let payload ← decodeBody body.reverse
      if payload.isEmpty then none else some payload
    | _ => none
  | _ => none

theorem decodeQuoted_correct {code payload : List Char}
    (grammar : QuotedAtom code payload) : decodeQuoted code = some payload := by
  cases grammar with
  | atom nonempty body =>
    simp [decodeQuoted, List.reverse_append, decodeBody_correct body, nonempty]

theorem QuotedAtom.functional {code left right : List Char}
    (hl : QuotedAtom code left) (hr : QuotedAtom code right) : left = right := by
  have eq := (decodeQuoted_correct hl).symm.trans (decodeQuoted_correct hr)
  exact Option.some.inj eq

def unquote (text : String) : Option String := String.ofList <$> decodeQuoted text.toList

theorem quote_roundtrip {input output : String}
    (accepted : TstpExport.quote input = .ok output) : unquote output = some input := by
  simp [unquote, decodeQuoted_correct (quote_grammar accepted)]

theorem quote_utf8_roundtrip {input output : String}
    (accepted : TstpExport.quote input = .ok output) :
    String.toUTF8 <$> unquote output = some input.toUTF8 := by
  rw [quote_roundtrip accepted]
  rfl

theorem quote_injective {left right output : String}
    (hl : TstpExport.quote left = .ok output)
    (hr : TstpExport.quote right = .ok output) : left = right := by
  exact Option.some.inj ((quote_roundtrip hl).symm.trans (quote_roundtrip hr))

end Fang.TstpText
