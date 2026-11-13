/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Revision 2 of the coverage framer (`CoverageFramer`, frozen): `cutRecord`
   uses the last two pieces as the record's closing only when they are `).`.
   Independent byte framer for the coverage constructs: extended tokens,
   statement splitting, include directives, the annotation cut and general
   terms, distinct objects and typed rejections. Formula records are decoded by
   the accepted `CnfBoolean.declaration`. No Rust correspondence is claimed. -/
import CoverageBundle

namespace Fang.TptpCandidate.FullFof.Coverage.FramerV2

open Fang.TptpCandidate.FullFof.Coverage

/-- Tokens the accepted lexer does not produce. -/
inductive Extra where
  | distinct : String → Extra
  | number : String → Extra
  | defined : String → Extra
  | system : String → Extra
  | backQuoted : String → Extra
  | star : Extra
  deriving Repr, BEq, DecidableEq

inductive Piece where
  | old : Token → Piece
  | extra : Extra → Nat → Nat → Piece
  deriving Repr, BEq

def Piece.start : Piece → Nat
  | .old token => token.start
  | .extra _ start _ => start

def Piece.isPunct (char : Char) : Piece → Bool
  | .old token => token.kind == .legacy (.punctuation char)
  | .extra _ _ _ => false

def formulaData : List String := ["$fof", "$cnf", "$fot", "$tff", "$thf"]

namespace Policy

/-- Decided OPEN-2: relative paths only; no empty, `.` or `..` component;
    no backslash, colon or NUL; at most 4096 bytes and 64 components. -/
def pathParts (path : String) : Option (List String) :=
  let parts := path.splitOn "/"
  if path.isEmpty || path.length > 4096 || path.startsWith "/" then none
  else if path.any (fun c => c == '\\' || c == ':' || c.toNat == 0) then none
  else if parts.length > 64 then none
  else if parts.any (fun part => part.isEmpty || part == "." || part == "..") then none
  else some parts

/-- Decided OPEN-4: include namespaces are unsupported. -/
def namespaceAllowed : Bool := false

/-- Decided OPEN-8, OPEN-9, OPEN-10: numbers, `$distinct` and every other
    defined word, system words and back-quoted words never become ordinary
    symbols in a formula. True means unsupported; false means invalid input. -/
def formulaUnsupported : Extra → Bool
  | .number _ | .system _ | .backQuoted _ => true
  | .defined word => !formulaData.contains word
  | .star | .distinct _ => false

end Policy

/-- After the opening double quote; the count includes the closing quote. -/
def distinctBody (origin offset : Nat) : List Char → Except Error (List Char × Nat)
  | [] => .error ⟨.invalid, origin⟩
  | '"' :: _ => .ok ([], 1)
  | '\\' :: [] => .error ⟨.invalid, origin⟩
  | '\\' :: escaped :: rest =>
    if escaped == '"' || escaped == '\\' then do
      let (value, count) ← distinctBody origin (offset + 2) rest
      pure (escaped :: value, count + 2)
    else .error ⟨.invalid, offset + 1⟩
  | c :: rest =>
    if 32 ≤ c.toNat && c.toNat ≤ 126 then do
      let (value, count) ← distinctBody origin (offset + 1) rest
      pure (c :: value, count + 1)
    else .error ⟨.invalid, offset⟩

def exponentLength : List Char → Option Nat
  | c :: rest =>
    if c == 'e' || c == 'E' then
      let sign := match rest with
        | s :: _ => if s == '+' || s == '-' then 1 else 0
        | [] => 0
      let digits := (rest.drop sign).takeWhile digit
      if digits.isEmpty then none else some (1 + sign + digits.length)
    else none
  | [] => none

/-- After integer digits: the remaining length of a rational or real. -/
def numberTail (start separatorOffset : Nat) (leadingZero : Bool) (after : List Char) :
    Option (Except Error Nat) :=
  match after with
  | separator :: d :: rest =>
    if (separator == '/' || separator == '.') && digit d then
      if leadingZero then some (.error ⟨.invalid, start⟩)
      else if separator == '/' && d == '0' then some (.error ⟨.invalid, separatorOffset + 1⟩)
      else
        let fraction := (d :: rest).takeWhile digit
        let exponent := if separator == '.' then
          (exponentLength ((d :: rest).drop fraction.length)).getD 0 else 0
        some (.ok (1 + fraction.length + exponent))
    else (exponentLength after).map .ok
  | _ => (exponentLength after).map .ok

/-- A new construct at the head of the input, or `none` for the accepted lexer. -/
def extraPiece (offset : Nat) : List Char → Option (Except Error (Extra × Nat))
  | '"' :: rest => some do
    let (value, count) ← distinctBody offset (offset + 1) rest
    if value.isEmpty then throw ⟨.invalid, offset⟩
    pure (.distinct (String.ofList value), count + 1)
  | '$' :: '$' :: rest =>
    let tail := rest.takeWhile word
    some (.ok (.system (String.ofList ('$' :: '$' :: tail)), tail.length + 2))
  | '$' :: rest =>
    let tail := rest.takeWhile word
    let value := String.ofList ('$' :: tail)
    if value == "$true" || value == "$false" then none
    else some (.ok (.defined value, tail.length + 1))
  | '`' :: c :: rest =>
    if upper c then
      let tail := rest.takeWhile word
      some (.ok (.backQuoted (String.ofList ('`' :: c :: tail)), tail.length + 2))
    else some (.error ⟨.invalid, offset⟩)
  | ['`'] => some (.error ⟨.invalid, offset⟩)
  | '*' :: _ => some (.ok (.star, 1))
  | '-' :: '-' :: '>' :: _ => some (.error ⟨.unsupported, offset⟩)
  | '/' :: rest => if rest.head? == some '*' then none else some (.error ⟨.invalid, offset⟩)
  | input@(c :: _) =>
    if digit c || c == '+' || c == '-' then
      let sign := if c == '+' || c == '-' then 1 else 0
      let body := input.drop sign
      let digits := body.takeWhile digit
      if digits.isEmpty then none
      else
        let leadingZero := digits.head? == some '0' && digits.length != 1
        match numberTail offset (offset + sign + digits.length) leadingZero (body.drop digits.length) with
        | none => none
        | some (.error failure) => some (.error failure)
        | some (.ok extra) =>
          let count := sign + digits.length + extra
          some (.ok (.number (String.ofList (input.take count)), count))
    else none
  | [] => none

def lexLoop : Nat → List Char → Nat → Except Error (List Piece)
  | 0, _, offset => .error ⟨.resource, offset⟩
  | _ + 1, [], _ => .ok []
  | fuel + 1, input@(_ :: _), offset =>
    match extraPiece offset input with
    | some (.error failure) => .error failure
    | some (.ok (extra, count)) =>
      if count == 0 || input.length < count then .error ⟨.internal, offset⟩
      else match lexLoop fuel (input.drop count) (offset + count) with
        | .error failure => .error failure
        | .ok rest => .ok (.extra extra offset (offset + count) :: rest)
    | none => do
      let (kind, count) ← FullFof.piece offset input
      if count == 0 || input.length < count then throw ⟨.internal, offset⟩
      let rest ← lexLoop fuel (input.drop count) (offset + count)
      match kind with
      | none => pure rest
      | some kind => pure (.old ⟨kind, offset, offset + count, input.take count⟩ :: rest)

def tokenize (input : List UInt8) (maximum : Nat) : Except Error (List Piece) :=
  if input.length > maximum then .error ⟨.resource, 0⟩
  else lexLoop (input.length + 1) (byteChars input) 0

def depthStep (depth : Int) (piece : Piece) : Int :=
  if piece.isPunct '(' || piece.isPunct '[' then depth + 1
  else if piece.isPunct ')' || piece.isPunct ']' then depth - 1
  else depth

/-- One statement: pieces through the first dot at depth 0, or every
    remaining piece when no such dot exists (the parse then reports it). -/
def splitStatement : Int → List Piece → List Piece → List Piece × List Piece
  | _, acc, [] => (acc, [])
  | depth, acc, piece :: rest =>
    if piece.isPunct '.' && depth == 0 then (acc ++ [piece], rest)
    else splitStatement (depthStep depth piece) (acc ++ [piece]) rest

/-- Index of the comma number `wanted` (from 0) at depth 1. -/
def commaIndex : Nat → Int → Nat → List Piece → Option Nat
  | _, _, _, [] => none
  | wanted, depth, index, piece :: rest =>
    if piece.isPunct ',' && depth == 1 then
      if wanted == 0 then some index else commaIndex (wanted - 1) depth (index + 1) rest
    else commaIndex wanted (depthStep depth piece) (index + 1) rest

/-- The name a distinct object takes inside the accepted decoder. NUL cannot
    occur in a lower word or a quoted atom, so it never meets an ordinary name. -/
def objectName (content : String) : String := String.ofList ('\x00' :: content.toList)

def isObject (value : String) : Bool := value.toList.head? == some '\x00'

/-- Map a formula-part piece to an accepted token. Unsupported constructs
    become an integer token, which the accepted grammar rejects as unsupported
    in every term position and as invalid elsewhere; invalid ones become `*`. -/
def coreToken : Piece → Token
  | .old token => token
  | .extra (.distinct content) start stop => ⟨.legacy (.quoted (objectName content)), start, stop, []⟩
  | .extra extra start stop =>
    if Policy.formulaUnsupported extra then ⟨.legacy (.integer "0"), start, stop, []⟩
    else ⟨.legacy (.punctuation '*'), start, stop, []⟩

def nameOf : Piece → Option Name
  | .old token => match token.kind with
    | .legacy kind => kind.name
    | _ => none
  | .extra _ _ _ => none

def isBackQuoted : Piece → Bool
  | .extra (.backQuoted _) _ _ => true
  | _ => false

section Annotation

def depthLimit : Nat := 64

mutual
/-- `<general_term>`; returns the pieces after it. -/
def term : Nat → Nat → List Piece → Except Error (List Piece)
  | 0, _, pieces => .error ⟨.resource, (pieces.head?.map Piece.start).getD 0⟩
  | fuel + 1, depth, pieces =>
    if depth > depthLimit then .error ⟨.resource, (pieces.head?.map Piece.start).getD 0⟩
    else match pieces with
      | first :: rest =>
        if first.isPunct '[' then
          match rest with
          | next :: after => if next.isPunct ']' then .ok after else terms fuel (depth + 1) ']' rest
          | [] => terms fuel (depth + 1) ']' rest
        else match data fuel depth pieces with
          | .error failure => .error failure
          | .ok (next :: after) => if next.isPunct ':' then term fuel (depth + 1) after else .ok (next :: after)
          | .ok [] => .ok []
      | [] => .error ⟨.invalid, 0⟩
/-- `<general_terms>` and the closing bracket. -/
def terms : Nat → Nat → Char → List Piece → Except Error (List Piece)
  | 0, _, _, pieces => .error ⟨.resource, (pieces.head?.map Piece.start).getD 0⟩
  | fuel + 1, depth, close, pieces =>
    match term fuel depth pieces with
    | .error failure => .error failure
    | .ok (next :: after) =>
      if next.isPunct ',' then terms fuel depth close after
      else if next.isPunct close then .ok after
      else .error ⟨.invalid, next.start⟩
    | .ok [] => .error ⟨.invalid, 0⟩
/-- `<general_data>`. -/
def data : Nat → Nat → List Piece → Except Error (List Piece)
  | 0, _, pieces => .error ⟨.resource, (pieces.head?.map Piece.start).getD 0⟩
  | fuel + 1, depth, pieces =>
    match pieces with
    | .old token :: rest =>
      match token.kind with
      | .legacy (.lower _) | .legacy (.quoted _) =>
        match rest with
        | next :: after => if next.isPunct '(' then terms fuel (depth + 1) ')' after else .ok rest
        | [] => .ok rest
      | .legacy (.variable _) | .legacy (.integer _) => .ok rest
      | _ => .error ⟨.invalid, token.start⟩
    | .extra (.number _) _ _ :: rest | .extra (.distinct _) _ _ :: rest => .ok rest
    | .extra (.defined language) start _ :: rest =>
      if formulaData.contains language then
        match rest with
        | next :: _ => if next.isPunct '(' then balanced fuel [] rest else .error ⟨.invalid, start⟩
        | [] => .error ⟨.invalid, start⟩
      else .error ⟨.invalid, start⟩
    | piece :: _ => .error ⟨.invalid, piece.start⟩
    | [] => .error ⟨.invalid, 0⟩
/-- Formula data payload: bracket-balanced pieces only (decided OPEN-7). -/
def balanced : Nat → List Char → List Piece → Except Error (List Piece)
  | 0, _, pieces => .error ⟨.resource, (pieces.head?.map Piece.start).getD 0⟩
  | fuel + 1, pending, piece :: rest =>
    if piece.isPunct '(' || piece.isPunct '[' then
      if pending.length ≥ depthLimit then .error ⟨.resource, piece.start⟩
      else balanced fuel ((if piece.isPunct '(' then ')' else ']') :: pending) rest
    else if piece.isPunct ')' || piece.isPunct ']' then
      match pending with
      | close :: outer =>
        if piece.isPunct close then (if outer.isEmpty then .ok rest else balanced fuel outer rest)
        else .error ⟨.invalid, piece.start⟩
      | [] => .error ⟨.invalid, piece.start⟩
    else balanced fuel pending rest
  | _ + 1, _, [] => .error ⟨.invalid, 0⟩
end

/-- Decided OPEN-6: `<source>` is any general term; `<useful_info>` is a
    general list; nothing may follow. Annotations never reach the decoder. -/
def annotation (pieces : List Piece) : Except Error Unit :=
  let fuel := 2 * pieces.length + 2
  match term fuel 1 pieces with
  | .error failure => .error failure
  | .ok [] => .ok ()
  | .ok (next :: after) =>
    if next.isPunct ',' then
      match after with
      | first :: _ =>
        if first.isPunct '[' then
          match term fuel 1 after with
          | .error failure => .error failure
          | .ok [] => .ok ()
          | .ok (extra :: _) => .error ⟨.invalid, extra.start⟩
        else .error ⟨.invalid, first.start⟩
      | [] => .error ⟨.invalid, next.start⟩
    else .error ⟨.invalid, next.start⟩

end Annotation

def selectionNames : Nat → List Piece → Except Error (List Name × List Piece)
  | 0, pieces => .error ⟨.resource, (pieces.head?.map Piece.start).getD 0⟩
  | fuel + 1, piece :: rest =>
    match nameOf piece with
    | none => .error ⟨if isBackQuoted piece then .unsupported else .invalid, piece.start⟩
    | some label =>
      match rest with
      | next :: after =>
        if next.isPunct ',' then do
          let (more, final) ← selectionNames fuel after
          pure (label :: more, final)
        else .ok ([label], rest)
      | [] => .ok ([label], [])
  | _ + 1, [] => .error ⟨.invalid, 0⟩

def closing : List Piece → Bool
  | [close, dot] => close.isPunct ')' && dot.isPunct '.'
  | _ => false

/-- `include(<file_name><include_optionals>).` An invalid path becomes the
    part list `[""]`, which no well-shaped bundle key matches, so resolution
    reports it as missing at the same point the Rust candidate checks paths. -/
def directive (pieces : List Piece) : Except Error (List String × Selection) :=
  match pieces with
  | _ :: opening :: path :: rest =>
    if !opening.isPunct '(' then .error ⟨.invalid, opening.start⟩
    else
      let value : Except Error String := match path with
        | .old token => match token.kind with
          | .legacy (.lower text) | .legacy (.quoted text) => .ok text
          | _ => .error ⟨.invalid, token.start⟩
        | .extra (.backQuoted _) start _ => .error ⟨.unsupported, start⟩
        | .extra _ start _ => .error ⟨.invalid, start⟩
      match value with
      | .error failure => .error failure
      | .ok text =>
        let parts := (Policy.pathParts text).getD [""]
        if closing rest then .ok (parts, .absent)
        else match rest with
          | comma :: more =>
            if !comma.isPunct ',' then .error ⟨.invalid, comma.start⟩
            else
              let selection : Except Error (Selection × List Piece) := match more with
                | .extra .star _ _ :: after => .ok (.star, after)
                | bracket :: after =>
                  if bracket.isPunct '[' then
                    match selectionNames 4096 after with
                    | .error failure => .error failure
                    | .ok (labels, close :: final) =>
                      if close.isPunct ']' then .ok (.names labels, final) else .error ⟨.invalid, close.start⟩
                    | .ok (_, []) => .error ⟨.invalid, 0⟩
                  else .error ⟨.invalid, bracket.start⟩
                | [] => .error ⟨.invalid, 0⟩
              match selection with
              | .error failure => .error failure
              | .ok (chosen, after) =>
                if closing after then .ok (parts, chosen)
                else match after with
                  | comma :: space :: _ =>
                    if !comma.isPunct ',' then .error ⟨.invalid, comma.start⟩
                    else if (nameOf space).isSome || isBackQuoted space then
                      .error ⟨if Policy.namespaceAllowed then .invalid else .unsupported, space.start⟩
                    else .error ⟨.invalid, space.start⟩
                  | piece :: _ => .error ⟨.invalid, piece.start⟩
                  | [] => .error ⟨.invalid, 0⟩
          | [] => .error ⟨.invalid, 0⟩
  | piece :: _ => .error ⟨.invalid, piece.start⟩
  | [] => .error ⟨.invalid, 0⟩

/-- Distinct objects are constants: never formulas, never applied. -/
def objectsWellUsed (value : Declaration) : Bool :=
  !(value.body.formula.predicates.any (fun symbol => isObject symbol.1)) &&
    !(value.body.formula.functions.any (fun symbol => isObject symbol.1 && symbol.2 != 0))

/-- The record name is never a mapped token: a distinct object or number
    there is invalid, as in the accepted grammar's name position. -/
def nameGuard : List Piece → Except Error Unit
  | _ :: _ :: .extra _ start _ :: _ => .error ⟨.invalid, start⟩
  | _ => .ok ()

/-- Everything before the annotation cut plus the closing `).`, and the
    annotation pieces when a cut exists. -/
def cutRecord (pieces : List Piece) : List Piece × Option (List Piece) :=
  match commaIndex 2 0 0 pieces with
  | some cut =>
    -- A record truncated after its annotation comma has no closing `).`;
    -- the decoder then sees the formula part alone and reports the missing
    -- parenthesis, as the Rust candidate does.
    if closing (pieces.drop (pieces.length - 2)) && cut + 3 ≤ pieces.length then
      ((pieces.take cut) ++ pieces.drop (pieces.length - 2),
        some ((pieces.drop (cut + 1)).take (pieces.length - (cut + 1) - 2)))
    else (pieces.take cut, some (pieces.drop (cut + 1)))
  | none => (pieces, none)

/-- A formula record: the accepted decoder reads the part before the cut;
    the annotation is checked apart and never reaches the decoder. -/
def formulaRecord (seen : List Name) (endOffset : Nat) (pieces : List Piece) :
    Except Error Declaration :=
  match nameGuard pieces with
  | .error failure => .error failure
  | .ok () =>
    match CnfBoolean.declaration seen endOffset ((cutRecord pieces).1.map coreToken) with
    | .error failure => .error failure
    | .ok (value, rest) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map Token.start).getD endOffset⟩
      else if !objectsWellUsed value then .error ⟨.invalid, value.start⟩
      else match (cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match annotation annotationPieces with
          | .error failure => .error failure
          | .ok () => .ok value

def keyword (pieces : List Piece) : Option String :=
  match pieces with
  | .old token :: _ => match token.kind with
    | .legacy (.lower text) => some text
    | _ => none
  | _ => none

/-- Frame every statement of one file; formula names are unique per file. -/
def statements : Nat → List Name → Nat → List Piece → Except Error (List Statement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ 1000 then .error ⟨.resource, first.start⟩
    else
      let split := splitStatement 0 [] (first :: more)
      match keyword split.1 with
      | some "include" =>
        match directive split.1 with
        | .error failure => .error failure
        | .ok (parts, selection) =>
          match statements fuel seen endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecord seen endOffset split.1 with
        | .error failure => .error failure
        | .ok value =>
          match statements fuel (value.name :: seen) endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.formula value :: tail)

def frameFile (bytes : List UInt8) (maximum : Nat) : Except Error (List Statement) :=
  match tokenize bytes maximum with
  | .error failure => .error failure
  | .ok pieces => statements (pieces.length + 1) [] bytes.length pieces

def frameBundle : List (Key × List UInt8) → Nat → Except Error Bundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFile bytes maximum with
    | .error failure => .error failure
    | .ok framed => match frameBundle rest maximum with
      | .error failure => .error failure
      | .ok others => .ok (⟨key, framed⟩ :: others)

/-! Bundle shape: the files are exactly those reached, in first-reach order,
    with distinct well-formed keys. -/

def reachWalk (bundle : Bundle) (recurse : List Nat → Nat → List Nat → Except Failure (List Nat))
    (stack : List Nat) (key : Key) : List Statement → List Nat → Except Failure (List Nat)
  | [], order => .ok order
  | .formula _ :: rest, order => reachWalk bundle recurse stack key rest order
  | .directive parts _ :: rest, order =>
    match resolve bundle key parts with
    | none => .error .missing
    | some child =>
      let order := if child ∈ order then order else order ++ [child]
      if child ∈ stack then .error .cycle
      else match recurse (child :: stack) child order with
        | .error failure => .error failure
        | .ok order => reachWalk bundle recurse stack key rest order

def reach (bundle : Bundle) : Nat → List Nat → Nat → List Nat → Except Failure (List Nat)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, stack, index, order =>
    match bundle[index]? with
    | none => .error .missing
    | some file => reachWalk bundle (reach bundle fuel) stack file.key file.statements order

def keyWellFormed (key : Key) : Bool :=
  !key.path.isEmpty && key.path.all (fun part => !part.isEmpty && !part.contains '/')

def wellShaped (bundle : Bundle) (fuel : Nat) : Bool :=
  (bundle.map File.key).Nodup && bundle.all (fun file => keyWellFormed file.key) &&
    match reach bundle fuel [0] 0 [0] with
    | .ok order => order == List.range bundle.length
    | .error _ => false

/-- Distinct-object names of a declaration list, in first-occurrence order. -/
def objectNames (values : List Declaration) : List String :=
  (((source values).flatMap Formula.functions).filterMap
    (fun symbol => if isObject symbol.1 then some symbol.1 else none)).eraseDups

def NamedSeparated {D : Type} (model : Source.Interpretation D) (names : List String) : Prop :=
  ∀ left ∈ names, ∀ right ∈ names, left ≠ right → model.function left [] ≠ model.function right []

/-- The meaning of a sealed bundle of files: framed, well shaped, expanded,
    and satisfiable with pairwise different distinct objects. -/
def ByteBundleSatisfiable (files : List (Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, frameBundle files maximum = .ok bundle ∧ wellShaped bundle fuel = true ∧
    expand bundle fuel = .ok items ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Models (source (declarationsOf bundle items)) model ∧
      NamedSeparated model (objectNames (declarationsOf bundle items))

theorem frameBundle_keys {files : List (Key × List UInt8)} {maximum : Nat} {bundle : Bundle}
    (success : frameBundle files maximum = .ok bundle) : bundle.map File.key = files.map Prod.fst := by
  induction files generalizing bundle with
  | nil => simp only [frameBundle, Except.ok.injEq] at success; subst success; rfl
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundle] at success
    split at success
    · cases success
    · split at success
      · cases success
      · rename_i others tail
        simp only [Except.ok.injEq] at success
        subst success
        simp [ih tail]

/-- Without distinct objects the byte meaning is the framed bundle meaning. -/
theorem byte_bundle_without_objects {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} (framed : frameBundle files maximum = .ok bundle)
    (shaped : wellShaped bundle fuel = true) (expanded : expand bundle fuel = .ok items)
    (none : objectNames (declarationsOf bundle items) = []) :
    ByteBundleSatisfiable files maximum fuel ↔ BundleSatisfiable bundle fuel := by
  constructor
  · rintro ⟨bundle', items', framed', _, expanded', D, inhabited, model, holds, _⟩
    rw [framed] at framed'
    cases framed'
    rw [expanded] at expanded'
    cases expanded'
    exact ⟨items, expanded, D, inhabited, model, holds⟩
  · rintro ⟨items', expanded', D, inhabited, model, holds⟩
    rw [expanded] at expanded'
    cases expanded'
    refine ⟨bundle, items, framed, shaped, expanded, D, inhabited, model, holds, ?_⟩
    rw [none]
    intro left member
    simp at member

/-- Refuting the expanded problem together with the separation condition
    refutes the sealed bundle. -/
theorem byte_bundle_unsat {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} (framed : frameBundle files maximum = .ok bundle)
    (expanded : expand bundle fuel = .ok items)
    (refuted : ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Models (source (declarationsOf bundle items)) model →
        ¬ NamedSeparated model (objectNames (declarationsOf bundle items))) :
    ¬ ByteBundleSatisfiable files maximum fuel := by
  rintro ⟨bundle', items', framed', _, expanded', D, inhabited, model, holds, separated⟩
  rw [framed] at framed'
  cases framed'
  rw [expanded] at expanded'
  cases expanded'
  exact refuted D inhabited model holds separated

theorem objectName_isObject (content : String) : isObject (objectName content) = true := by
  simp [isObject, objectName]

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.frameBundle_keys
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.byte_bundle_without_objects
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.byte_bundle_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.objectName_isObject

end Fang.TptpCandidate.FullFof.Coverage.FramerV2
