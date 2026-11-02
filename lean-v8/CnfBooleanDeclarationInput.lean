/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   New framing candidate; the accepted decoder remains unchanged. -/
import CnfBooleanGrammar
import FofDeclarationSound

namespace Fang.TptpCandidate.FullFof.CnfBoolean

def declaration (seen : List Name) (endOffset : Nat) (tokens : List Token) :
    Except Error (Declaration × List Token) := do
  let keyword :: rest := tokens | failure .invalid endOffset tokens
  let isCnf ← match keyword.kind with
    | .legacy (.lower "cnf") => pure true
    | .legacy (.lower "fof") => pure false
    | .legacy (.lower "include") | .legacy (.lower "tff") | .legacy (.lower "thf") |
        .legacy (.lower "tcf") => failure .unsupported endOffset tokens
    | _ => failure .invalid endOffset tokens
  let (_, rest) ← expect '(' endOffset rest
  let nameToken :: rest := rest | failure .invalid endOffset rest
  let .legacy nameKind := nameToken.kind | failure .invalid endOffset (nameToken :: rest)
  let some name := nameKind.name | failure .invalid endOffset (nameToken :: rest)
  if seen.contains name then failure .invalid endOffset (nameToken :: rest)
  let (_, rest) ← expect ',' endOffset rest
  let role :: rest := rest | failure .invalid endOffset rest
  match role.kind with
  | .legacy (.lower "axiom") => pure ()
  | .legacy (.lower _) => failure .unsupported endOffset (role :: rest)
  | _ => failure .invalid endOffset (role :: rest)
  let (_, originalBody) ← expect ',' endOffset rest
  let (body, rest) ← if isCnf then do
      let (values, rest) ← clause (originalBody.length + 1) 1 endOffset originalBody
      pure (Body.cnf values, rest)
    else do
      let (body, rest) ← formula (3 * originalBody.length + 1) 1 [] endOffset originalBody
      pure (Body.fof body, rest)
  let bodyStop := ((originalBody.take (originalBody.length - rest.length)).getLast?.map Token.stop).getD endOffset
  if isChar ',' rest then failure .unsupported endOffset rest
  let (_, rest) ← expect ')' endOffset rest
  let (dot, rest) ← expect '.' endOffset rest
  pure (⟨name, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest)

end Fang.TptpCandidate.FullFof.CnfBoolean
