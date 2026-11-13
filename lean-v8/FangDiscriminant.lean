/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Proof-only naming adapter for the pinned Aeneas discriminant attribute. -/
module
public import Aeneas
public meta import Aeneas.Data.Discriminant
public section

open Lean Elab Term Meta Command

namespace FangDiscriminant

/-- Change only the missing declaration name of the backend-generated instance.
    The definition, type, binders and instance fields remain the backend syntax. -/
private meta partial def nameInstance (input : Syntax) (declId : Syntax) :
    Except String (Syntax × Nat) := do
  match input with
  | .node info kind args =>
    if kind == ``Lean.Parser.Command.instance then
      if args.size != 6 || args[3]!.getArgs.size != 0 then
        throw "Unexpected backend instance syntax; expected one unnamed instance"
      return (.node info kind (args.set! 3 (mkNullNode #[declId])), 1)
    else
      let mut count := 0
      let mut mapped := #[]
      for child in args do
        let (output, found) ← nameInstance child declId
        mapped := mapped.push output
        count := count + found
      return (.node info kind mapped, count)
  | other => return (other, 0)

meta def generate (declName : Name) (ty : Aeneas.Discriminant.ScalarTy)
    (values : Option (List Nat)) : CommandElabM Unit := do
  let cmds ← liftTermElabM (Aeneas.Discriminant.generateReadDiscriminantCmds declName ty values)
  let [definition, instanceCmd] := cmds
    | throwError "Unexpected backend discriminant command count"
  let instanceName := declName.str "fangDiscriminantInstance"
  if (← getEnv).contains instanceName then
    throwError "Discriminant instance name already exists: {instanceName}"
  let identifier := mkIdent (`_root_ ++ instanceName)
  let namedId ← `(Lean.Parser.Command.declId| $identifier:ident)
  let (named, count) ← match nameInstance instanceCmd namedId with
    | .ok result => pure result
    | .error message => throwError message
  unless count == 1 do
    throwError "Expected exactly one backend-generated instance; found {count}"
  elabCommand definition
  elabCommand named

syntax (name := fangDiscriminant) "fang_discriminant" ident ("["num,*"]")? : attr

public meta initialize fangDiscriminantAttribute : AttributeImpl ← do
  let implementation : AttributeImpl := {
    «name» := `fangDiscriminant
    descr := "Aeneas discriminant generation with a qualified explicit instance name"
    add := fun declName stx _ => do
      let original ← match stx with
        | `(attr| fang_discriminant $ty) => `(attr| discriminant $ty)
        | `(attr| fang_discriminant $ty [$values,*]) => `(attr| discriminant $ty [$values,*])
        | _ => throwUnsupportedSyntax
      let (ty, values) ← Aeneas.Discriminant.elabReadDiscriminantAttribute original
      liftCommandElabM (generate declName ty values)
  }
  registerBuiltinAttribute implementation
  pure implementation

end FangDiscriminant
