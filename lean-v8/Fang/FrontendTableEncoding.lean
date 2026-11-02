/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Encoding witnesses with explicit lookup premises, preserved as parser tables grow.
This relation is a proof specification; it does not execute or replace the parser.
-/
import Fang.FrontendEncoding
import Fang.FrontendTableExtension

namespace Fang.Frontend

mutual
inductive TableTermEncoding (state : State) : Source.Term → Fang.Term → Prop where
  | var (name : String) (id : Nat) (found : namedIndex name state.variables 0 = some id) :
      TableTermEncoding state (.var name) (.var id)
  | app (name : String) (id : Nat) (arguments : List Source.Term) (encoded : List Fang.Term)
      (found : symbolIndex name state.functions 0 = some id)
      (checked : (state.functions[id]?).map Symbol.arity = some (some arguments.length))
      (children : TableTermsEncoding state arguments encoded) :
      TableTermEncoding state (.app name arguments) (.app id encoded)
inductive TableTermsEncoding (state : State) : List Source.Term → List Fang.Term → Prop where
  | nil : TableTermsEncoding state [] []
  | cons {named encoded names terms} (head : TableTermEncoding state named encoded)
      (tail : TableTermsEncoding state names terms) :
      TableTermsEncoding state (named :: names) (encoded :: terms)
end

theorem TableTermsEncoding.length {state named encoded}
    (encoding : TableTermsEncoding state named encoded) : named.length = encoded.length := by
  cases encoding with
  | nil => rfl
  | cons head tail => exact congrArg Nat.succ tail.length

mutual
theorem TableTermEncoding.toSource {state named encoded}
    (encoding : TableTermEncoding state named encoded) :
    Source.TermEncoding (signatureFrom state) (symbolsFrom state)
      (variablesFrom state.variables) named encoded := by
  cases encoding with
  | var name id found => exact variable_encoding_of_found _ _ found
  | app name id arguments encoded found checked children =>
      exact function_encoding_of_found state _ found checked children.toSource

theorem TableTermsEncoding.toSource {state named encoded}
    (encoding : TableTermsEncoding state named encoded) :
    Source.TermsEncoding (signatureFrom state) (symbolsFrom state)
      (variablesFrom state.variables) named encoded := by
  cases encoding with
  | nil => exact .nil
  | cons head tail => exact .cons head.toSource tail.toSource
end

mutual
theorem TableTermEncoding.extend {before after named encoded}
    (encoding : TableTermEncoding before named encoded) (extension : TableExtension before after) :
    TableTermEncoding after named encoded := by
  cases encoding with
  | var name id found => exact .var name id (extension.variables name id found)
  | app name id arguments encoded found checked children =>
      exact .app name id arguments encoded (extension.symbols false name id found)
        (extension.arities false id arguments.length checked) (children.extend extension)

theorem TableTermsEncoding.extend {before after named encoded}
    (encoding : TableTermsEncoding before named encoded) (extension : TableExtension before after) :
    TableTermsEncoding after named encoded := by
  cases encoding with
  | nil => exact .nil
  | cons head tail => exact .cons (head.extend extension) (tail.extend extension)
end

structure TableLiteralEncoding (state : State) (named : Source.Literal) (encoded : Fang.Literal) : Prop where
  polarity : encoded.positive = named.positive
  found : symbolIndex named.predicate state.predicates 0 = some encoded.atom.pred
  checked : (state.predicates[encoded.atom.pred]?).map Symbol.arity = some (some named.arguments.length)
  arguments : TableTermsEncoding state named.arguments encoded.atom.args

theorem TableLiteralEncoding.toSource {state named encoded}
    (encoding : TableLiteralEncoding state named encoded) :
    Source.LiteralEncoding (signatureFrom state) (symbolsFrom state)
      (variablesFrom state.variables) named encoded := by
  rcases named with ⟨positive, name, arguments⟩
  rcases encoded with ⟨outputPositive, ⟨id, outputArguments⟩⟩
  rcases encoding with ⟨rfl, found, checked, children⟩
  exact literal_encoding_of_found state _ _ found checked children.toSource

theorem TableLiteralEncoding.extend {before after named encoded}
    (encoding : TableLiteralEncoding before named encoded) (extension : TableExtension before after) :
    TableLiteralEncoding after named encoded := by
  exact ⟨encoding.polarity, extension.symbols true _ _ encoding.found,
    extension.arities true _ _ encoding.checked, encoding.arguments.extend extension⟩

#print axioms TableTermEncoding.toSource
#print axioms TableTermEncoding.extend
#print axioms TableLiteralEncoding.toSource
#print axioms TableLiteralEncoding.extend

end Fang.Frontend
