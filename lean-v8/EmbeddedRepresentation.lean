/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural decoding into the independent quantified logical model. -/
import EmbeddedPublicRectification
import QuantifiedFormula

namespace FangSkolemEmbeddedCore
open Aeneas.Std Aeneas.Data.ListN fang_skolem_core.fang_quantified_fof_core

mutual
def decodeTerm : fang_skolem_core.fang.syntax.Term → Fang.Term
  | .Var id => .var id.val
  | .Fun symbol arguments => .app symbol.val (decodeVec arguments)
def decodeVec : alloc.vec.Vec fang_skolem_core.fang.syntax.Term → List Fang.Term
  | ⟨slice⟩ => decodeSlice slice
def decodeSlice : Slice fang_skolem_core.fang.syntax.Term → List Fang.Term
  | ⟨_, terms, _⟩ => decodeTerms terms
def decodeTerms {n : Nat} : ListN fang_skolem_core.fang.syntax.Term n → List Fang.Term
  | .nil => []
  | .cons term rest => decodeTerm term :: decodeTerms rest
end

def decodeLiteral (literal : fang_skolem_core.fang.syntax.Literal) : Fang.Literal :=
  ⟨literal.positive, ⟨literal.predicate.val, decodeVec literal.arguments⟩⟩

def decodeFormula : Formula → Fang.QuantifiedFOF.Formula
  | .Atom predicate arguments => .atom ⟨predicate.val, decodeVec arguments⟩
  | .True => .truth
  | .False => .falsity
  | .Not body => .neg (decodeFormula body)
  | .And left right => .conj (decodeFormula left) (decodeFormula right)
  | .Or left right => .disj (decodeFormula left) (decodeFormula right)
  | .Implies left right => .implies (decodeFormula left) (decodeFormula right)
  | .Forall id body => .all id.val (decodeFormula body)
  | .Exists id body => .ex id.val (decodeFormula body)

def decodeNnf : Nnf → Fang.QuantifiedFOF.Nnf
  | .Literal literal => .lit (decodeLiteral literal)
  | .True => .truth
  | .False => .falsity
  | .And left right => .conj (decodeNnf left) (decodeNnf right)
  | .Or left right => .disj (decodeNnf left) (decodeNnf right)
  | .Forall id body => .all id.val (decodeNnf body)
  | .Exists id body => .ex id.val (decodeNnf body)

/-- The identity copier needs no relationship between an arbitrary lexical scope
    and its unused renaming stack. The false mode never consults that stack. -/
theorem scoped_identity_copy {signature : Signature} {allowed : U32 → Prop}
    {term : fang_skolem_core.fang.syntax.Term} (valid : ScopedTerm signature allowed term) (stack : Bindings) :
    RenamedTerm stack false term term := by
  induction valid with
  | var id member => exact .var id id rfl
  | fun_ symbol arguments arity children ih =>
    exact .fun_ symbol arguments arguments rfl (fun i hi _ => ih i hi)

end FangSkolemEmbeddedCore
