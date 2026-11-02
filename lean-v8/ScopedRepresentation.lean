/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural decoding only; production normalization remains the generated Rust function. -/
import ScopedCopy
import GroundFormula

namespace FangScopedFof
open Aeneas.Std Aeneas.Data.ListN fang_fof_core

mutual
def decodeTerm : fang.syntax.Term → Fang.Term
  | .Var v => .var v.val
  | .Fun symbol arguments => .app symbol.val (decodeVec arguments)
def decodeVec : alloc.vec.Vec fang.syntax.Term → List Fang.Term
  | ⟨slice⟩ => decodeSlice slice
def decodeSlice : Slice fang.syntax.Term → List Fang.Term
  | ⟨_, terms, _⟩ => decodeTerms terms
def decodeTerms {n : Nat} : ListN fang.syntax.Term n → List Fang.Term
  | .nil => []
  | .cons term rest => decodeTerm term :: decodeTerms rest
end

def decodeLiteral (literal : fang.syntax.Literal) : Fang.Literal :=
  ⟨literal.positive, ⟨literal.predicate.val, decodeVec literal.arguments⟩⟩

def decodeFormula : Formula → Fang.GroundFOF.Formula
  | .Atom predicate arguments => .atom ⟨predicate.val, decodeVec arguments⟩
  | .True => .truth
  | .False => .falsity
  | .Not inner => .neg (decodeFormula inner)
  | .And left right => .conj (decodeFormula left) (decodeFormula right)
  | .Or left right => .disj (decodeFormula left) (decodeFormula right)
  | .Implies left right => .implies (decodeFormula left) (decodeFormula right)

def decodeNnf : Nnf → Fang.GroundFOF.Nnf
  | .Literal literal => .lit (decodeLiteral literal)
  | .True => .truth
  | .False => .falsity
  | .And left right => .conj (decodeNnf left) (decodeNnf right)
  | .Or left right => .disj (decodeNnf left) (decodeNnf right)

end FangScopedFof
