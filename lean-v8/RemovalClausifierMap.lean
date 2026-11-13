/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural maps preserve every ID, vector length, argument and literal. -/
import RemovalSemantics
import NnfEntry

open Aeneas.Std Aeneas.Data.ListN

namespace FangQuantifiedPipeline

mutual
def removedTerm : fang_binder_removal_core.fang.syntax.Term → fang_fof_core.fang.syntax.Term
  | .Var id => .Var id
  | .Fun symbol arguments => .Fun symbol (removedVec arguments)
def removedVec : alloc.vec.Vec fang_binder_removal_core.fang.syntax.Term →
    alloc.vec.Vec fang_fof_core.fang.syntax.Term
  | ⟨slice⟩ => ⟨removedSlice slice⟩
def removedSlice : Slice fang_binder_removal_core.fang.syntax.Term →
    Slice fang_fof_core.fang.syntax.Term
  | ⟨count, terms, bound⟩ => ⟨count, removedTerms terms, bound⟩
def removedTerms {n : Nat} : ListN fang_binder_removal_core.fang.syntax.Term n →
    ListN fang_fof_core.fang.syntax.Term n
  | .nil => .nil
  | .cons term rest => .cons (removedTerm term) (removedTerms rest)
end

mutual
theorem removedTerm_decode (term : fang_binder_removal_core.fang.syntax.Term) :
    FangScopedFof.decodeTerm (removedTerm term) = FangBinderRemovalCore.decodeTerm term := by
  cases term with
  | Var id => rfl
  | Fun symbol arguments => exact congrArg (Fang.Term.app symbol.val) (removedVec_decode arguments)
theorem removedVec_decode (arguments : alloc.vec.Vec fang_binder_removal_core.fang.syntax.Term) :
    FangScopedFof.decodeVec (removedVec arguments) = FangBinderRemovalCore.decodeVec arguments := by
  cases arguments with
  | mk slice => exact removedSlice_decode slice
theorem removedSlice_decode (slice : Slice fang_binder_removal_core.fang.syntax.Term) :
    FangScopedFof.decodeSlice (removedSlice slice) = FangBinderRemovalCore.decodeSlice slice := by
  cases slice with
  | mk count terms bound => exact removedTerms_decode terms
theorem removedTerms_decode {n : Nat} (terms : ListN fang_binder_removal_core.fang.syntax.Term n) :
    FangScopedFof.decodeTerms (removedTerms terms) = FangBinderRemovalCore.decodeTerms terms := by
  cases terms with
  | nil => rfl
  | cons term rest => exact congrArg₂ List.cons (removedTerm_decode term) (removedTerms_decode rest)
end

def removedLiteral (literal : fang_binder_removal_core.fang.syntax.Literal) :
    fang_fof_core.fang.syntax.Literal :=
  ⟨literal.positive, literal.predicate, removedVec literal.arguments⟩

theorem removedLiteral_decode (literal : fang_binder_removal_core.fang.syntax.Literal) :
    FangScopedFof.decodeLiteral (removedLiteral literal) = FangBinderRemovalCore.decodeLiteral literal := by
  simp only [FangScopedFof.decodeLiteral, removedLiteral, FangBinderRemovalCore.decodeLiteral,
    removedVec_decode]

def removedNnf : FangBinderRemovalCore.Output → fang_fof_core.Nnf
  | .Literal literal => .Literal (removedLiteral literal)
  | .True => .True
  | .False => .False
  | .And left right => .And (removedNnf left) (removedNnf right)
  | .Or left right => .Or (removedNnf left) (removedNnf right)

theorem removedNnf_decode (formula : FangBinderRemovalCore.Output) :
    FangScopedFof.decodeNnf (removedNnf formula) = FangBinderRemovalCore.decodeOutput formula := by
  induction formula with
  | Literal literal => exact congrArg Fang.GroundFOF.Nnf.lit (removedLiteral_decode literal)
  | True | False => rfl
  | And left right il ir | Or left right il ir =>
    simp only [removedNnf, FangScopedFof.decodeNnf, FangBinderRemovalCore.decodeOutput, il, ir]

end FangQuantifiedPipeline
