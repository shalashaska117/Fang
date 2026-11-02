/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural maps between duplicate extraction namespaces, not Rust algorithms. -/
import TransformOutput
import RemovalSemantics

open Aeneas.Std Aeneas.Data.ListN

namespace FangQuantifiedPipeline

mutual
def skolemTerm : fang_skolem_core.fang.syntax.Term → fang_binder_removal_core.fang.syntax.Term
  | .Var id => .Var id
  | .Fun symbol arguments => .Fun symbol (skolemVec arguments)
def skolemVec : alloc.vec.Vec fang_skolem_core.fang.syntax.Term →
    alloc.vec.Vec fang_binder_removal_core.fang.syntax.Term
  | ⟨slice⟩ => ⟨skolemSlice slice⟩
def skolemSlice : Slice fang_skolem_core.fang.syntax.Term →
    Slice fang_binder_removal_core.fang.syntax.Term
  | ⟨count, terms, bound⟩ => ⟨count, skolemTerms terms, bound⟩
def skolemTerms {n : Nat} : ListN fang_skolem_core.fang.syntax.Term n →
    ListN fang_binder_removal_core.fang.syntax.Term n
  | .nil => .nil
  | .cons term rest => .cons (skolemTerm term) (skolemTerms rest)
end

mutual
theorem skolemTerm_decode (term : fang_skolem_core.fang.syntax.Term) :
    FangBinderRemovalCore.decodeTerm (skolemTerm term) = FangSkolemCore.decodeTerm term := by
  cases term with
  | Var id => rfl
  | Fun symbol arguments => exact congrArg (Fang.Term.app symbol.val) (skolemVec_decode arguments)
theorem skolemVec_decode (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) :
    FangBinderRemovalCore.decodeVec (skolemVec arguments) = FangSkolemCore.decodeVec arguments := by
  cases arguments with
  | mk slice => exact skolemSlice_decode slice
theorem skolemSlice_decode (slice : Slice fang_skolem_core.fang.syntax.Term) :
    FangBinderRemovalCore.decodeSlice (skolemSlice slice) = FangSkolemCore.decodeSlice slice := by
  cases slice with
  | mk count terms bound => exact skolemTerms_decode terms
theorem skolemTerms_decode {n : Nat} (terms : ListN fang_skolem_core.fang.syntax.Term n) :
    FangBinderRemovalCore.decodeTerms (skolemTerms terms) = FangSkolemCore.decodeTerms terms := by
  cases terms with
  | nil => rfl
  | cons term rest => exact congrArg₂ List.cons (skolemTerm_decode term) (skolemTerms_decode rest)
end

def skolemLiteral (literal : fang_skolem_core.fang.syntax.Literal) :
    fang_binder_removal_core.fang.syntax.Literal :=
  ⟨literal.positive, literal.predicate, skolemVec literal.arguments⟩

theorem skolemLiteral_decode (literal : fang_skolem_core.fang.syntax.Literal) :
    FangBinderRemovalCore.decodeLiteral (skolemLiteral literal) =
      ⟨literal.positive, FangSkolemCore.decodeAtom literal⟩ := by
  simp only [FangBinderRemovalCore.decodeLiteral, skolemLiteral, FangSkolemCore.decodeAtom,
    skolemVec_decode]

def skolemNnf : fang_skolem_core.fang_quantified_fof_core.Nnf → FangBinderRemovalCore.Input
  | .Literal literal => .Literal (skolemLiteral literal)
  | .True => .True
  | .False => .False
  | .And left right => .And (skolemNnf left) (skolemNnf right)
  | .Or left right => .Or (skolemNnf left) (skolemNnf right)
  | .Forall id body => .Forall id (skolemNnf body)
  | .Exists id body => .Exists id (skolemNnf body)

theorem skolemNnf_decode (formula : fang_skolem_core.fang_quantified_fof_core.Nnf) :
    FangBinderRemovalCore.decodeInput (skolemNnf formula) =
      FangSkolemCore.decodeIndependentNnf formula := by
  induction formula with
  | Literal literal => exact congrArg Fang.QuantifiedFOF.Nnf.lit (skolemLiteral_decode literal)
  | True | False => rfl
  | And left right il ir | Or left right il ir =>
    simp only [skolemNnf, FangBinderRemovalCore.decodeInput, FangSkolemCore.decodeIndependentNnf,
      il, ir]
  | Forall id body ih | Exists id body ih =>
    simp only [skolemNnf, FangBinderRemovalCore.decodeInput, FangSkolemCore.decodeIndependentNnf, ih]

end FangQuantifiedPipeline
