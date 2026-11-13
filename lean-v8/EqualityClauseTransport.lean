/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked structural transport into the unchanged extracted equality bridge. -/
import ReservedInput
import ClauseConversion

open Aeneas Aeneas.Std

namespace FangQuantifiedEqualityReplay.Transport
open FangQuantifiedTransport

mutual
def encodeTerm : Fang.Term → Except FangQuantifiedTransport.Error fang_fof_equality_bridge.fang.syntax.Term
  | .var id => do pure (.Var (← checkedU32 id))
  | .app symbol arguments => do
    let symbol ← checkedU32 symbol
    let arguments ← checkedVec (← encodeTerms arguments)
    pure (.Fun symbol arguments)

def encodeTerms : List Fang.Term → Except FangQuantifiedTransport.Error (List fang_fof_equality_bridge.fang.syntax.Term)
  | [] => .ok []
  | term :: rest => do pure ((← encodeTerm term) :: (← encodeTerms rest))
end

def encodeLiteral (source : Fang.Literal) : Except FangQuantifiedTransport.Error FangEqualityBridge.OutputLiteral := do
  let predicate ← checkedU32 source.atom.pred
  let arguments ← checkedVec (← encodeTerms source.atom.args)
  pure ⟨source.positive, predicate, arguments⟩

def encodeLiterals : Fang.Clause → Except FangQuantifiedTransport.Error (List FangEqualityBridge.OutputLiteral)
  | [] => .ok []
  | literal :: rest => do pure ((← encodeLiteral literal) :: (← encodeLiterals rest))

def encodeClause (source : Fang.Clause) : Except FangQuantifiedTransport.Error (alloc.vec.Vec FangEqualityBridge.OutputLiteral) := do
  checkedVec (← encodeLiterals source)

mutual
theorem encodeTerm_decode (source : Fang.Term) {target} (success : encodeTerm source = .ok target) :
    FangEqualityBridge.decodeTerm target = source := by
  cases source with
  | var id =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    cases Except.ok.inj success
    exact congrArg Fang.Term.var (checkedU32_value encoded)
  | app symbol arguments =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    obtain ⟨terms, children, success⟩ := except_bind_success success
    obtain ⟨vector, packed, success⟩ := except_bind_success success
    cases Except.ok.inj success
    change Fang.Term.app actual.val (FangEqualityBridge.decodeVec vector) = .app symbol arguments
    rw [FangEqualityBridge.decodeVec_map, checkedVec_values packed,
      encodeTerms_decode arguments children, checkedU32_value encoded]

theorem encodeTerms_decode (source : List Fang.Term) {target}
    (success : encodeTerms source = .ok target) :
    target.map FangEqualityBridge.decodeTerm = source := by
  cases source with
  | nil => cases Except.ok.inj success; rfl
  | cons term rest =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    obtain ⟨tail, children, success⟩ := except_bind_success success
    cases Except.ok.inj success
    exact congrArg₂ List.cons (encodeTerm_decode term encoded) (encodeTerms_decode rest children)
end

theorem encodeLiteral_decode {source target} (success : encodeLiteral source = .ok target) :
    FangEqualityBridge.decodeOutput target = source := by
  obtain ⟨predicate, encoded, success⟩ := except_bind_success success
  obtain ⟨terms, children, success⟩ := except_bind_success success
  obtain ⟨vector, packed, success⟩ := except_bind_success success
  cases Except.ok.inj success
  simp only [FangEqualityBridge.decodeOutput, FangEqualityBridge.decodeVec_map,
    checkedVec_values packed, encodeTerms_decode _ children, checkedU32_value encoded]

theorem encodeLiterals_decode {source target} (success : encodeLiterals source = .ok target) :
    target.map FangEqualityBridge.decodeOutput = source := by
  induction source generalizing target with
  | nil => cases Except.ok.inj success; rfl
  | cons literal rest ih =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    obtain ⟨tail, children, success⟩ := except_bind_success success
    cases Except.ok.inj success
    exact congrArg₂ List.cons (encodeLiteral_decode encoded) (ih children)

theorem encodeClause_decode {source target} (success : encodeClause source = .ok target) :
    target.val.map FangEqualityBridge.decodeOutput = source := by
  obtain ⟨literals, encoded, packed⟩ := except_bind_success success
  rw [checkedVec_values packed]
  exact encodeLiterals_decode encoded

end FangQuantifiedEqualityReplay.Transport
