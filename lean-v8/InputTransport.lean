/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked transport from independent numeric syntax into extracted Rust types.
   This converts representations; preprocessing remains the generated Rust code. -/
import InputScope

open Aeneas Aeneas.Std

namespace FangQuantifiedTransport

inductive Error where
  | identifierOverflow
  | wordOverflow
  | vectorOverflow
deriving DecidableEq, Repr

def checkedU32 (value : Nat) : Except Error U32 :=
  if bound : value ≤ U32.max then .ok (U32.ofNatCore value (by scalar_tac))
  else .error .identifierOverflow

def checkedUsize (value : Nat) : Except Error Usize :=
  if bound : value ≤ Usize.max then .ok (Usize.ofNatCore value (by scalar_tac))
  else .error .wordOverflow

def checkedVec {α : Type} (values : List α) : Except Error (alloc.vec.Vec α) :=
  if bound : values.length ≤ Usize.max then .ok ⟨Slice.from values bound⟩
  else .error .vectorOverflow

mutual
def encodeTerm : Fang.Term → Except Error fang_skolem_core.fang.syntax.Term
  | .var id => do
    let id ← checkedU32 id
    pure (.Var id)
  | .app symbol arguments => do
    let symbol ← checkedU32 symbol
    let terms ← encodeTerms arguments
    let arguments ← checkedVec terms
    pure (.Fun symbol arguments)

def encodeTerms : List Fang.Term → Except Error (List fang_skolem_core.fang.syntax.Term)
  | [] => .ok []
  | term :: rest => do
    let term ← encodeTerm term
    let rest ← encodeTerms rest
    pure (term :: rest)
end

def encodeFormula : Fang.QuantifiedFOF.Formula →
    Except Error fang_skolem_core.fang_quantified_fof_core.Formula
  | .atom atom => do
    let predicate ← checkedU32 atom.pred
    let terms ← encodeTerms atom.args
    let arguments ← checkedVec terms
    pure (.Atom predicate arguments)
  | .truth => .ok .True
  | .falsity => .ok .False
  | .neg body => do pure (.Not (← encodeFormula body))
  | .conj left right => do pure (.And (← encodeFormula left) (← encodeFormula right))
  | .disj left right => do pure (.Or (← encodeFormula left) (← encodeFormula right))
  | .implies left right => do pure (.Implies (← encodeFormula left) (← encodeFormula right))
  | .all id body => do pure (.Forall (← checkedU32 id) (← encodeFormula body))
  | .ex id body => do pure (.Exists (← checkedU32 id) (← encodeFormula body))

def encodeDeclaration (positive : Bool) (formula : Fang.QuantifiedFOF.Formula) :
    Except Error fang_skolem_core.Declaration := do
  pure ⟨← encodeFormula formula, positive⟩

def encodeArities : List Nat → Except Error (List Usize)
  | [] => .ok []
  | arity :: rest => do pure ((← checkedUsize arity) :: (← encodeArities rest))

def encodeSignature (functions predicates : List Nat) :
    Except Error fang_skolem_core.fang_quantified_fof_core.Signature := do
  let functions ← checkedVec (← encodeArities functions)
  let predicates ← checkedVec (← encodeArities predicates)
  pure ⟨functions, predicates⟩

theorem except_bind_success {α β : Type} {action : Except Error α}
    {next : α → Except Error β} {output : β}
    (success : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem checkedU32_value {source target} (success : checkedU32 source = .ok target) :
    target.val = source := by
  unfold checkedU32 at success
  split at success
  · cases Except.ok.inj success
    rfl
  · cases success

theorem checkedUsize_value {source target} (success : checkedUsize source = .ok target) :
    target.val = source := by
  unfold checkedUsize at success
  split at success
  · cases Except.ok.inj success
    rfl
  · cases success

theorem checkedVec_values {α : Type} {source : List α} {target : alloc.vec.Vec α}
    (success : checkedVec source = .ok target) : target.val = source := by
  unfold checkedVec at success
  split at success
  next bound =>
    cases Except.ok.inj success
    exact Slice.from_val source bound
  next outside => cases success

mutual
theorem encodeTerm_decode (source : Fang.Term) {target}
    (success : encodeTerm source = .ok target) :
    FangSkolemEmbeddedCore.decodeTerm target = source := by
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
    change Fang.Term.app actual.val (FangSkolemEmbeddedCore.decodeVec vector) = .app symbol arguments
    rw [FangSkolemEmbeddedCore.decodeVec_eq_map, checkedVec_values packed,
      encodeTerms_decode arguments children, checkedU32_value encoded]

theorem encodeTerms_decode (source : List Fang.Term) {target}
    (success : encodeTerms source = .ok target) :
    target.map FangSkolemEmbeddedCore.decodeTerm = source := by
  cases source with
  | nil => cases Except.ok.inj success; rfl
  | cons term rest =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    obtain ⟨tail, children, success⟩ := except_bind_success success
    cases Except.ok.inj success
    exact congrArg₂ List.cons (encodeTerm_decode term encoded) (encodeTerms_decode rest children)
end

theorem encodeFormula_decode (source : Fang.QuantifiedFOF.Formula) {target}
    (success : encodeFormula source = .ok target) :
    FangSkolemEmbeddedCore.decodeFormula target = source := by
  induction source generalizing target with
  | atom atom =>
    obtain ⟨predicate, encoded, success⟩ := except_bind_success success
    obtain ⟨terms, children, success⟩ := except_bind_success success
    obtain ⟨vector, packed, success⟩ := except_bind_success success
    cases Except.ok.inj success
    simp only [FangSkolemEmbeddedCore.decodeFormula, FangSkolemEmbeddedCore.decodeVec_eq_map,
      checkedVec_values packed, encodeTerms_decode atom.args children, checkedU32_value encoded]
  | truth | falsity => cases Except.ok.inj success; rfl
  | neg body ih =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    cases Except.ok.inj success
    exact congrArg Fang.QuantifiedFOF.Formula.neg (ih encoded)
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    obtain ⟨actualLeft, leftRun, success⟩ := except_bind_success success
    obtain ⟨actualRight, rightRun, success⟩ := except_bind_success success
    cases Except.ok.inj success
    simp only [FangSkolemEmbeddedCore.decodeFormula, il leftRun, ir rightRun]
  | all id body ih | ex id body ih =>
    obtain ⟨actualId, idRun, success⟩ := except_bind_success success
    obtain ⟨actualBody, bodyRun, success⟩ := except_bind_success success
    cases Except.ok.inj success
    simp only [FangSkolemEmbeddedCore.decodeFormula, checkedU32_value idRun, ih bodyRun]

theorem encodeDeclaration_decode {positive source target}
    (success : encodeDeclaration positive source = .ok target) :
    target.positive = positive ∧ FangSkolemEmbeddedCore.decodeFormula target.formula = source := by
  obtain ⟨formula, encoded, success⟩ := except_bind_success success
  cases Except.ok.inj success
  exact ⟨rfl, encodeFormula_decode source encoded⟩

theorem encodeArities_values (source : List Nat) {target}
    (success : encodeArities source = .ok target) : target.map (fun value => value.val) = source := by
  induction source generalizing target with
  | nil => cases Except.ok.inj success; rfl
  | cons arity rest ih =>
    obtain ⟨actual, encoded, success⟩ := except_bind_success success
    obtain ⟨tail, children, success⟩ := except_bind_success success
    cases Except.ok.inj success
    exact congrArg₂ List.cons (checkedUsize_value encoded) (ih children)

theorem encodeSignature_values {functions predicates target}
    (success : encodeSignature functions predicates = .ok target) :
    target.functions.val.map (fun value => value.val) = functions ∧
      target.predicates.val.map (fun value => value.val) = predicates := by
  obtain ⟨functionValues, functionsRun, success⟩ := except_bind_success success
  obtain ⟨actualFunctions, functionsPacked, success⟩ := except_bind_success success
  obtain ⟨predicateValues, predicatesRun, success⟩ := except_bind_success success
  obtain ⟨actualPredicates, predicatesPacked, success⟩ := except_bind_success success
  cases Except.ok.inj success
  exact ⟨by rw [checkedVec_values functionsPacked]; exact encodeArities_values functions functionsRun,
    by rw [checkedVec_values predicatesPacked]; exact encodeArities_values predicates predicatesRun⟩

end FangQuantifiedTransport
