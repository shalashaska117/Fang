/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The actual validated rectifier/NNF result preserves the function signature. -/
import SignatureInventory
import NormalizedReady

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

inductive DecodedTermArities (functions : alloc.vec.Vec Usize) : Fang.Term → Prop where
  | var (id : Nat) : DecodedTermArities functions (.var id)
  | app (symbol : Nat) (arguments : List Fang.Term)
      (arity : ∃ inside : symbol < functions.val.length, functions.val[symbol].val = arguments.length)
      (children : ∀ term ∈ arguments, DecodedTermArities functions term) :
      DecodedTermArities functions (.app symbol arguments)

theorem termArities_decoded {functions : alloc.vec.Vec Usize} {term : fang.syntax.Term}
    (valid : TermArities functions term) :
    DecodedTermArities functions (FangSkolemEmbeddedCore.decodeTerm term) := by
  induction valid with
  | var id => exact .var id.val
  | fun_ symbol arguments arity children ih =>
    simp only [FangSkolemEmbeddedCore.decodeTerm, FangSkolemEmbeddedCore.decodeVec_eq_map]
    refine .app symbol.val _ ?_ ?_
    · simpa only [List.length_map, FunctionArity] using arity
    · intro term member
      obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp present
      exact same ▸ ih i hi

theorem termArities_of_decoded {functions : alloc.vec.Vec Usize} {decoded : Fang.Term}
    (valid : DecodedTermArities functions decoded) (term : fang.syntax.Term)
    (same : FangSkolemEmbeddedCore.decodeTerm term = decoded) : TermArities functions term := by
  induction valid generalizing term with
  | var id =>
    cases term with
    | Var other => exact .var other
    | Fun symbol arguments => simp [FangSkolemEmbeddedCore.decodeTerm] at same
  | app symbol arguments arity children ih =>
    cases term with
    | Var id => simp [FangSkolemEmbeddedCore.decodeTerm] at same
    | Fun actual actualArguments =>
      simp only [FangSkolemEmbeddedCore.decodeTerm, Fang.Term.app.injEq] at same
      obtain ⟨symbolEq, argumentEq⟩ := same
      rw [FangSkolemEmbeddedCore.decodeVec_eq_map] at argumentEq
      have length := congrArg List.length argumentEq
      simp only [List.length_map] at length
      apply TermArities.fun_
      · simpa only [FunctionArity, symbolEq, length] using arity
      · intro i inside
        apply ih (FangSkolemEmbeddedCore.decodeTerm actualArguments.val[i])
        · rw [← argumentEq]
          exact List.mem_map.mpr ⟨actualArguments.val[i], List.getElem_mem inside, rfl⟩
        · rfl

theorem scopedTerm_arities {signature : fang_quantified_fof_core.Signature} {allowed : U32 → Prop}
    {term : fang.syntax.Term} (valid : FangSkolemEmbeddedCore.ScopedTerm signature allowed term) :
    TermArities signature.functions term := by
  induction valid with
  | var id member => exact .var id
  | fun_ symbol arguments arity children ih => exact .fun_ symbol arguments arity ih

def DecodedFormulaArities (functions : alloc.vec.Vec Usize) : Fang.QuantifiedFOF.Formula → Prop
  | .atom atom => ∀ term ∈ atom.args, DecodedTermArities functions term
  | .truth | .falsity => True
  | .neg body | .all _ body | .ex _ body => DecodedFormulaArities functions body
  | .conj left right | .disj left right | .implies left right =>
      DecodedFormulaArities functions left ∧ DecodedFormulaArities functions right

def DecodedNnfArities (functions : alloc.vec.Vec Usize) : Fang.QuantifiedFOF.Nnf → Prop
  | .lit literal => ∀ term ∈ literal.atom.args, DecodedTermArities functions term
  | .truth | .falsity => True
  | .all _ body | .ex _ body => DecodedNnfArities functions body
  | .conj left right | .disj left right =>
      DecodedNnfArities functions left ∧ DecodedNnfArities functions right

theorem validFormula_arities {signature : fang_quantified_fof_core.Signature}
    {allowed : U32 → Prop} {formula : fang_quantified_fof_core.Formula}
    (valid : FangSkolemEmbeddedCore.FormulaValid signature allowed formula) :
    DecodedFormulaArities signature.functions (FangSkolemEmbeddedCore.decodeFormula formula) := by
  induction formula generalizing allowed with
  | Atom predicate arguments =>
    intro term member
    rw [FangSkolemEmbeddedCore.decodeVec_eq_map] at member
    obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, inside, same⟩ := List.mem_iff_getElem.mp present
    apply termArities_decoded
    rw [← same]
    exact scopedTerm_arities (valid.2 i inside)
  | True | False => trivial
  | Not body ih => exact ih valid
  | And left right il ir | Or left right il ir | Implies left right il ir =>
    exact ⟨il valid.1, ir valid.2⟩
  | Forall id body ih | Exists id body ih => exact ih valid

theorem decoded_nnf_arities {functions : alloc.vec.Vec Usize} (formula : Fang.QuantifiedFOF.Formula)
    (valid : DecodedFormulaArities functions formula) (positive : Bool) :
    DecodedNnfArities functions (formula.nnf positive) := by
  induction formula generalizing positive with
  | atom atom => exact valid
  | truth | falsity => cases positive <;> trivial
  | neg body ih => exact ih valid (!positive)
  | conj left right il ir | disj left right il ir =>
    cases positive <;> exact ⟨il valid.1 _, ir valid.2 _⟩
  | implies left right il ir =>
    cases positive <;> exact ⟨il valid.1 _, ir valid.2 _⟩
  | all id body ih | ex id body ih => cases positive <;> exact ih valid _

theorem nnfArities_of_decoded {functions : alloc.vec.Vec Usize} (formula : fang_quantified_fof_core.Nnf)
    (valid : DecodedNnfArities functions (FangSkolemEmbeddedCore.decodeNnf formula)) :
    NnfArities functions formula := by
  induction formula with
  | Literal literal =>
    intro i inside
    apply termArities_of_decoded (valid _ ?_) _ rfl
    change FangSkolemEmbeddedCore.decodeTerm literal.arguments.val[i] ∈
      FangSkolemEmbeddedCore.decodeVec literal.arguments
    rw [FangSkolemEmbeddedCore.decodeVec_eq_map]
    exact List.mem_map.mpr ⟨literal.arguments.val[i], List.getElem_mem inside, rfl⟩
  | True | False => trivial
  | And left right il ir | Or left right il ir => exact ⟨il valid.1, ir valid.2⟩
  | Forall id body ih | Exists id body ih => exact ih valid

theorem actual_normalized_arities {source : fang_quantified_fof_core.Formula}
    {positive : Bool} {signature : fang_quantified_fof_core.Signature}
    {limits : fang_quantified_fof_core.Limits} {output : fang_quantified_fof_core.Normalized}
    (success : fang_quantified_fof_core.rectify_normalize_closed source positive signature limits = .ok (.Ok output)) :
    NnfArities signature.functions output.formula := by
  have checked := FangSkolemEmbeddedCore.normalized_witness_spec source positive signature limits
  rw [success] at checked
  simp only [spec_ok, FangSkolemEmbeddedCore.NormalizedWitness] at checked
  obtain ⟨sourceValid, target, count, renamed, normalized⟩ := checked
  apply nnfArities_of_decoded
  rw [normalized]
  exact decoded_nnf_arities _
    (validFormula_arities (FangSkolemEmbeddedCore.rectified_signature renamed signature _ sourceValid)) positive

end FangSkolemCore
