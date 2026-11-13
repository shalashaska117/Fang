/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit of the naming proofs: the two results the replay uses are stated
   here again with their full types, and the axioms of every main result are
   printed here rather than by the modules that prove them. -/
import NamingEntry

open Aeneas Aeneas.Std Result fang_fof_core FangScopedFof FangNaming

/-- Obligations 1 and 3 for the clauses: fresh predicates from `next`, every clause
    predicate below the returned `next`, and every model of the block formula extended
    only from `next` on to a model of the clauses. -/
example {signature : Signature} {scope : VariableScope} (formula : Nnf) (threshold : Usize) (next : U32)
    (limits : Limits) (statistics : Statistics) (output : naming.Named)
    (valid : NnfScoped signature scope formula) (below : PredsBelow next.val (decodeNnf formula))
    (success : naming.name_then_clausify formula threshold next limits statistics = ok (.Ok output)) :
    next.val ≤ output.next.val ∧
      (∀ clause ∈ decodeClauses output.clauses.val, ∀ literal ∈ clause, literal.atom.pred < output.next.val) ∧
      ∀ {D : Type} [Nonempty D] (model : Fang.Interpretation D),
        (∀ valuation, (decodeNnf formula).Holds model valuation) →
        ∃ extended : Fang.Interpretation D, AgreeBelow next.val model extended ∧
          (decodeClauses output.clauses.val).Models extended :=
  name_then_clausify_spec formula threshold next limits statistics output valid below success

/-- Obligation 2 at the level of formulas: the renamed formula conjoined with its
    definitions holds in the extended interpretation whenever the input holds. -/
example {signature : Signature} {scope : VariableScope} (formula : Nnf) (threshold : Usize) (next : U32)
    (limits : Limits) (statistics : Statistics) (output : naming.Renamed)
    (valid : NnfScoped signature scope formula) (below : PredsBelow next.val (decodeNnf formula))
    (success : naming.name_nnf formula threshold next limits statistics = ok (.Ok output)) :
    next.val ≤ output.next.val ∧
      NnfScoped signature scope output.formula ∧
      PredsBelow output.next.val (decodeNnf output.formula) ∧
      ∀ {D : Type} [Nonempty D] (model : Fang.Interpretation D),
        (∀ valuation, (decodeNnf formula).Holds model valuation) →
        ∃ extended : Fang.Interpretation D, AgreeBelow next.val model extended ∧
          ∀ valuation, (decodeNnf output.formula).Holds extended valuation :=
  name_nnf_spec formula threshold next limits statistics output valid below success

#print axioms FangNaming.extend_agree
#print axioms FangNaming.extendOne_atom
#print axioms FangNaming.extend_definitions_hold
#print axioms FangNaming.insert_variable_spec
#print axioms FangNaming.collect_nnf_spec
#print axioms FangNaming.variable_terms_spec
#print axioms FangNaming.name_spec
#print axioms FangNaming.rename_spec
#print axioms FangNaming.name_nnf_loop_spec
#print axioms FangNaming.name_nnf_spec
#print axioms FangNaming.clauses_below
#print axioms FangNaming.name_then_clausify_spec
