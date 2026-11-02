/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Local meaning of printed equality rows: each row follows from its own
   parents. This replaces the whole-problem premise of Rows.render_valid,
   which no model of a refuted problem can satisfy. -/
import EqualityGroup

namespace Fang.QuantifiedEqualityTstp.Local
open TstpText Equality

/-- One checked step needs only its parent clauses, or the input clause it fetches. -/
theorem step_local {problem : Equality.Problem} {checked : List Equality.Clause} {step : Ordered.Step}
    {output : Equality.Clause} (accepted : Ordered.checkStep problem checked step = .ok output)
    {D : Type} (model : Interpretation D)
    (parents : ∀ parent ∈ step.parents, ∀ clause, checked[parent]? = some clause → clauseValid model clause)
    (inputs : ∀ index, step = .input index → ∀ clause, problem[index]? = some clause →
      clauseValid model clause) :
    clauseValid model output := by
  cases step with
  | input index =>
    simp only [Ordered.checkStep, Equality.checkStep] at accepted
    exact inputs index rfl output (fetch_exact _ _ _ _ accepted)
  | factor parent first second substitution claimed =>
    simp only [Ordered.checkStep, Equality.checkStep] at accepted
    cases parentResult : fetch checked parent (.parentIndex parent) with
    | error error => simp [parentResult, bind, Except.bind] at accepted
    | ok premise =>
      simp only [parentResult, bind, Except.bind] at accepted
      exact inferUnary_sound model premise claimed output _
        (parents parent (by simp [Ordered.Step.parents]) premise (fetch_exact _ _ _ _ parentResult))
        (requireClaim_exact _ _ _ accepted).1
  | equalityResolution parent before after left right substitution claimed =>
    simp only [Ordered.checkStep, Equality.checkStep] at accepted
    cases parentResult : fetch checked parent (.parentIndex parent) with
    | error error => simp [parentResult, bind, Except.bind] at accepted
    | ok premise =>
      simp only [parentResult, bind, Except.bind] at accepted
      exact inferUnary_sound model premise claimed output _
        (parents parent (by simp [Ordered.Step.parents]) premise (fetch_exact _ _ _ _ parentResult))
        (requireClaim_exact _ _ _ accepted).1
  | resolution left leftPosition right rightPosition substitution claimed =>
    simp only [Ordered.checkStep, Equality.checkStep] at accepted
    cases leftResult : fetch checked left (.parentIndex left) with
    | error error => simp [leftResult, bind, Except.bind] at accepted
    | ok leftParent =>
      simp only [leftResult, bind, Except.bind] at accepted
      cases rightResult : fetch checked right (.parentIndex right) with
      | error error => simp [rightResult] at accepted
      | ok rightParent =>
        simp only [rightResult] at accepted
        exact inferBinary_sound model leftParent rightParent claimed output _
          (parents left (by simp [Ordered.Step.parents]) leftParent (fetch_exact _ _ _ _ leftResult))
          (parents right (by simp [Ordered.Step.parents]) rightParent (fetch_exact _ _ _ _ rightResult))
          (requireClaim_exact _ _ _ accepted).1
  | paramodulation source target witness claimed =>
    simp only [Ordered.checkStep] at accepted
    cases sourceResult : fetch checked source (.parentIndex source) with
    | error error => simp [sourceResult, bind, Except.bind] at accepted
    | ok sourceClause =>
      simp only [sourceResult, bind, Except.bind] at accepted
      cases targetResult : fetch checked target (.parentIndex target) with
      | error error => simp [targetResult] at accepted
      | ok targetClause =>
        simp only [targetResult] at accepted
        exact Ordered.infer_sound model sourceClause targetClause output witness
          (parents source (by simp [Ordered.Step.parents]) sourceClause (fetch_exact _ _ _ _ sourceResult))
          (parents target (by simp [Ordered.Step.parents]) targetClause (fetch_exact _ _ _ _ targetResult))
          (requireClaim_exact _ _ _ accepted).1

/-- The TSTP `status(thm)` meaning of one printed row, over all source models.
    An inference row follows from the named clauses of its parent rows. An
    input row follows from the prepared problem, which is exactly what the
    group row states (`Group.groupText_spec`). -/
theorem row_local {input proof limits maximumPredicates maximumLiterals output}
    (built : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {leading : List Derivation.Row} {value : Derivation.Row} {rest : List Derivation.Row}
    (position : Derivation.rows output = leading ++ value :: rest)
    {names : Body.Names} {named : List EqualitySource.Literal} (same : Body.NamedClause names value.2 named)
    {D : Type} (model : Source.Interpretation D) (label : String)
    (parentsPrinted : ∀ parent ∈ value.1.parents, ∀ row, leading[parent]? = some row →
      ∃ parentNamed, Body.NamedClause names row.2 parentNamed)
    (parents : ∀ parent ∈ value.1.parents, ∀ row, leading[parent]? = some row →
      ∀ parentNamed, Body.NamedClause names row.2 parentNamed →
        (EqualitySource.Clause.mk "" parentNamed).Valid model)
    (group : ∀ index, value.1 = .input index →
      Equality.models (tableModel names.view model) output.prepared.problem) :
    (EqualitySource.Clause.mk label named).Valid model := by
  rw [Group.namedClause_valid_iff same model label]
  apply step_local (Derivation.build_row_checked built position) (tableModel names.view model)
  · intro parent member clause found
    rw [List.getElem?_map] at found
    cases rowAt : leading[parent]? with
    | none => simp [rowAt] at found
    | some row =>
      simp only [rowAt, Option.map_some, Option.some.injEq] at found
      subst clause
      obtain ⟨parentNamed, parentSame⟩ := parentsPrinted parent member row rowAt
      exact (Group.namedClause_valid_iff parentSame model "").mp
        (parents parent member row rowAt parentNamed parentSame)
  · intro index isInput clause found
    exact group index isInput clause (List.mem_iff_getElem?.mpr ⟨index, found⟩)

#print axioms Fang.QuantifiedEqualityTstp.Local.step_local
#print axioms Fang.QuantifiedEqualityTstp.Local.row_local

end Fang.QuantifiedEqualityTstp.Local
