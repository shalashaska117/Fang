/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Function arities through the actual Skolem traversal branches. -/
import SignatureInventory
import Transform

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

/-- Error classification and termination are supplied by TransformPost. This
    additional postcondition describes only a successful signature and output. -/
def TransformArityPost (before : Transformer)
    (answer : core.result.Result Nnf fang_skolem_core.Error × Transformer) : Prop :=
  match answer.1 with
  | .Ok value => FunctionPrefix before.functions answer.2.functions ∧
      NnfArities answer.2.functions value ∧
      (IntroducedArities before.functions before.introduced →
        IntroducedArities answer.2.functions answer.2.introduced)
  | .Err _ => True

theorem transform_literal_arities (before : Transformer) (literal : fang.syntax.Literal)
    (limits : Limits) (arities : LiteralArities before.functions literal) :
    Transformer.transform before (.Literal literal) limits ⦃ TransformArityPost before ⦄ := by
  unfold Transformer.transform
  apply spec_bind (tick_spec before.work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (allocate_spec _ 1#usize limits)
    intro answer allocated
    unfold AllocationAnswer at allocated
    split at allocated
    next storageFits =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
      simp only [Aeneas.Std.uncurry, bind_ok]
      apply spec_bind (copy_literal_spec literal limits _)
      rintro ⟨result, after⟩ ⟨monotone, outcome⟩
      dsimp only at outcome
      simp only [Aeneas.Std.uncurry]
      cases result with
      | Ok value =>
        subst value
        simp only [bind_ok, spec_ok, TransformArityPost, NnfArities]
        exact ⟨functionPrefix_refl _, arities, id⟩
      | Err error =>
        simp [TransformArityPost,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    next storageExceeded =>
      rw [allocated]
      simp [TransformArityPost, Aeneas.Std.uncurry,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  next exceeded =>
    rw [ticked]
    simp [TransformArityPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem transform_constant_arities (before : Transformer) (value : Bool) (limits : Limits) :
    Transformer.transform before (if value then .True else .False) limits
      ⦃ TransformArityPost before ⦄ := by
  cases value <;>
    (unfold Transformer.transform
     apply spec_bind (tick_spec before.work limits)
     intro answer ticked
     unfold TickAnswer at ticked
     split at ticked
     next fits =>
       obtain ⟨operation, rfl, operation_eq⟩ := ticked
       simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
       apply spec_bind (allocate_spec _ 1#usize limits)
       intro answer allocated
       unfold AllocationAnswer at allocated
       split at allocated
       next storageFits =>
         obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
         simp only [Aeneas.Std.uncurry, bind_ok, spec_ok, TransformArityPost, NnfArities]
         exact ⟨functionPrefix_refl _, trivial, id⟩
       next storageExceeded =>
         rw [allocated]
         simp [TransformArityPost, Aeneas.Std.uncurry,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
     next exceeded =>
       rw [ticked]
       simp [TransformArityPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])

theorem transform_binary_arities (before : Transformer) (left right : Nnf) (disjunction : Bool)
    (limits : Limits) (valid : UniversalValid before.universals)
    (arities : NnfArities before.functions left ∧ NnfArities before.functions right)
    (leftChecked : ∀ state : Transformer, UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals → NnfArities state.functions left →
      Transformer.transform state left limits ⦃ fun answer =>
        TransformPost state left answer ∧ TransformArityPost state answer ⦄)
    (rightChecked : ∀ state : Transformer, UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals → NnfArities state.functions right →
      Transformer.transform state right limits ⦃ fun answer =>
        TransformPost state right answer ∧ TransformArityPost state answer ⦄) :
    Transformer.transform before (if disjunction then .Or left right else .And left right) limits
      ⦃ TransformArityPost before ⦄ := by
  cases disjunction <;>
    (unfold Transformer.transform
     apply spec_bind (tick_spec before.work limits)
     intro answer ticked
     unfold TickAnswer at ticked
     split at ticked
     next fits =>
       obtain ⟨operation, rfl, operation_eq⟩ := ticked
       simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
       apply spec_bind (allocate_spec _ 1#usize limits)
       intro answer allocated
       unfold AllocationAnswer at allocated
       split at allocated
       next storageFits =>
         obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
         simp only [Aeneas.Std.uncurry, bind_ok]
         let advanced : Transformer := { before with work := { statistics := {
           operations := operation, allocated_nodes := nodes } } }
         apply spec_bind (leftChecked advanced valid rfl arities.1)
         rintro ⟨leftResult, intermediate⟩ ⟨leftPost, leftArity⟩
         obtain ⟨leftValid, leftFrame, leftDeclaration, leftOperations, leftOutcome⟩ := leftPost
         simp only [Aeneas.Std.uncurry]
         cases leftResult with
         | Err error =>
           simp [TransformArityPost,
             core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
         | Ok l =>
           obtain ⟨leftPrefix, leftTyped, leftOrigins⟩ := leftArity
           simp only [bind_ok]
           apply spec_bind (rightChecked intermediate leftValid (universalFrame_ids leftFrame)
             (nnfArities_prefix leftPrefix arities.2))
           rintro ⟨rightResult, after⟩ ⟨rightPost, rightArity⟩
           simp only [Aeneas.Std.uncurry]
           cases rightResult with
           | Err error =>
             simp [TransformArityPost,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
           | Ok r =>
             obtain ⟨rightPrefix, rightTyped, rightOrigins⟩ := rightArity
             simp only [bind_ok, spec_ok, TransformArityPost, NnfArities]
             exact ⟨functionPrefix_trans leftPrefix rightPrefix,
               ⟨nnfArities_prefix rightPrefix leftTyped, rightTyped⟩,
               fun initial => rightOrigins (leftOrigins initial)⟩
       next storageExceeded =>
         rw [allocated]
         simp [TransformArityPost, Aeneas.Std.uncurry,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
     next exceeded =>
       rw [ticked]
       simp [TransformArityPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])

theorem transform_universal_arities (before : Transformer) (binder : U32) (body : Nnf)
    (limits : Limits) (valid : UniversalValid before.universals)
    (room : before.universals.active.val < Usize.max) (arities : NnfArities before.functions body)
    (bodyChecked : ∀ state : Transformer, UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals ++ [binder.val] →
      NnfArities state.functions body →
      Transformer.transform state body limits ⦃ fun answer =>
        TransformPost state body answer ∧ TransformArityPost state answer ⦄) :
    Transformer.transform before (.Forall binder body) limits ⦃ TransformArityPost before ⦄ := by
  unfold Transformer.transform
  apply spec_bind (tick_spec before.work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (allocate_spec _ 1#usize limits)
    intro answer allocated
    unfold AllocationAnswer at allocated
    split at allocated
    next storageFits =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
      simp only [Aeneas.Std.uncurry, bind_ok]
      apply spec_bind (universals_push_spec before.universals binder limits _ valid room)
      rintro ⟨pushedResult, pushed, pushedWork⟩ ⟨pushedValid, pushedOperations, pushedStorage, pushedOutcome⟩
      dsimp only at pushedOutcome
      simp only [Aeneas.Std.uncurry]
      cases pushedResult with
      | Err error =>
        simp [TransformArityPost,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok returned =>
        obtain ⟨pushedDepth, pushedEntries, _, _⟩ := pushedOutcome
        have pushedIds := universals_pushed_ids binder valid pushedDepth pushedEntries
        simp only [bind_ok]
        apply spec_bind (bodyChecked { before with universals := pushed, work := pushedWork }
          pushedValid pushedIds arities)
        rintro ⟨bodyResult, inner⟩ ⟨innerPost, innerArity⟩
        simp only [Aeneas.Std.uncurry]
        apply spec_bind (universals_pop_spec inner.universals innerPost.1)
        rintro popped poppedPost
        cases bodyResult with
        | Err error =>
          simp [TransformArityPost,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok target =>
          simpa only [bind_ok, spec_ok, TransformArityPost, NnfArities] using innerArity
    next storageExceeded =>
      rw [allocated]
      simp [TransformArityPost, Aeneas.Std.uncurry,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  next exceeded =>
    rw [ticked]
    simp [TransformArityPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem transform_existential_arities (before : Transformer) (binder : U32) (body : Nnf)
    (limits : Limits) (valid : UniversalValid before.universals)
    (arities : NnfArities before.functions body)
    (bodyChecked : ∀ (state : Transformer) (replacement : fang.syntax.Term) (target : Nnf),
      UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals →
      decodeTerm replacement = .app before.functions.val.length
        ((universalIds before.universals).map Fang.Term.var) →
      SubstitutedNnf binder replacement true body target → NnfArities state.functions target →
      Transformer.transform state target limits ⦃ TransformArityPost state ⦄) :
    Transformer.transform before (.Exists binder body) limits ⦃ TransformArityPost before ⦄ := by
  unfold Transformer.transform
  apply spec_bind (tick_spec before.work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    let advanced : Transformer := { before with work := { statistics := {
      before.work.statistics with operations := operation } } }
    apply spec_bind (introduce_spec advanced binder limits valid)
    rintro ⟨introducedResult, introduced⟩ introduction
    have savedIntroduction := introduction
    obtain ⟨sameStack, sameDeclaration, introducedOperations, introducedStorage, introducedOutcome⟩ := introduction
    dsimp only [advanced] at sameStack
    have introducedValid : UniversalValid introduced.universals := by rw [sameStack]; exact valid
    have introducedIds : universalIds introduced.universals = universalIds before.universals := by rw [sameStack]
    simp only [Aeneas.Std.uncurry]
    cases introducedResult with
    | Err error =>
      simp [TransformArityPost,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok replacement =>
      have replacementDecoded := introduce_decoded savedIntroduction
      dsimp only [advanced] at replacementDecoded
      obtain ⟨functionTable, extension, replacementTyped, origins⟩ := introducePost_arities (before := advanced) valid savedIntroduction
      simp only [bind_ok]
      apply spec_bind (substitute_nnf_total body binder replacement true limits introduced.work)
      rintro ⟨substitutedResult, substitutedWork⟩ ⟨substitutedOperations, substitutedOutcome⟩
      dsimp only at substitutedOutcome
      simp only [Aeneas.Std.uncurry]
      cases substitutedResult with
      | Err error =>
        simp [TransformArityPost,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok target =>
        simp only [bind_ok]
        apply spec_mono (bodyChecked { introduced with work := substitutedWork } replacement target
          introducedValid introducedIds replacementDecoded substitutedOutcome
          (substituted_nnf_arities substitutedOutcome replacementTyped (nnfArities_prefix extension arities)))
        rintro ⟨result, after⟩ afterArity
        cases result with
        | Err error => trivial
        | Ok output =>
          obtain ⟨suffix, outputTyped, outputOrigins⟩ := afterArity
          exact ⟨functionPrefix_trans extension suffix, outputTyped,
            fun initial => outputOrigins (origins initial)⟩
  next exceeded =>
    rw [ticked]
    simp [TransformArityPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end FangSkolemCore
