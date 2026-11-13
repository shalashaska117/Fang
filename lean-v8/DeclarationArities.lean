/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signature inventory through actual ordered declaration processing. -/
import TransformArities
import NormalizedArities
import PublicDeclarations

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

theorem transform_declarations_loop_arities
    (declarations : Slice Declaration) (signature : fang_quantified_fof_core.Signature)
    (limits : Limits) (before : Transformer) (formulas : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (after : Transformer) (output : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (_inside : before.declaration.val ≤ declarations.val.length)
    (valid : UniversalValid before.universals) (empty : before.universals.active.val = 0)
    (reserved : FunctionPrefix signature.functions before.functions)
    (previous : ∀ formula ∈ formulas.val, NnfArities before.functions formula)
    (success : transform_declarations_loop declarations signature limits before formulas =
      .ok (.Ok output, after)) :
    FunctionPrefix before.functions after.functions ∧
      (∀ formula ∈ output.val, NnfArities after.functions formula) ∧
      (IntroducedArities before.functions before.introduced →
        IntroducedArities after.functions after.introduced) := by
  unfold transform_declarations_loop at success
  dsimp only at success
  split at success
  next more =>
    have indexBound : before.declaration.val < declarations.val.length := by scalar_tac
    obtain ⟨⟨ticked, w⟩, tickEq, success⟩ := (bind_success_iff _ _ _).mp success
    dsimp only [Aeneas.Std.uncurry] at success
    cases ticked with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at success
      obtain ⟨declaration, declarationEq, success⟩ := (bind_success_iff _ _ _).mp success
      obtain ⟨coreLimits, remainingEq, success⟩ := (bind_success_iff _ _ _).mp success
      obtain ⟨normalizedResult, normalizedEq, success⟩ := (bind_success_iff _ _ _).mp success
      cases normalizedResult with
      | Err error =>
        simp [core.result.Result.map_err, P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
          Error.Core.constructor,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
      | Ok normalized =>
        simp only [core.result.Result.map_err, bind_ok] at success
        obtain ⟨⟨absorbed, w1⟩, absorbedEq, success⟩ := (bind_success_iff _ _ _).mp success
        dsimp only [Aeneas.Std.uncurry] at success
        cases absorbed with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
        | Ok value =>
          simp only [bind_ok] at success
          obtain ⟨⟨converted, state⟩, convertedEq, success⟩ := (bind_success_iff _ _ _).mp success
          dsimp only [Aeneas.Std.uncurry] at success
          cases converted with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
          | Ok target =>
            have prepared := actual_normalized_ready normalizedEq
            have ids : universalIds before.universals = [] := by simp [universalIds, empty]
            have convertedPost := transform_success (before := {before with work := w1}) valid
              (by simpa only [ids] using prepared.1) (prepared.2 _ empty) convertedEq
            have typed := transform_arities_success (before := {before with work := w1}) valid
              (by simpa only [ids] using prepared.1) (prepared.2 _ empty)
              (nnfArities_prefix reserved (actual_normalized_arities normalizedEq)) convertedEq
            have stateEmpty : state.universals.active.val = 0 := convertedPost.2.1.1.trans empty
            have stateDeclaration : state.declaration = before.declaration := convertedPost.2.2.1
            simp only [bind_ok] at success
            obtain ⟨⟨allocated, w2⟩, allocatedEq, success⟩ := (bind_success_iff _ _ _).mp success
            dsimp only [Aeneas.Std.uncurry] at success
            cases allocated with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
            | Ok value =>
              simp only [bind_ok] at success
              obtain ⟨pushed, pushedEq, success⟩ := (bind_success_iff _ _ _).mp success
              obtain ⟨next, nextEq, success⟩ := (bind_success_iff _ _ _).mp success
              have nextChecked := Usize.add_spec (x := state.declaration) (y := 1#usize) (by
                rw [stateDeclaration]
                have := declarations.property
                scalar_tac)
              rw [nextEq] at nextChecked
              simp only [spec_ok] at nextChecked
              have nextValue : next.val = before.declaration.val + 1 := by scalar_tac
              have accumulated : ∀ formula ∈ pushed.val, NnfArities state.functions formula := by
                intro formula member
                rw [push_success pushedEq, List.mem_append, List.mem_singleton] at member
                rcases member with old | rfl
                · exact nnfArities_prefix typed.1 (previous formula old)
                · exact typed.2.1
              obtain ⟨extension, outputTyped, origins⟩ :=
                transform_declarations_loop_arities declarations signature limits
                  {state with declaration := next, work := w2} pushed after output
                  (by dsimp only; omega) convertedPost.1 stateEmpty
                  (functionPrefix_trans reserved typed.1) accumulated success
              exact ⟨functionPrefix_trans typed.1 extension, outputTyped,
                fun initial => origins (typed.2.2 initial)⟩
  next done =>
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at success
    obtain ⟨rfl, rfl⟩ := success
    exact ⟨functionPrefix_refl _, previous, id⟩
termination_by declarations.val.length - before.declaration.val
decreasing_by omega

theorem transform_declarations_arities
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {before after : Transformer}
    {output : alloc.vec.Vec fang_quantified_fof_core.Nnf}
    (first : before.declaration.val = 0)
    (valid : UniversalValid before.universals) (empty : before.universals.active.val = 0)
    (reserved : FunctionPrefix signature.functions before.functions)
    (success : transform_declarations declarations signature limits before = .ok (.Ok output, after)) :
    FunctionPrefix before.functions after.functions ∧
      (∀ formula ∈ output.val, NnfArities after.functions formula) ∧
      (IntroducedArities before.functions before.introduced →
        IntroducedArities after.functions after.introduced) :=
  transform_declarations_loop_arities declarations signature limits before _ after output
    (by rw [first]; omega) valid empty reserved (by simp [alloc.vec.Vec.new]) success

/-- Successful execution alone establishes the output function inventory. The
    complete original table remains a prefix, including unused symbols. This
    is a generated-model theorem, not a native resource-sufficiency claim. -/
theorem skolemize_problem_arities
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output)) :
    FunctionPrefix signature.functions output.signature.functions ∧
      (∀ formula ∈ output.formulas.val, NnfArities output.signature.functions formula) ∧
      IntroducedArities output.signature.functions output.introduced := by
  unfold skolemize_problem at success
  dsimp only at success
  split at success
  next exceeded => simp at success
  next declarationsFit =>
    obtain ⟨maximum, castEq, success⟩ := (bind_success_iff _ _ _).mp success
    obtain ⟨functionLimit, minimumEq, success⟩ := (bind_success_iff _ _ _).mp success
    split at success
    next exceeded => simp at success
    next functionsFit =>
      simp only [Statistics.Insts.CoreDefaultDefault.default, bind_ok] at success
      obtain ⟨⟨validated, w⟩, validatedEq, success⟩ := (bind_success_iff _ _ _).mp success
      dsimp only [Aeneas.Std.uncurry] at success
      cases validated with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
      | Ok value =>
        cases value
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at success
        obtain ⟨⟨functionsResult, w1⟩, functionsEq, success⟩ := (bind_success_iff _ _ _).mp success
        dsimp only [Aeneas.Std.uncurry] at success
        cases functionsResult with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
        | Ok functions =>
          have copiedFunctions := copy_arities_spec (alloc.vec.Vec.deref signature.functions) limits w
          rw [functionsEq] at copiedFunctions
          simp only [spec_ok, ArityCopyPost] at copiedFunctions
          have functionValues : functions.val = signature.functions.val := by
            simpa [alloc.vec.Vec.deref] using copiedFunctions.2.2.1
          have reserved : FunctionPrefix signature.functions functions := ⟨[], by simpa using functionValues⟩
          simp only [bind_ok] at success
          obtain ⟨⟨predicatesResult, w2⟩, predicatesEq, success⟩ := (bind_success_iff _ _ _).mp success
          dsimp only [Aeneas.Std.uncurry] at success
          cases predicatesResult with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
          | Ok predicates =>
            simp only [bind_ok] at success
            obtain ⟨⟨formulasResult, state⟩, formulasEq, success⟩ := (bind_success_iff _ _ _).mp success
            dsimp only [Aeneas.Std.uncurry] at success
            cases formulasResult with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
            | Ok formulas =>
              have converted := transform_declarations_arities (by simp) (by simp [UniversalValid])
                (by simp) reserved formulasEq
              simp only [bind_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at success
              subst output
              exact ⟨functionPrefix_trans reserved converted.1, converted.2.1,
                converted.2.2 (by simp [IntroducedArities, alloc.vec.Vec.new])⟩

end FangSkolemCore
