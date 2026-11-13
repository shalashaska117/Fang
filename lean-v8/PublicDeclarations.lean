/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual whole-input Skolem success, with ordered source witnesses. -/
import DeclarationsTrace
import ValidationDeclarations
import CopyArities

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

theorem transform_declarations_success
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {before after : Transformer}
    {output : alloc.vec.Vec fang_quantified_fof_core.Nnf}
    (first : before.declaration.val = 0)
    (valid : UniversalValid before.universals) (empty : before.universals.active.val = 0)
    (success : transform_declarations declarations signature limits before = .ok (.Ok output, after)) :
    UniversalValid after.universals ∧ UniversalFrame before.universals after.universals ∧
      after.declaration.val = declarations.val.length ∧
      DeclarationTrace signature declarations.val before.functions.val.length output.val after.functions.val.length := by
  obtain ⟨lastValid, frame, last, targets, same, trace⟩ :=
    transform_declarations_loop_success declarations signature limits before _ after output
      (by rw [first]; omega) valid empty success
  simp [alloc.vec.Vec.new] at same
  subst targets
  simpa only [first, List.drop_zero] using And.intro lastValid (And.intro frame (And.intro last trace))

/-- The complete original signature is reserved before the first declaration.
    This successful-call theorem does not assert a sufficient resource budget,
    whole-call termination, or complete extended arity/origin inventories. -/
theorem skolemize_problem_success
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output)) :
    DeclarationsFrom signature declarations 0 ∧
      output.signature.predicates.val = signature.predicates.val ∧
      DeclarationTrace signature declarations.val signature.functions.val.length output.formulas.val
        output.signature.functions.val.length := by
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
        have sourceValid := (validate_declarations_success (by change 0 ≤ _; omega)
          (by change 0 ≤ _; omega) validatedEq).1
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
          simp only [bind_ok] at success
          obtain ⟨⟨predicatesResult, w2⟩, predicatesEq, success⟩ := (bind_success_iff _ _ _).mp success
          dsimp only [Aeneas.Std.uncurry] at success
          cases predicatesResult with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
          | Ok predicates =>
            have copiedPredicates := copy_arities_spec (alloc.vec.Vec.deref signature.predicates) limits w1
            rw [predicatesEq] at copiedPredicates
            simp only [spec_ok, ArityCopyPost] at copiedPredicates
            have predicateValues : predicates.val = signature.predicates.val := by
              simpa [alloc.vec.Vec.deref] using copiedPredicates.2.2.1
            simp only [bind_ok] at success
            obtain ⟨⟨formulasResult, state⟩, formulasEq, success⟩ := (bind_success_iff _ _ _).mp success
            dsimp only [Aeneas.Std.uncurry] at success
            cases formulasResult with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
            | Ok formulas =>
              have converted := transform_declarations_success (by simp) (by simp [UniversalValid])
                (by simp) formulasEq
              simp only [bind_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at success
              subst output
              refine ⟨sourceValid, predicateValues, ?_⟩
              simpa only [functionValues] using converted.2.2.2

theorem skolemize_problem_output_length
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output)) :
    output.formulas.val.length = declarations.val.length :=
  declarationTrace_length (skolemize_problem_success success).2.2

end FangSkolemCore
