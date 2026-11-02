/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Successful-call traces for the actual declaration traversal. -/
import NormalizedReady

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

/-- A successful bind exposes a successful first call. This lemma makes no
    termination or success claim for calls without the stated equation. -/
theorem bind_success_iff {α β : Type} (input : Result α) (next : α → Result β) (out : β) :
    (input >>= next) = .ok out ↔ ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | ret value => simp
  | vis effect continuation => simp
  | div => simp

theorem push_success {α : Type} {before after : alloc.vec.Vec α} {value : α}
    (success : alloc.vec.Vec.push before value = .ok after) :
    after.val = before.val ++ [value] := by
  unfold alloc.vec.Vec.push at success
  dsimp only at success
  split at success
  · simp only [Result.ok.injEq] at success
    subst after
    simp
  · simp at success

/-- Each declaration has its own actual closed normalization call and variable
    scope. The function counter passes from one declaration to the next. -/
inductive DeclarationTrace (signature : fang_quantified_fof_core.Signature) :
    List Declaration → Nat → List fang_quantified_fof_core.Nnf → Nat → Prop where
  | nil (first : Nat) : DeclarationTrace signature [] first [] first
  | cons {declaration declarations first middle last target targets}
      (normalized : fang_quantified_fof_core.Normalized)
      (coreLimits : fang_quantified_fof_core.Limits)
      (normalization : fang_quantified_fof_core.rectify_normalize_closed declaration.formula
        declaration.positive signature coreLimits = .ok (.Ok normalized))
      (head : Fang.QuantifiedFOF.Skolem.Skolemized [] first (decodeNnf normalized.formula)
        (decodeNnf target) middle)
      (tail : DeclarationTrace signature declarations middle targets last) :
      DeclarationTrace signature (declaration :: declarations) first (target :: targets) last

theorem declarationTrace_length {signature declarations first targets last}
    (trace : DeclarationTrace signature declarations first targets last) :
    targets.length = declarations.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ _ _ ih => simp [ih]

theorem transform_declarations_loop_success
    (declarations : Slice Declaration) (signature : fang_quantified_fof_core.Signature)
    (limits : Limits) (before : Transformer) (formulas : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (after : Transformer) (output : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (inside : before.declaration.val ≤ declarations.val.length)
    (valid : UniversalValid before.universals) (empty : before.universals.active.val = 0)
    (success : transform_declarations_loop declarations signature limits before formulas =
      .ok (.Ok output, after)) :
    UniversalValid after.universals ∧ UniversalFrame before.universals after.universals ∧
      after.declaration.val = declarations.val.length ∧
      ∃ targets, output.val = formulas.val ++ targets ∧
        DeclarationTrace signature (declarations.val.drop before.declaration.val)
          before.functions.val.length targets after.functions.val.length := by
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
      have selected := Slice.index_usize_spec declarations before.declaration indexBound
      rw [declarationEq] at selected
      simp only [spec_ok] at selected
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
              have stepTrace : Fang.QuantifiedFOF.Skolem.Skolemized [] before.functions.val.length
                  (decodeNnf normalized.formula) (decodeNnf target) state.functions.val.length := by
                simpa only [ids] using convertedPost.2.2.2.2
              obtain ⟨finalValid, finalFrame, finalDeclaration, targets, outputEq, trace⟩ :=
                transform_declarations_loop_success declarations signature limits
                  {state with declaration := next, work := w2} pushed after output
                  (by dsimp only; omega) convertedPost.1 stateEmpty success
              refine ⟨finalValid, universalFrame_trans convertedPost.2.1 finalFrame,
                finalDeclaration, target :: targets, ?_, ?_⟩
              · rw [outputEq, push_success pushedEq]
                simp
              · have tail : declarations.val.drop before.declaration.val =
                    declaration :: declarations.val.drop next.val := by
                  rw [selected, nextValue]
                  exact List.drop_eq_getElem_cons indexBound
                rw [tail]
                exact DeclarationTrace.cons normalized coreLimits normalizedEq stepTrace trace
  next done =>
    have atEnd : before.declaration.val = declarations.val.length := by scalar_tac
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at success
    obtain ⟨rfl, rfl⟩ := success
    refine ⟨valid, universalFrame_refl _, atEnd, [], by simp, ?_⟩
    simp only [atEnd, List.drop_length]
    exact DeclarationTrace.nil _
termination_by declarations.val.length - before.declaration.val
decreasing_by omega

end FangSkolemCore
