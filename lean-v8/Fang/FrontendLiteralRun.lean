/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Exact equations for the existing literal parser, used by grammar proofs.
-/
import Fang.FrontendTermGrammar

namespace Fang.Frontend

theorem position_run (state : State) :
    position state = .ok ((state.tokens.head?.map Token.offset).getD state.endOffset, state) := by
  cases shape : state.tokens <;>
    simp [position, shape, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]

theorem literal_run (fuel : Nat) (state : State) :
    literal fuel state = Except.bind
      (if state.tokens.head?.map Token.text == some "~" then do
          let (_, updated) ← expect "~" state
          pure (false, updated)
        else .ok (true, state))
      (fun (positive, beforeName) => do
        let offset := (beforeName.tokens.head?.map Token.offset).getD beforeName.endOffset
        let (name, consumed) ← consume beforeName
        let (_, validated) ← if !lowerName name then
          failAt offset s!"unsupported: expected a predicate, found '{name}'" consumed
          else .ok ((), consumed)
        let (id, reserved) ← reserveSymbol true name validated
        Except.bind (if reserved.tokens.head?.map Token.text == some "(" then do
            let (_, opened) ← expect "(" reserved
            let (args, afterArgs) ← terms fuel opened
            let (_, closed) ← expect ")" afterArgs
            pure (args, closed)
          else .ok ([], reserved)) (fun (args, beforeArity) => do
          let (_, updated) ← checkArity true id args.length offset beforeArity
          pure ({ positive, atom := { pred := id, args } }, updated))) := by
  simp only [literal, bind, pure, StateT.bind, peek_run, Except.pure, Except.bind]
  repeat' (simp_all [bind, pure, StateT.bind, StateT.pure,
      Except.bind, Except.pure, position_run, failAt_run] <;> first | rfl | split)
  all_goals split
  all_goals simp_all [bind, StateT.bind, Except.bind, peek_run, failAt_run]
  all_goals repeat' first | split | rfl
  all_goals simp_all [bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure]
  all_goals repeat' first | split | rfl
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all

#print axioms literal_run

end Fang.Frontend
