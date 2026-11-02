/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent numeric-occurrence checker, separate from generated Rust. -/
import Equality

namespace Fang.Equality.Ordered

inductive Root where
  | argument : Nat → Root
  | equalityLeft
  | equalityRight
  deriving DecidableEq, Repr

/-- Select one numeric path after substitution. Fixed siblings retain order. -/
def focusTerm : Term → List Nat → Option (Term × TermContext)
  | term, [] => some (term, .hole)
  | .var _, _ :: _ => none
  | .app symbol arguments, index :: path => do
      let child ← arguments[index]?
      let (selected, context) ← focusTerm child path
      pure (selected, .app symbol (arguments.take index) context (arguments.drop (index + 1)))

def focusLiteral (literal : Literal) (root : Root) (path : List Nat) :
    Option (Term × LiteralContext) := do
  match literal.atom, root with
  | .predicate atom, .argument index =>
      let child ← atom.args[index]?
      let (selected, context) ← focusTerm child path
      pure (selected, .predicate literal.positive atom.pred
        (atom.args.take index) context (atom.args.drop (index + 1)))
  | .equal left right, .equalityLeft =>
      let (selected, context) ← focusTerm left path
      pure (selected, .equalityLeft literal.positive context right)
  | .equal left right, .equalityRight =>
      let (selected, context) ← focusTerm right path
      pure (selected, .equalityRight literal.positive left context)
  | _, _ => none

theorem split_at {α : Type} (values : List α) (index : Nat) (selected : α)
    (found : values[index]? = some selected) :
    values = values.take index ++ selected :: values.drop (index + 1) := by
  obtain ⟨bound, selectedEq⟩ := List.getElem?_eq_some_iff.mp found
  calc
    values = values.take (index + 1) ++ values.drop (index + 1) := (List.take_append_drop _ _).symm
    _ = _ := by rw [List.take_succ_eq_append_getElem bound, selectedEq]; simp

theorem focusTerm_plug (term : Term) (path : List Nat) (selected : Term) (context : TermContext)
    (accepted : focusTerm term path = some (selected, context)) : context.plug selected = term := by
  induction path generalizing term context with
  | nil => cases accepted; rfl
  | cons index rest ih =>
    cases term with
    | var id => simp [focusTerm] at accepted
    | app symbol arguments =>
      cases found : arguments[index]? with
      | none => simp [focusTerm, found] at accepted
      | some child =>
        cases focused : focusTerm child rest with
        | none => simp [focusTerm, found, focused] at accepted
        | some value =>
          rcases value with ⟨result, inner⟩
          simp only [focusTerm, found, focused, bind, Option.bind, pure] at accepted
          cases accepted
          simp only [TermContext.plug, ih child inner focused]
          exact congrArg (Term.app symbol) (split_at arguments index child found).symm

theorem focusLiteral_plug (literal : Literal) (root : Root) (path : List Nat)
    (selected : Term) (context : LiteralContext)
    (accepted : focusLiteral literal root path = some (selected, context)) :
    context.plug selected = literal := by
  cases literal with
  | mk positive atom =>
    cases atom with
    | predicate atom =>
      cases root with
      | equalityLeft | equalityRight => simp [focusLiteral] at accepted
      | argument index =>
        cases found : atom.args[index]? with
        | none => simp [focusLiteral, found] at accepted
        | some child =>
          cases focused : focusTerm child path with
          | none => simp [focusLiteral, found, focused] at accepted
          | some value =>
            rcases value with ⟨result, inner⟩
            simp only [focusLiteral, found, focused, bind, Option.bind, pure] at accepted
            cases accepted
            simp only [LiteralContext.plug, focusTerm_plug child path selected inner focused]
            have split := (split_at atom.args index child found).symm
            cases atom
            exact congrArg (fun arguments => Literal.mk positive (.predicate ⟨_, arguments⟩)) split
    | equal left right =>
      cases root with
      | argument index => simp [focusLiteral] at accepted
      | equalityLeft =>
        cases focused : focusTerm left path with
        | none => simp [focusLiteral, focused] at accepted
        | some value =>
          rcases value with ⟨result, inner⟩
          simp only [focusLiteral, focused, bind, Option.bind, pure] at accepted
          cases accepted
          simp only [LiteralContext.plug, focusTerm_plug left path selected inner focused]
      | equalityRight =>
        cases focused : focusTerm right path with
        | none => simp [focusLiteral, focused] at accepted
        | some value =>
          rcases value with ⟨result, inner⟩
          simp only [focusLiteral, focused, bind, Option.bind, pure] at accepted
          cases accepted
          simp only [LiteralContext.plug, focusTerm_plug right path selected inner focused]

end Fang.Equality.Ordered
