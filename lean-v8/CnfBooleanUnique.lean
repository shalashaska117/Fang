/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanScope
import FofProblemUnique

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

def AtomicHeadValid (kind : Kind) : Prop :=
  HeadValid kind ∨ kind = .legacy .truth ∨ kind = .legacy .falsity

theorem atomic_starts {input value rest} (parsed : AtomicTokens input value rest) :
    ∃ token tail, input = token :: tail ∧ AtomicHeadValid token.kind := by
  cases parsed with
  | truth kind => exact ⟨_, _, rfl, Or.inr (Or.inl kind)⟩
  | falsity kind => exact ⟨_, _, rfl, Or.inr (Or.inr kind)⟩
  | ordinary parsed =>
    obtain ⟨token, tail, rfl, valid⟩ := atom_starts parsed
    exact ⟨token, tail, rfl, Or.inl valid⟩

theorem atomic_head_valid {token tail value rest}
    (parsed : AtomicTokens (token :: tail) value rest) : AtomicHeadValid token.kind := by
  obtain ⟨_, _, shape, valid⟩ := atomic_starts parsed
  cases shape
  exact valid

theorem atomic_unique {input left leftRest right rightRest}
    (first : AtomicTokens input left leftRest) (second : AtomicTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | truth kind =>
    cases second with
    | truth _ => exact ⟨rfl, rfl⟩
    | falsity other => simp_all
    | ordinary parsed =>
      have valid := atom_head_valid parsed
      simp_all [HeadValid, FullFof.atomic]
  | falsity kind =>
    cases second with
    | truth other => simp_all
    | falsity _ => exact ⟨rfl, rfl⟩
    | ordinary parsed =>
      have valid := atom_head_valid parsed
      simp_all [HeadValid, FullFof.atomic]
  | ordinary parsed =>
    cases second with
    | truth kind =>
      have valid := atom_head_valid parsed
      simp_all [HeadValid, FullFof.atomic]
    | falsity kind =>
      have valid := atom_head_valid parsed
      simp_all [HeadValid, FullFof.atomic]
    | ordinary other => exact atom_unique parsed other

theorem wrappedAtom_unique {input left leftRest right rightRest}
    (first : WrappedAtomicTokens input left leftRest)
    (second : WrappedAtomicTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | bare parsed =>
    cases second with
    | bare other => exact atomic_unique parsed other
    | paren kind _ _ =>
      have valid := atomic_head_valid parsed
      simp_all [AtomicHeadValid, HeadValid, FullFof.atomic, Punct]
  | paren kind parsed closing =>
    cases second with
    | bare other =>
      have valid := atomic_head_valid other
      simp_all [AtomicHeadValid, HeadValid, FullFof.atomic, Punct]
    | paren _ other _ =>
      obtain ⟨rfl, same⟩ := atomic_unique parsed other
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      exact ⟨rfl, rfl⟩

theorem literal_starts {input value rest} (parsed : LiteralTokens input value rest) :
    ∃ token tail, input = token :: tail ∧ (AtomicHeadValid token.kind ∨ Punct token '~') := by
  cases parsed with
  | positive parsed =>
    obtain ⟨token, tail, rfl, valid⟩ := atomic_starts parsed
    exact ⟨token, tail, rfl, Or.inl valid⟩
  | negative kind _ _ => exact ⟨_, _, rfl, Or.inr kind⟩

theorem literal_unique {input left leftRest right rightRest}
    (first : LiteralTokens input left leftRest) (second : LiteralTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | positive parsed =>
    cases second with
    | positive other => exact atomic_unique parsed other
    | negative kind _ _ =>
      have valid := atomic_head_valid parsed
      simp_all [AtomicHeadValid, HeadValid, FullFof.atomic, Punct]
  | negative kind parsed atomicValue =>
    cases second with
    | positive other =>
      have valid := atomic_head_valid other
      simp_all [AtomicHeadValid, HeadValid, FullFof.atomic, Punct]
    | negative _ other _ =>
      obtain ⟨same, rfl⟩ := wrappedAtom_unique parsed other
      exact ⟨congrArg Formula.neg same, rfl⟩

theorem disjunction_unique {input left leftRest right rightRest}
    (first : DisjunctionTokens input left leftRest) (second : DisjunctionTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | one parsed noBar =>
    cases second with
    | one other _ =>
      obtain ⟨rfl, rfl⟩ := literal_unique parsed other
      exact ⟨rfl, rfl⟩
    | more other bar _ =>
      have rest := (literal_unique parsed other).2
      simp [rest, isChar] at noBar
      exact False.elim (noBar bar)
  | more parsed bar tail ih =>
    cases second with
    | one other noBar =>
      have rest := (literal_unique parsed other).2
      simp [← rest, isChar] at noBar
      exact False.elim (noBar bar)
    | more other _ others =>
      obtain ⟨rfl, rest⟩ := literal_unique parsed other
      obtain ⟨rfl, rfl⟩ := List.cons.inj rest
      obtain ⟨rfl, rfl⟩ := ih others
      exact ⟨rfl, rfl⟩

theorem disjunction_head_valid {token input values rest}
    (parsed : DisjunctionTokens (token :: input) values rest) : AtomicHeadValid token.kind ∨ Punct token '~' := by
  cases parsed with
  | one first _ | more first _ _ =>
    obtain ⟨_, _, shape, valid⟩ := literal_starts first
    cases shape
    exact valid

theorem clause_unique {input left leftRest right rightRest}
    (first : ClauseTokens input left leftRest) (second : ClauseTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | bare parsed =>
    cases second with
    | bare other => exact disjunction_unique parsed other
    | paren opening _ _ =>
      have valid := disjunction_head_valid parsed
      simp_all [AtomicHeadValid, HeadValid, FullFof.atomic, Punct]
  | paren opening parsed closing ih =>
    cases second with
    | bare other =>
      have valid := disjunction_head_valid other
      simp_all [AtomicHeadValid, HeadValid, FullFof.atomic, Punct]
    | paren _ other _ =>
      obtain ⟨rfl, same⟩ := ih other
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      exact ⟨rfl, rfl⟩

theorem body_unique {input left leftRest right rightRest} (kind : BodyKind left = BodyKind right)
    (first : BodyTokens input left leftRest) (second : BodyTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | fof parsed =>
    cases second with
    | fof other =>
      obtain ⟨rfl, rfl⟩ := formula_unique parsed other
      exact ⟨rfl, rfl⟩
    | cnf _ => simp [BodyKind] at kind
  | cnf parsed =>
    cases second with
    | fof _ => simp [BodyKind] at kind
    | cnf other =>
      obtain ⟨rfl, rfl⟩ := clause_unique parsed other
      exact ⟨rfl, rfl⟩

end Fang.TptpCandidate.FullFof.CnfBoolean
