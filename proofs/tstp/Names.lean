/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Invariant
import Init.Data.Nat.ToString

namespace Fang.TstpExport.BuilderProof

def LowerNames (names : List String) : Prop :=
  ∀ name ∈ names, Frontend.lowerName name = true

theorem statement_lower_names (fuel : Nat) :
    Frontend.PreservesClauseProperty LowerNames (Frontend.statement fuel) := by
  intro state clause final prior success
  obtain ⟨name, _, _, named, _, _, _, nameValid, _, names, _, tail⟩ :=
    Frontend.statement_success_decomposition success
  have history : final.clauseNames = state.clauseNames ++ [name] := by
    simpa only [names] using tail.clause_names
  intro other member
  rw [history] at member
  rcases List.mem_append.mp member with previous | added
  · exact prior other previous
  · simpa only [List.mem_singleton.mp added] using nameValid

theorem statements_lower_names (fuel : Nat) :
    Frontend.PreservesClauseProperty LowerNames (Frontend.statements fuel) := by
  induction fuel with
  | zero => exact Frontend.clauseProperty_fail LowerNames _
  | succ fuel ih =>
    simp only [Frontend.statements]
    apply Frontend.clauseProperty_bind (Frontend.clauseProperty_peek LowerNames)
    intro next
    split
    · exact Frontend.clauseProperty_pure LowerNames _
    · apply Frontend.clauseProperty_bind (statement_lower_names fuel)
      intro first
      exact Frontend.clauseProperty_bind ih (fun _ => Frontend.clauseProperty_pure LowerNames _)

theorem decoded_names (input : String) (problem : NamedProblem)
    (decoded : decodeNamed input = .ok problem) :
    problem.names.Nodup ∧ LowerNames problem.names := by
  obtain ⟨tokens, state, _, parsed, _, _, names⟩ := decodeNamed_success decoded
  rw [names]
  constructor
  · exact Frontend.statements_preserve_unique_clause_names _ _ _ _ (by simp) parsed
  · exact statements_lower_names _ _ _ _ (by simp [LowerNames]) parsed

inductive NameKind where
  | step | left | right
  deriving DecidableEq

def generatedName (kind : NameKind) (node : Nat) : String :=
  match kind with
  | .step => internalName node
  | .left => s!"fang:left:{node}"
  | .right => s!"fang:right:{node}"

def prefixChars : NameKind → List Char
  | .step => ['f', 'a', 'n', 'g', ':', 's', 't', 'e', 'p', ':']
  | .left => ['f', 'a', 'n', 'g', ':', 'l', 'e', 'f', 't', ':']
  | .right => ['f', 'a', 'n', 'g', ':', 'r', 'i', 'g', 'h', 't', ':']

theorem generated_name_chars (kind : NameKind) (node : Nat) :
    (generatedName kind node).toList = prefixChars kind ++ node.repr.toList := by
  cases kind <;>
    simp only [generatedName, internalName, String.toList_append] <;> rfl

theorem decimal_name_injective {left right : Nat} (equal : left.repr = right.repr) : left = right := by
  have characters := congrArg String.toList equal
  simp only [Nat.toList_repr] at characters
  have decoded := congrArg (fun chars => Nat.ofDigitChars 10 chars 0) characters
  simpa using decoded

theorem generated_name_injective {leftKind rightKind : NameKind} {left right : Nat}
    (equal : generatedName leftKind left = generatedName rightKind right) :
    leftKind = rightKind ∧ left = right := by
  have tags := congrArg (fun s : String => s.toList[5]?) equal
  have kind : leftKind = rightKind := by
    cases leftKind <;> cases rightKind <;> first
      | exact rfl
      | simp [generated_name_chars, prefixChars] at tags
  subst rightKind
  refine ⟨rfl, ?_⟩
  apply decimal_name_injective
  cases leftKind <;>
    simpa [generatedName, internalName, Nat.toString_eq_repr] using equal

theorem generated_name_not_lower (kind : NameKind) (node : Nat) :
    Frontend.lowerName (generatedName kind node) = false := by
  rw [Frontend.lowerName, generated_name_chars]
  cases kind <;> rfl

theorem source_generated_distinct (name : String) (kind : NameKind) (node : Nat)
    (valid : Frontend.lowerName name = true) : name ≠ generatedName kind node := by
  intro equal
  rw [equal, generated_name_not_lower] at valid
  contradiction

end Fang.TstpExport.BuilderProof
