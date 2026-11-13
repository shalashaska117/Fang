/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Function-arity inventory for actual Skolem introduction and substitution. -/
import Introduce
import SubstituteNnf

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

/-- A prefix preserves every original symbol ID and arity. -/
def FunctionPrefix (before after : alloc.vec.Vec Usize) : Prop :=
  ∃ appended, after.val = before.val ++ appended

def FunctionArity (functions : alloc.vec.Vec Usize) (symbol : U32) (count : Nat) : Prop :=
  ∃ inside : symbol.val < functions.val.length, functions.val[symbol.val].val = count

inductive TermArities (functions : alloc.vec.Vec Usize) : fang.syntax.Term → Prop where
  | var (id : U32) : TermArities functions (.Var id)
  | fun_ (symbol : U32) (arguments : alloc.vec.Vec fang.syntax.Term)
      (arity : FunctionArity functions symbol arguments.val.length)
      (children : ∀ i (inside : i < arguments.val.length), TermArities functions arguments.val[i]) :
      TermArities functions (.Fun symbol arguments)

def LiteralArities (functions : alloc.vec.Vec Usize) (literal : fang.syntax.Literal) : Prop :=
  ∀ i (inside : i < literal.arguments.val.length), TermArities functions literal.arguments.val[i]

def NnfArities (functions : alloc.vec.Vec Usize) : Nnf → Prop
  | .Literal literal => LiteralArities functions literal
  | .True | .False => True
  | .And left right | .Or left right => NnfArities functions left ∧ NnfArities functions right
  | .Forall _ body | .Exists _ body => NnfArities functions body

theorem functionPrefix_refl (functions : alloc.vec.Vec Usize) : FunctionPrefix functions functions :=
  ⟨[], by simp⟩

theorem functionPrefix_trans {first middle last : alloc.vec.Vec Usize}
    (left : FunctionPrefix first middle) (right : FunctionPrefix middle last) :
    FunctionPrefix first last := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := right
  exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

theorem functionArity_prefix {before after : alloc.vec.Vec Usize} {symbol : U32} {count : Nat}
    (extension : FunctionPrefix before after) (arity : FunctionArity before symbol count) :
    FunctionArity after symbol count := by
  obtain ⟨appended, same⟩ := extension
  obtain ⟨inside, arity⟩ := arity
  have bound : symbol.val < after.val.length := by rw [same, List.length_append]; omega
  refine ⟨bound, ?_⟩
  simpa only [same, List.getElem_append_left inside] using arity

theorem termArities_prefix {before after : alloc.vec.Vec Usize} {term : fang.syntax.Term}
    (extension : FunctionPrefix before after) (valid : TermArities before term) :
    TermArities after term := by
  induction valid with
  | var id => exact .var id
  | fun_ symbol arguments arity children ih =>
    exact .fun_ symbol arguments (functionArity_prefix extension arity) ih

theorem literalArities_prefix {before after : alloc.vec.Vec Usize} {literal : fang.syntax.Literal}
    (extension : FunctionPrefix before after) (valid : LiteralArities before literal) :
    LiteralArities after literal := fun i inside => termArities_prefix extension (valid i inside)

theorem nnfArities_prefix {before after : alloc.vec.Vec Usize} {formula : Nnf}
    (extension : FunctionPrefix before after) (valid : NnfArities before formula) :
    NnfArities after formula := by
  induction formula with
  | Literal literal => exact literalArities_prefix extension valid
  | True | False => trivial
  | And left right il ir | Or left right il ir => exact ⟨il valid.1, ir valid.2⟩
  | Forall id body ih | Exists id body ih => exact ih valid

theorem substituted_term_arities {functions : alloc.vec.Vec Usize} {binder replacement source target}
    (related : SubstitutedTerm binder replacement source target)
    (replacementValid : TermArities functions replacement) (sourceValid : TermArities functions source) :
    TermArities functions target := by
  induction related with
  | bound => exact replacementValid
  | free id different => exact .var id
  | fun_ symbol arguments target length children ih =>
    cases sourceValid with
    | fun_ _ _ arity valid =>
      apply TermArities.fun_ symbol target
      · simpa only [length] using arity
      · intro i inside
        exact ih i (by omega) inside (valid i (by omega))

theorem substituted_literal_arities {functions : alloc.vec.Vec Usize} {binder replacement source target}
    (related : SubstitutedLiteral binder replacement source target)
    (replacementValid : TermArities functions replacement) (sourceValid : LiteralArities functions source) :
    LiteralArities functions target := by
  obtain ⟨positive, predicate, length, children⟩ := related
  intro i inside
  exact substituted_term_arities (children i (by omega) inside) replacementValid (sourceValid i (by omega))

theorem substituted_nnf_arities {functions : alloc.vec.Vec Usize} {binder replacement active source target}
    (related : SubstitutedNnf binder replacement active source target)
    (replacementValid : TermArities functions replacement) (sourceValid : NnfArities functions source) :
    NnfArities functions target := by
  induction related with
  | literalOn child => exact substituted_literal_arities child replacementValid sourceValid
  | literalOff => exact sourceValid
  | truth | falsity => trivial
  | conjunction left right il ir | disjunction left right il ir =>
    exact ⟨il sourceValid.1, ir sourceValid.2⟩
  | universal child ih | existential child ih => exact ih sourceValid

def IntroducedArity (functions : alloc.vec.Vec Usize) (entry : Introduced) : Prop :=
  FunctionArity functions entry.function entry.universals.val.length

def IntroducedArities (functions : alloc.vec.Vec Usize) (entries : alloc.vec.Vec Introduced) : Prop :=
  ∀ entry ∈ entries.val, IntroducedArity functions entry

theorem introducedArities_prefix {before after : alloc.vec.Vec Usize} {entries : alloc.vec.Vec Introduced}
    (extension : FunctionPrefix before after) (valid : IntroducedArities before entries) :
    IntroducedArities after entries := fun entry member => functionArity_prefix extension (valid entry member)

/-- The exact emitted replacement and appended metadata have the recorded
    active-prefix arity. This does not validate the incoming formula or its IDs. -/
theorem introducePost_arities {before after : Transformer} {binder : U32}
    {term : fang.syntax.Term}
    (stack : before.universals.active.val ≤ before.universals.entries.val.length)
    (checked : IntroducePost before binder (.Ok term, after)) :
    after.functions.val = before.functions.val ++ [before.universals.active] ∧
    FunctionPrefix before.functions after.functions ∧
    TermArities after.functions term ∧
    (IntroducedArities before.functions before.introduced → IntroducedArities after.functions after.introduced) := by
  simp only [IntroducePost] at checked
  obtain ⟨universals, declaration, operations, storage, symbol, arguments, dependencies,
    rfl, symbolId, argumentsEq, dependenciesEq, functionsEq, introducedEq, operationEq, storageEq⟩ := checked
  have extension : FunctionPrefix before.functions after.functions := ⟨[before.universals.active], functionsEq⟩
  have argumentLength : arguments.val.length = before.universals.active.val := by
    rw [argumentsEq, List.length_map, List.length_take]
    exact Nat.min_eq_left stack
  have dependencyLength : dependencies.val.length = before.universals.active.val := by
    rw [dependenciesEq, List.length_take]
    exact Nat.min_eq_left stack
  have arity : FunctionArity after.functions symbol before.universals.active.val := by
    have inside : symbol.val < after.functions.val.length := by
      rw [functionsEq, List.length_append, List.length_singleton, symbolId]
      omega
    refine ⟨inside, ?_⟩
    simp [functionsEq, symbolId]
  refine ⟨functionsEq, extension, ?_, ?_⟩
  · apply TermArities.fun_ symbol arguments
    · simpa only [argumentLength] using arity
    · intro i inside
      have member := List.getElem_mem inside
      have mapped : arguments.val[i] ∈
          (before.universals.entries.val.take before.universals.active.val).map fang.syntax.Term.Var := by
        rw [← argumentsEq]
        exact member
      obtain ⟨id, _, equal⟩ := List.mem_map.mp mapped
      rw [← equal]
      exact .var id
  · intro old entry member
    rw [introducedEq, List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · exact functionArity_prefix extension (old entry previous)
    · simpa only [IntroducedArity, dependencyLength] using arity

theorem introduce_arity_success {before after : Transformer} {binder : U32} {limits : Limits}
    {term : fang.syntax.Term}
    (stack : before.universals.active.val ≤ before.universals.entries.val.length)
    (success : Transformer.introduce before binder limits = .ok (.Ok term, after)) :
    after.functions.val = before.functions.val ++ [before.universals.active] ∧
    FunctionPrefix before.functions after.functions ∧
    TermArities after.functions term ∧
    (IntroducedArities before.functions before.introduced → IntroducedArities after.functions after.introduced) := by
  have checked := introduce_spec before binder limits stack
  rw [success] at checked
  simp only [spec_ok] at checked
  exact introducePost_arities stack checked

end FangSkolemCore
