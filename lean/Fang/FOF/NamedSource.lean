/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.SourceSemantics
import Fang.FOF.Groundness

namespace Fang.NamedFOF

inductive Formula where
  | atom : String → List Source.Term → Formula
  | truth
  | falsity
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | implies : Formula → Formula → Formula

def Formula.Holds {D : Type} (M : Source.Interpretation D) (ρ : String → D) : Formula → Prop
  | .atom name args => M.predicate name (args.map (Source.Term.eval M ρ))
  | .truth => True
  | .falsity => False
  | .neg a => ¬ a.Holds M ρ
  | .conj a b => a.Holds M ρ ∧ b.Holds M ρ
  | .disj a b => a.Holds M ρ ∨ b.Holds M ρ
  | .implies a b => a.Holds M ρ → b.Holds M ρ

def GroundTerm : Source.Term → Prop
  | .var _ => False
  | .app _ args => ∀ t ∈ args, GroundTerm t

def Formula.Ground : Formula → Prop
  | .atom _ args => ∀ t ∈ args, GroundTerm t
  | .truth | .falsity => True
  | .neg a => a.Ground
  | .conj a b | .disj a b | .implies a b => a.Ground ∧ b.Ground

inductive Encoding (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) : Formula → GroundFOF.Formula → Prop where
  | atom (name : String) (args : List Source.Term) (encoded : List Fang.Term)
      (roundtrip : symbols.predicateName (symbols.predicateId name) = name)
      (arity : signature.predicateArity name = some args.length)
      (terms : Source.TermsEncoding signature symbols variables args encoded) :
      Encoding signature symbols variables (.atom name args) (.atom ⟨symbols.predicateId name, encoded⟩)
  | truth : Encoding signature symbols variables .truth .truth
  | falsity : Encoding signature symbols variables .falsity .falsity
  | neg {a out} (child : Encoding signature symbols variables a out) :
      Encoding signature symbols variables (.neg a) (.neg out)
  | conj {a b left right} (first : Encoding signature symbols variables a left)
      (second : Encoding signature symbols variables b right) :
      Encoding signature symbols variables (.conj a b) (.conj left right)
  | disj {a b left right} (first : Encoding signature symbols variables a left)
      (second : Encoding signature symbols variables b right) :
      Encoding signature symbols variables (.disj a b) (.disj left right)
  | implies {a b left right} (first : Encoding signature symbols variables a left)
      (second : Encoding signature symbols variables b right) :
      Encoding signature symbols variables (.implies a b) (.implies left right)

mutual
theorem encoded_term_ground {signature symbols variables named encoded}
    (encoding : Source.TermEncoding signature symbols variables named encoded)
    (ground : GroundTerm named) : GroundFOF.GroundTerm encoded := by
  cases encoding with
  | var name _ => simp only [GroundTerm] at ground
  | app name args encoded _ _ children =>
    simp only [GroundTerm] at ground
    simp only [GroundFOF.GroundTerm]
    exact encoded_terms_ground children ground
theorem encoded_terms_ground {signature symbols variables named encoded}
    (encoding : Source.TermsEncoding signature symbols variables named encoded)
    (ground : ∀ t ∈ named, GroundTerm t) : ∀ t ∈ encoded, GroundFOF.GroundTerm t := by
  cases encoding with
  | nil => simp
  | cons head tail =>
    intro t member
    rcases List.mem_cons.mp member with same | member
    · subst t
      exact encoded_term_ground head (ground _ List.mem_cons_self)
    · exact encoded_terms_ground tail (fun t ht => ground t (List.mem_cons_of_mem _ ht)) t member
end

theorem Encoding.ground {signature symbols variables named encoded}
    (encoding : Encoding signature symbols variables named encoded)
    (ground : named.Ground) : encoded.Ground := by
  induction encoding with
  | atom name args encoded _ _ terms =>
    exact encoded_terms_ground terms ground
  | truth => trivial
  | falsity => trivial
  | neg child ih => exact ih ground
  | conj first second ih₁ ih₂ => exact ⟨ih₁ ground.1, ih₂ ground.2⟩
  | disj first second ih₁ ih₂ => exact ⟨ih₁ ground.1, ih₂ ground.2⟩
  | implies first second ih₁ ih₂ => exact ⟨ih₁ ground.1, ih₂ ground.2⟩

theorem Encoding.holds_toNumeric {signature symbols variables named encoded}
    (encoding : Encoding signature symbols variables named encoded)
    {D : Type} (M : Source.Interpretation D) (ρ : Nat → D) :
    encoded.Holds (M.toNumeric symbols) ρ ↔ named.Holds M (fun n => ρ (variables.id n)) := by
  induction encoding with
  | atom name args encoded roundtrip _ terms =>
    simp only [GroundFOF.Formula.Holds, Fang.Atom.Holds, Formula.Holds]
    rw [terms.eval_toNumeric M ρ]
    simp only [Source.Interpretation.toNumeric, roundtrip]
  | truth => rfl
  | falsity => rfl
  | neg _ ih => exact not_congr ih
  | conj _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | disj _ _ ih₁ ih₂ => exact or_congr ih₁ ih₂
  | implies _ _ ih₁ ih₂ => exact imp_congr ih₁ ih₂

theorem Encoding.holds_toNamed {signature symbols variables named encoded}
    (encoding : Encoding signature symbols variables named encoded)
    {D : Type} (M : Fang.Interpretation D) (ρ : String → D) :
    named.Holds (Source.numericToNamed M symbols) ρ ↔ encoded.Holds M (fun n => ρ (variables.name n)) := by
  induction encoding with
  | atom name args encoded _ _ terms =>
    simp only [GroundFOF.Formula.Holds, Fang.Atom.Holds, Formula.Holds]
    rw [terms.eval_toNamed M ρ]
    rfl
  | truth => rfl
  | falsity => rfl
  | neg _ ih => exact not_congr ih
  | conj _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | disj _ _ ih₁ ih₂ => exact or_congr ih₁ ih₂
  | implies _ _ ih₁ ih₂ => exact imp_congr ih₁ ih₂

inductive Declaration where
  | cnf : Source.Clause → Declaration
  | fof : String → Formula → Declaration

def Declaration.name : Declaration → String
  | .cnf clause => clause.name
  | .fof name _ => name

/-- Closure is used only after the groundness requirement in DeclarationEncoding.
    This definition does not authorize implicit universal quantification in FOF. -/
def Declaration.Models {D : Type} (M : Source.Interpretation D) : Declaration → Prop
  | .cnf clause => clause.Valid M
  | .fof _ formula => ∀ ρ, formula.Holds M ρ

inductive DeclarationEncoding (signature : Source.Signature) (symbols : Source.Symbols) :
    Declaration → GroundFOF.Declaration → Prop where
  | cnf {named encoded} (variables : Source.Variables)
      (relation : Source.ClauseEncoding signature symbols variables named encoded) :
      DeclarationEncoding signature symbols (.cnf named) (.cnf encoded)
  | fof (name : String) {named encoded} (variables : Source.Variables)
      (ground : named.Ground) (relation : Encoding signature symbols variables named encoded) :
      DeclarationEncoding signature symbols (.fof name named) (.fof encoded)

theorem DeclarationEncoding.models_toNumeric {signature symbols named encoded}
    (encoding : DeclarationEncoding signature symbols named encoded)
    {D : Type} (M : Source.Interpretation D) (h : named.Models M) :
    encoded.Models (M.toNumeric symbols) := by
  cases encoding with
  | cnf variables relation => exact relation.valid_toNumeric M h
  | fof name variables ground relation =>
    intro ρ
    exact (relation.holds_toNumeric M ρ).mpr (h (fun n => ρ (variables.id n)))

theorem DeclarationEncoding.models_toNamed {signature symbols named encoded}
    (encoding : DeclarationEncoding signature symbols named encoded)
    {D : Type} (M : Fang.Interpretation D) (h : encoded.Models M) :
    named.Models (Source.numericToNamed M symbols) := by
  cases encoding with
  | cnf variables relation => exact relation.valid_toNamed M h
  | fof name variables ground relation =>
    intro ρ
    exact (relation.holds_toNamed M ρ).mpr (h (fun n => ρ (variables.name n)))

def Models {D : Type} (M : Source.Interpretation D) (declarations : List Declaration) : Prop :=
  ∀ declaration ∈ declarations, declaration.Models M

def Satisfiable (declarations : List Declaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (M : Source.Interpretation D), Models M declarations

structure ProblemEncoding (signature : Source.Signature) (symbols : Source.Symbols)
    (named : List Declaration) (encoded : List GroundFOF.Declaration) : Prop where
  uniqueNames : (named.map Declaration.name).Nodup
  declarations : Source.RelatedLists (DeclarationEncoding signature symbols) named encoded

theorem ProblemEncoding.satisfiable_iff {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded) :
    Satisfiable named ↔ GroundFOF.DeclarationsSatisfiable encoded := by
  constructor
  · rintro ⟨D, inhabited, M, models⟩
    refine ⟨D, inhabited, M.toNumeric symbols, ?_⟩
    intro declaration member
    obtain ⟨source, sourceMember, related⟩ := encoding.declarations.member_right member
    exact related.models_toNumeric M (models source sourceMember)
  · rintro ⟨D, inhabited, M, models⟩
    refine ⟨D, inhabited, Source.numericToNamed M symbols, ?_⟩
    intro declaration member
    obtain ⟨output, outputMember, related⟩ := encoding.declarations.member_left member
    exact related.models_toNamed M (models output outputMember)

theorem ProblemEncoding.prepared_satisfiable_iff {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded) :
    Satisfiable named ↔ Fang.Satisfiable (GroundFOF.prepareDeclarations encoded) :=
  encoding.satisfiable_iff.trans (GroundFOF.prepareDeclarations_satisfiable encoded).symm

/-- Refutation transfer to a named AST, under an explicit encoding witness.
    Parsing and original-byte FOF semantics are still separate obligations. -/
theorem ProblemEncoding.unsat_of_check {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded) (certificate : Fang.Certificate)
    (accepted : Fang.check (GroundFOF.prepareDeclarations encoded) certificate = true) :
    ¬ Satisfiable named := by
  intro model
  exact Fang.check_sound _ certificate accepted (encoding.prepared_satisfiable_iff.mp model)

end Fang.NamedFOF
