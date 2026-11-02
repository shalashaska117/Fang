/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Equality

namespace Fang.Equality

def Atom.rename (mapping : Nat → Nat) : Atom → Atom
  | .predicate atom => .predicate (atom.rename mapping)
  | .equal left right => .equal (left.rename mapping) (right.rename mapping)

def Literal.rename (mapping : Nat → Nat) (literal : Literal) : Literal :=
  ⟨literal.positive, literal.atom.rename mapping⟩

theorem atom_holds_rename {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (mapping : Nat → Nat) (atom : Atom) :
    (atom.rename mapping).Holds model valuation ↔
      atom.Holds model (fun varId => valuation (mapping varId)) := by
  cases atom <;> simp [Atom.rename, Atom.Holds, Fang.Atom.rename, Fang.Atom.Holds,
    List.map_map, Function.comp_def, Term.eval_rename]

theorem literal_holds_rename {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (mapping : Nat → Nat) (literal : Literal) :
    (literal.rename mapping).Holds model valuation ↔
      literal.Holds model (fun varId => valuation (mapping varId)) := by
  simp [Literal.rename, Literal.Holds, atom_holds_rename]

theorem clause_valid_rename {D : Type} (model : Interpretation D) (mapping : Nat → Nat)
    (clause : Clause) (valid : clauseValid model clause) :
    clauseValid model (clause.map (Literal.rename mapping)) := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun varId => valuation (mapping varId))
  exact ⟨literal.rename mapping, List.mem_map.mpr ⟨literal, member, rfl⟩,
    (literal_holds_rename model valuation mapping literal).mpr holds⟩

end Fang.Equality
