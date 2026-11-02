/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent binder-removal specification, not a Rust refinement theorem. -/
import QuantifiedFormula

namespace Fang.QuantifiedFOF.BinderRemoval

def binders : Nnf → List Nat
  | .lit _ | .truth | .falsity => []
  | .conj left right | .disj left right => binders left ++ binders right
  | .all id body | .ex id body => id :: binders body

def NoExists : Nnf → Prop
  | .lit _ | .truth | .falsity => True
  | .conj left right | .disj left right => NoExists left ∧ NoExists right
  | .all _ body => NoExists body
  | .ex _ _ => False

/-- The literal values, binary syntax and operand order are unchanged.
    There is deliberately no rule for an existential binder. -/
inductive Erases : Nnf → GroundFOF.Nnf → Prop where
  | lit (literal) : Erases (.lit literal) (.lit literal)
  | truth : Erases .truth .truth
  | falsity : Erases .falsity .falsity
  | conj {left right l r} : Erases left l → Erases right r → Erases (.conj left right) (.conj l r)
  | disj {left right l r} : Erases left l → Erases right r → Erases (.disj left right) (.disj l r)
  | all {id body result} : Erases body result → Erases (.all id body) result

theorem Erases.functional {source left right} (first : Erases source left)
    (second : Erases source right) : left = right := by
  induction first generalizing right with
  | lit | truth | falsity => cases second; rfl
  | conj l r il ir =>
    cases second with
    | conj l' r' => rw [il l', ir r']
  | disj l r il ir =>
    cases second with
    | disj l' r' => rw [il l', ir r']
  | all child ih => cases second with | all other => exact ih other

theorem erases_exists_iff (source : Nnf) : (∃ target, Erases source target) ↔ NoExists source := by
  induction source with
  | lit literal => exact ⟨fun _ => trivial, fun _ => ⟨_, .lit literal⟩⟩
  | truth => exact ⟨fun _ => trivial, fun _ => ⟨_, .truth⟩⟩
  | falsity => exact ⟨fun _ => trivial, fun _ => ⟨_, .falsity⟩⟩
  | conj left right il ir =>
    constructor
    · rintro ⟨target, erased⟩
      cases erased with
      | conj l r => exact ⟨il.mp ⟨_, l⟩, ir.mp ⟨_, r⟩⟩
    · rintro ⟨l, r⟩
      obtain ⟨l, el⟩ := il.mpr l
      obtain ⟨r, er⟩ := ir.mpr r
      exact ⟨_, .conj el er⟩
  | disj left right il ir =>
    constructor
    · rintro ⟨target, erased⟩
      cases erased with
      | disj l r => exact ⟨il.mp ⟨_, l⟩, ir.mp ⟨_, r⟩⟩
    · rintro ⟨l, r⟩
      obtain ⟨l, el⟩ := il.mpr l
      obtain ⟨r, er⟩ := ir.mpr r
      exact ⟨_, .disj el er⟩
  | all id body ih =>
    constructor
    · rintro ⟨target, erased⟩
      cases erased with | all child => exact ih.mp ⟨_, child⟩
    · intro body
      obtain ⟨target, child⟩ := ih.mpr body
      exact ⟨target, .all child⟩
  | ex id body ih =>
    constructor
    · rintro ⟨target, impossible⟩; cases impossible
    · intro impossible; exact False.elim impossible

/-- `free` contains the allowed external variables. Binder IDs are globally
    distinct and excluded from that external scope; uniqueness alone is not enough. -/
def RectifiedWithin (free : List Nat) (source : Nnf) : Prop :=
  source.Within free ∧ (binders source).Nodup ∧ ∀ id ∈ binders source, id ∉ free

theorem rectified_binary {free left right} (within : left.Within free ∧ right.Within free)
    (unique : (binders left ++ binders right).Nodup)
    (fresh : ∀ id ∈ binders left ++ binders right, id ∉ free) :
    RectifiedWithin free left ∧ RectifiedWithin free right ∧
      ∀ id ∈ binders left, ∀ other ∈ binders right, id ≠ other := by
  obtain ⟨leftUnique, rightUnique, disjoint⟩ := List.nodup_append.mp unique
  exact ⟨⟨within.1, leftUnique, fun id member => fresh id (List.mem_append_left _ member)⟩,
    ⟨within.2, rightUnique, fun id member => fresh id (List.mem_append_right _ member)⟩,
    disjoint⟩

theorem rectified_all {free id body} (safe : RectifiedWithin free (.all id body)) :
    RectifiedWithin (id :: free) body ∧ id ∉ free := by
  obtain ⟨within, unique, fresh⟩ := safe
  have unique' := List.nodup_cons.mp unique
  refine ⟨⟨within, unique'.2, ?_⟩, fresh id (by simp [binders])⟩
  intro other member admitted
  rcases List.mem_cons.mp admitted with same | inFree
  · exact unique'.1 (same ▸ member)
  · exact fresh other (by simp [binders, member]) inFree

def GroundWithin (free : List Nat) : GroundFOF.Nnf → Prop
  | .lit literal => ∀ term ∈ literal.atom.args, TermWithin free term
  | .truth | .falsity => True
  | .conj left right | .disj left right => GroundWithin free left ∧ GroundWithin free right

theorem termWithin_mono {left right : List Nat} (included : ∀ id ∈ left, id ∈ right)
    (term : Term) (within : TermWithin left term) : TermWithin right term := by
  cases term with
  | var id => simpa only [TermWithin] using included id (by simpa only [TermWithin] using within)
  | app symbol arguments =>
    simp only [TermWithin] at within ⊢
    intro term member
    exact termWithin_mono included term (within term member)
termination_by sizeOf term

theorem groundWithin_mono {left right : List Nat} (included : ∀ id ∈ left, id ∈ right)
    (formula : GroundFOF.Nnf) (within : GroundWithin left formula) : GroundWithin right formula := by
  induction formula with
  | lit literal => exact fun term member => termWithin_mono included term (within term member)
  | truth | falsity => trivial
  | conj left right il ir | disj left right il ir => exact ⟨il within.1, ir within.2⟩

theorem Erases.within {source target} (erased : Erases source target)
    (free : List Nat) (within : source.Within free) :
    GroundWithin (free ++ binders source) target := by
  induction erased generalizing free with
  | lit literal => simpa [binders, GroundWithin, Nnf.Within] using within
  | truth | falsity => trivial
  | @conj left right l r el er il ir | @disj left right l r el er il ir =>
    refine ⟨groundWithin_mono ?_ l (il free within.1), groundWithin_mono ?_ r (ir free within.2)⟩
    · intro id member
      simp only [binders, List.mem_append] at member ⊢
      exact member.elim Or.inl (fun h => Or.inr (Or.inl h))
    · intro id member
      simp only [binders, List.mem_append] at member ⊢
      exact member.elim Or.inl (fun h => Or.inr (Or.inr h))
  | @all id body target child ih =>
    apply groundWithin_mono _ target (ih (id :: free) within)
    intro other member
    simpa [binders, List.mem_append, or_assoc, or_left_comm, or_comm] using member

def literals : Nnf → List Literal
  | .lit literal => [literal]
  | .truth | .falsity => []
  | .conj left right | .disj left right => literals left ++ literals right
  | .all _ body | .ex _ body => literals body

def groundLiterals : GroundFOF.Nnf → List Literal
  | .lit literal => [literal]
  | .truth | .falsity => []
  | .conj left right | .disj left right => groundLiterals left ++ groundLiterals right

/-- All atoms, term arguments, IDs, polarities, duplicates and literal order
    remain exact. Removing binders allocates no function or predicate symbol. -/
theorem Erases.literals {source target} (erased : Erases source target) :
    groundLiterals target = literals source := by
  induction erased with
  | lit | truth | falsity => rfl
  | conj left right il ir | disj left right il ir => simp [groundLiterals, BinderRemoval.literals, il, ir]
  | all child ih => exact ih

end Fang.QuantifiedFOF.BinderRemoval
