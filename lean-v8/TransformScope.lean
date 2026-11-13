/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Scope obligations for recursive Skolem transformation. -/
import Introduce

namespace FangSkolemCore
open fang_skolem_core
open Aeneas.Std Fang.QuantifiedFOF

theorem termWithin_weaken {left right : List Nat} (included : ∀ id ∈ left, id ∈ right)
    (term : Fang.Term) (within : TermWithin left term) : TermWithin right term := by
  cases term with
  | var id =>
    simp only [TermWithin] at within ⊢
    exact included id within
  | app symbol arguments =>
    simp only [TermWithin] at within ⊢
    intro child member
    exact termWithin_weaken included child (within child member)
termination_by sizeOf term

theorem formulaWithin_weaken {left right : List Nat} (included : ∀ id ∈ left, id ∈ right)
    (formula : Formula) (within : formula.Within left) : formula.Within right := by
  induction formula generalizing left right with
  | atom atom => exact fun term member => termWithin_weaken included term (within term member)
  | truth | falsity => trivial
  | neg body ih => exact ih included within
  | conj l r il ir | disj l r il ir | implies l r il ir => exact ⟨il included within.1, ir included within.2⟩
  | all id body ih | ex id body ih =>
    apply ih _ within
    intro other member
    rcases List.mem_cons.mp member with same | member
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons_of_mem _ (included other member)

theorem term_substitution_within (binder : Nat) (bound : List Nat) (replacement term : Fang.Term)
    (replacementWithin : TermWithin bound replacement) (within : TermWithin (binder :: bound) term) :
    TermWithin bound (term.subst [(binder, replacement)]) := by
  cases term with
  | var id =>
    simp only [TermWithin] at within
    by_cases same : binder = id
    · subst id
      simpa [Fang.Term.subst, Fang.lookup] using replacementWithin
    · have present : id ∈ bound := (List.mem_cons.mp within).resolve_left (Ne.symm same)
      simpa [Fang.Term.subst, Fang.lookup, same, TermWithin] using present
  | app symbol arguments =>
    simp only [TermWithin] at within
    simp only [Fang.Term.subst, Fang.termsSubst_eq_map, TermWithin]
    intro target member
    obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
    exact term_substitution_within binder bound replacement child replacementWithin (within child childMember)
termination_by sizeOf term

/-- Scope preservation is separate from semantic capture safety. A captured
    result can still be syntactically in scope; the truth theorem needs both. -/
theorem formula_substitution_within (binder : Nat) (bound : List Nat) (replacement : Fang.Term)
    (formula : Formula) (replacementWithin : TermWithin bound replacement)
    (within : formula.Within (binder :: bound)) :
    (Skolem.substitute binder replacement formula).Within bound := by
  induction formula generalizing bound with
  | atom atom =>
    simp only [Skolem.substitute, Formula.Within, Fang.Atom.subst]
    intro target member
    obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
    exact term_substitution_within binder bound replacement child replacementWithin (within child childMember)
  | truth | falsity => trivial
  | neg body ih => exact ih bound replacementWithin within
  | conj l r il ir | disj l r il ir | implies l r il ir =>
    exact ⟨il bound replacementWithin within.1, ir bound replacementWithin within.2⟩
  | all id body ih | ex id body ih =>
    by_cases same : id = binder
    · subst id
      simp only [Skolem.substitute, ite_true, Formula.Within]
      apply formulaWithin_weaken _ body within
      intro other member
      simpa [List.mem_cons, or_assoc, or_self] using member
    · simp only [Skolem.substitute, same, ite_false, Formula.Within]
      apply ih (id :: bound)
      · exact termWithin_weaken (fun other member => List.mem_cons_of_mem id member) replacement replacementWithin
      · apply formulaWithin_weaken _ body within
        intro other member
        simpa [List.mem_cons, or_left_comm] using member

def TransformReady (universals : List Nat) (formula : fang_quantified_fof_core.Nnf) : Prop :=
  (decodeNnf formula).Within universals ∧ (nnfBinders formula).Nodup ∧
    ∀ id ∈ nnfBinders formula, id.val ∉ universals

/-- Formula structure, excluding term sizes that substitution can increase. -/
def nnfShapeSize : fang_quantified_fof_core.Nnf → Nat
  | .Literal _ | .True | .False => 1
  | .And left right | .Or left right => 1 + nnfShapeSize left + nnfShapeSize right
  | .Forall _ body | .Exists _ body => 1 + nnfShapeSize body

theorem substituted_nnf_shape {binder replacement active source target}
    (related : SubstitutedNnf binder replacement active source target) :
    nnfShapeSize target = nnfShapeSize source := by
  induction related <;> simp_all [nnfShapeSize]

theorem transformReady_and {universals left right}
    (ready : TransformReady universals (.And left right)) :
    TransformReady universals left ∧ TransformReady universals right := by
  have unique : (nnfBinders left ++ nnfBinders right).Nodup := ready.2.1
  refine ⟨⟨ready.1.1, (List.nodup_append.mp unique).1, ?_⟩,
    ⟨ready.1.2, (List.nodup_append.mp unique).2.1, ?_⟩⟩
  · intro id member
    exact ready.2.2 id (List.mem_append_left _ member)
  · intro id member
    exact ready.2.2 id (List.mem_append_right _ member)

theorem transformReady_or {universals left right}
    (ready : TransformReady universals (.Or left right)) :
    TransformReady universals left ∧ TransformReady universals right :=
  transformReady_and ready

theorem transformReady_universal {universals binder body}
    (ready : TransformReady universals (.Forall binder body)) :
    TransformReady (universals ++ [binder.val]) body := by
  have unique : (binder :: nnfBinders body).Nodup := ready.2.1
  refine ⟨?_, (List.nodup_cons.mp unique).2, ?_⟩
  · apply formulaWithin_weaken _ (decodeNnf body) ready.1
    intro id member
    simpa [List.mem_cons, List.mem_append, List.mem_singleton, or_comm] using member
  · intro id member present
    rcases List.mem_append.mp present with outer | last
    · exact ready.2.2 id (List.mem_cons_of_mem binder member) outer
    · have values : id.val = binder.val := List.mem_singleton.mp last
      have same : id = binder := by scalar_tac
      exact (List.nodup_cons.mp unique).1 (same ▸ member)

theorem transformReady_sublist {universals source target}
    (ready : TransformReady universals source)
    (within : (decodeNnf target).Within universals)
    (binders : (nnfBinders target).Sublist (nnfBinders source)) : TransformReady universals target :=
  ⟨within, ready.2.1.sublist binders, fun id member => ready.2.2 id (binders.subset member)⟩

theorem transformReady_existential_substitution {universals binder body replacement target fresh}
    (ready : TransformReady universals (.Exists binder body))
    (decoded : decodeTerm replacement = .app fresh (universals.map Fang.Term.var))
    (substituted : SubstitutedNnf binder replacement true body target) :
    TransformReady universals target ∧
      Skolem.CaptureSafe binder.val (decodeTerm replacement) (decodeNnf body) := by
  have bodyBinders : (nnfBinders body).Nodup := (List.nodup_cons.mp ready.2.1).2
  have bodyFresh : ∀ id ∈ nnfBinders body, id.val ∉ universals :=
    fun id member => ready.2.2 id (List.mem_cons_of_mem binder member)
  have replacementWithin : TermWithin universals (decodeTerm replacement) := by
    rw [decoded]
    simp only [TermWithin]
    intro term member
    obtain ⟨id, idMember, rfl⟩ := List.mem_map.mp member
    simpa only [TermWithin] using idMember
  have scope := formula_substitution_within binder.val universals (decodeTerm replacement) (decodeNnf body)
    replacementWithin ready.1
  have targetDecode := substituted_nnf_decode substituted
  simp only [ite_true] at targetDecode
  have preserved := substituted_nnf_binders substituted
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [targetDecode]
    exact scope
  · rw [preserved]
    exact bodyBinders
  · rw [preserved]
    exact bodyFresh
  · rw [decoded]
    exact skolem_application_captureSafe body binder.val fresh universals bodyFresh

end FangSkolemCore
