/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Explicit freshness premises for composition with rectified Skolem inputs. -/
import SubstituteFormula

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open Fang.QuantifiedFOF

def nnfBinders : fang_quantified_fof_core.Nnf → List U32
  | .Literal _ | .True | .False => []
  | .And left right | .Or left right => nnfBinders left ++ nnfBinders right
  | .Forall id body | .Exists id body => id :: nnfBinders body

theorem substituted_nnf_binders {binder replacement active source target}
    (related : SubstitutedNnf binder replacement active source target) :
    nnfBinders target = nnfBinders source := by
  induction related <;> simp_all [nnfBinders]

theorem captureSafe_of_avoids (formula : fang_quantified_fof_core.Nnf) (binder : Nat)
    (replacement : Fang.Term)
    (avoids : ∀ id ∈ nnfBinders formula, Skolem.TermAvoid id.val replacement) :
    Skolem.CaptureSafe binder replacement (decodeNnf formula) := by
  induction formula with
  | Literal literal => cases sign : literal.positive <;> simp [decodeNnf, literalFormula, sign, Skolem.CaptureSafe]
  | True | False => trivial
  | And left right il ir | Or left right il ir =>
    exact ⟨il (fun id member => avoids id (List.mem_append_left _ member)),
      ir (fun id member => avoids id (List.mem_append_right _ member))⟩
  | Forall id body ih | Exists id body ih =>
    exact Or.inr ⟨avoids id (List.mem_cons_self), ih (fun other member => avoids other (List.mem_cons_of_mem _ member))⟩

theorem skolem_application_captureSafe (formula : fang_quantified_fof_core.Nnf) (binder fresh : Nat)
    (universals : List Nat)
    (disjoint : ∀ id ∈ nnfBinders formula, id.val ∉ universals) :
    Skolem.CaptureSafe binder (.app fresh (universals.map Fang.Term.var)) (decodeNnf formula) := by
  apply captureSafe_of_avoids
  intro id member
  simp only [Skolem.TermAvoid]
  intro term termMember
  obtain ⟨varId, occurs, rfl⟩ := List.mem_map.mp termMember
  simp only [Skolem.TermAvoid]
  intro same
  exact disjoint id member (same ▸ occurs)

/-- This supplies the capture premise from disjoint enclosing universal IDs.
    Connecting that disjointness to the whole Rust Skolem traversal is separate. -/
theorem substitute_skolem_holds {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D)
    (formula : fang_quantified_fof_core.Nnf) (binder : U32) (replacement : fang.syntax.Term)
    (fresh : Nat) (universals : List Nat)
    (decoded : decodeTerm replacement = .app fresh (universals.map Fang.Term.var))
    (disjoint : ∀ id ∈ nnfBinders formula, id.val ∉ universals)
    (limits : Limits) (work : Work) :
    substitute_nnf formula binder replacement true limits work
      ⦃ CopyPost (fun value => (decodeNnf value).Holds model valuation ↔
        (decodeNnf formula).Holds model
          (update valuation binder.val ((decodeTerm replacement).eval model valuation))) work ⦄ := by
  apply substitute_nnf_holds
  rw [decoded]
  exact skolem_application_captureSafe formula binder.val fresh universals disjoint

end FangSkolemCore
