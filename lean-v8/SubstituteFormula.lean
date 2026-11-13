/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural and semantic correspondence for the actual generated helper. -/
import SubstituteNnf
import Substitution

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open Fang.QuantifiedFOF

def decodeAtom (literal : fang.syntax.Literal) : Fang.Atom :=
  ⟨literal.predicate.val, decodeVec literal.arguments⟩

def literalFormula (literal : fang.syntax.Literal) : Formula :=
  if literal.positive then .atom (decodeAtom literal) else .neg (.atom (decodeAtom literal))

def decodeNnf : fang_quantified_fof_core.Nnf → Formula
  | .Literal literal => literalFormula literal
  | .True => .truth
  | .False => .falsity
  | .And left right => .conj (decodeNnf left) (decodeNnf right)
  | .Or left right => .disj (decodeNnf left) (decodeNnf right)
  | .Forall id body => .all id.val (decodeNnf body)
  | .Exists id body => .ex id.val (decodeNnf body)

theorem substituted_literal_decode {binder replacement source target}
    (related : SubstitutedLiteral binder replacement source target) :
    literalFormula target = Skolem.substitute binder.val (decodeTerm replacement) (literalFormula source) := by
  obtain ⟨positive, predicate, length, children⟩ := related
  have arguments : decodeVec target.arguments =
      (decodeVec source.arguments).map (fun term => term.subst [(binder.val, decodeTerm replacement)]) := by
    simp only [decodeVec_eq_map, List.map_map]
    apply List.ext_getElem
    · simp [length]
    · intro i ht hs
      simp only [List.getElem_map, Function.comp_apply]
      exact substituted_decode (children i (by simpa using hs) (by simpa using ht))
  simp only [literalFormula, positive]
  cases source.positive <;> simp [decodeAtom, predicate, arguments, Skolem.substitute, Fang.Atom.subst]

theorem substituted_nnf_decode {binder replacement active source target}
    (related : SubstitutedNnf binder replacement active source target) :
    decodeNnf target = if active then Skolem.substitute binder.val (decodeTerm replacement) (decodeNnf source)
      else decodeNnf source := by
  induction related with
  | literalOn related => exact substituted_literal_decode related
  | literalOff | truth | falsity => simp [decodeNnf, Skolem.substitute]
  | @conjunction active left right l r leftChild rightChild il ir
    | @disjunction active left right l r leftChild rightChild il ir =>
    cases active <;> simp_all [decodeNnf, Skolem.substitute]
  | @universal active id body target child ih | @existential active id body target child ih =>
    have values : id.val = binder.val ↔ id = binder :=
      ⟨UScalar.eq_of_val_eq, fun same => congrArg (fun x : U32 => x.val) same⟩
    cases active <;> by_cases same : id = binder <;>
      simp_all [decodeNnf, Skolem.substitute]

/-- Exact substitution and totality refer to the actual generated Rust helper.
    The semantic corollary below separately requires capture safety. -/
theorem substitute_nnf_semantics (formula : fang_quantified_fof_core.Nnf) (binder : U32)
    (replacement : fang.syntax.Term) (active : Bool) (limits : Limits) (work : Work) :
    substitute_nnf formula binder replacement active limits work
      ⦃ CopyPost (fun value => decodeNnf value =
        if active then Skolem.substitute binder.val (decodeTerm replacement) (decodeNnf formula)
        else decodeNnf formula) work ⦄ := by
  apply spec_mono (substitute_nnf_total formula binder replacement active limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Ok value => exact substituted_nnf_decode hp
  | Err error => cases error <;> exact hp

theorem substitute_nnf_holds {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D)
    (formula : fang_quantified_fof_core.Nnf) (binder : U32) (replacement : fang.syntax.Term)
    (safe : Skolem.CaptureSafe binder.val (decodeTerm replacement) (decodeNnf formula))
    (limits : Limits) (work : Work) :
    substitute_nnf formula binder replacement true limits work
      ⦃ CopyPost (fun value => (decodeNnf value).Holds model valuation ↔
        (decodeNnf formula).Holds model
          (update valuation binder.val ((decodeTerm replacement).eval model valuation))) work ⦄ := by
  apply spec_mono (substitute_nnf_semantics formula binder replacement true limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Ok value =>
    simp only [ite_true] at hp
    dsimp only
    rw [hp]
    exact Skolem.substitute_holds model valuation binder.val (decodeTerm replacement) (decodeNnf formula) safe
  | Err error => cases error <;> exact hp

end FangSkolemCore
