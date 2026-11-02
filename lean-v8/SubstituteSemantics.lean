/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Explicit connection from the actual Rust representation to Fang's term model. -/
import SubstituteProperties
import Fang.Logic

open Aeneas Aeneas.Std Aeneas.Std.WP Result Aeneas.Data.ListN

namespace FangSkolemCore
open fang_skolem_core

mutual
def decodeTerm : fang.syntax.Term → Fang.Term
  | .Var id => .var id.val
  | .Fun symbol arguments => .app symbol.val (decodeVec arguments)
def decodeVec : alloc.vec.Vec fang.syntax.Term → List Fang.Term
  | ⟨slice⟩ => decodeSlice slice
def decodeSlice : Slice fang.syntax.Term → List Fang.Term
  | ⟨_, terms, _⟩ => decodeTerms terms
def decodeTerms {n : Nat} : ListN fang.syntax.Term n → List Fang.Term
  | .nil => []
  | .cons term rest => decodeTerm term :: decodeTerms rest
end

theorem decodeTerms_eq_map {n : Nat} (terms : ListN fang.syntax.Term n) :
    decodeTerms terms = terms.toList.map decodeTerm := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [decodeTerms, ListN.toList, ih]

theorem decodeVec_eq_map (arguments : alloc.vec.Vec fang.syntax.Term) :
    decodeVec arguments = arguments.val.map decodeTerm := by
  cases arguments with
  | mk slice =>
    cases slice with
    | mk count terms bound =>
      simpa [decodeVec, decodeSlice, alloc.vec.Vec.val, Slice.val] using decodeTerms_eq_map terms

theorem substituted_decode {binder replacement term target}
    (substituted : SubstitutedTerm binder replacement term target) :
    decodeTerm target = (decodeTerm term).subst [(binder.val, decodeTerm replacement)] := by
  induction substituted with
  | bound => simp [decodeTerm, Fang.Term.subst, Fang.lookup]
  | free id different =>
    have values_differ : binder.val ≠ id.val := by
      intro same
      exact different (UScalar.eq_of_val_eq same.symm)
    simp [decodeTerm, Fang.Term.subst, Fang.lookup, values_differ]
  | fun_ symbol arguments target length children ih =>
    simp only [decodeTerm, Fang.Term.subst, Fang.termsSubst_eq_map, decodeVec_eq_map, List.map_map]
    congr 1
    apply List.ext_getElem
    · simp [length]
    · intro i ht hs
      simp only [List.getElem_map, Function.comp_apply]
      exact ih i (by simpa using hs) (by simpa using ht)

/-- The actual generated helper, with no target-existence premise, returns the
    independent model's exact simultaneous substitution or typed resources. -/
theorem substitute_semantics (term : fang.syntax.Term) (binder : U32) (replacement : fang.syntax.Term)
    (depth : Usize) (limits : Limits) (work : Work) :
    substitute_term term binder replacement depth limits work
      ⦃ CopyPost (fun value => decodeTerm value =
        (decodeTerm term).subst [(binder.val, decodeTerm replacement)]) work ⦄ := by
  apply spec_mono (substitute_total term binder replacement depth limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Ok value => exact substituted_decode hp
  | Err error => cases error <;> exact hp

end FangSkolemCore
