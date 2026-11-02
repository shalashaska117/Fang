/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import SubstituteTerm

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

theorem forall₂_get {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : List.Forall₂ relation left right) :
    ∀ i (hl : i < left.length) (hr : i < right.length), relation left[i] right[i] := by
  induction related with
  | nil => intro i impossible; simp at impossible
  | cons head tail ih =>
    intro i hl hr
    cases i with
    | zero => simpa using head
    | succ i => simpa using ih i (by simpa using hl) (by simpa using hr)

mutual
theorem substituted_exists (binder : U32) (replacement term : fang.syntax.Term) :
    ∃ target, SubstitutedTerm binder replacement term target := by
  cases term with
  | Var id =>
    by_cases same : id = binder
    · subst id; exact ⟨replacement, .bound⟩
    · exact ⟨.Var id, .free id same⟩
  | Fun symbol arguments =>
    cases arguments with
    | mk slice =>
      cases slice with
      | mk count terms bound =>
        obtain ⟨targets, related⟩ := substituted_list_exists binder replacement terms
        let target : alloc.vec.Vec fang.syntax.Term := ⟨⟨count, targets, bound⟩⟩
        refine ⟨.Fun symbol target, .fun_ symbol _ target ?_ ?_⟩
        · simpa [target, alloc.vec.Vec.val, Slice.val] using related.length_eq.symm
        · intro i hi ht
          exact forall₂_get related i hi ht
termination_by sizeOf term

theorem substituted_list_exists (binder : U32) (replacement : fang.syntax.Term)
    {n : Nat} (terms : Aeneas.Data.ListN.ListN fang.syntax.Term n) :
    ∃ targets : Aeneas.Data.ListN.ListN fang.syntax.Term n,
      List.Forall₂ (SubstitutedTerm binder replacement) terms.toList targets.toList := by
  cases terms with
  | nil => exact ⟨.nil, .nil⟩
  | cons term rest =>
    obtain ⟨target, related⟩ := substituted_exists binder replacement term
    obtain ⟨targets, rest_related⟩ := substituted_list_exists binder replacement rest
    exact ⟨.cons target targets, .cons related rest_related⟩
termination_by sizeOf terms
end

theorem substituted_functional {binder replacement term left right}
    (first : SubstitutedTerm binder replacement term left)
    (second : SubstitutedTerm binder replacement term right) : left = right := by
  induction first generalizing right with
  | bound =>
    cases second with
    | bound => rfl
    | free _ different => exact False.elim (different rfl)
  | free id different =>
    cases second with
    | bound => exact False.elim (different rfl)
    | free => rfl
  | fun_ symbol arguments target length children ih =>
    cases second with
    | fun_ _ _ other other_length other_children =>
      congr 1
      apply alloc.vec.Vec.ext
      apply List.ext_getElem
      · omega
      · intro i ht ho
        exact ih i (by omega) ht (other_children i (by omega) ho)

theorem substitute_total (term : fang.syntax.Term) (binder : U32) (replacement : fang.syntax.Term)
    (depth : Usize) (limits : Limits) (work : Work) :
    substitute_term term binder replacement depth limits work
      ⦃ CopyPost (SubstitutedTerm binder replacement term) work ⦄ := by
  obtain ⟨target, substituted⟩ := substituted_exists binder replacement term
  apply spec_mono (substitute_term_spec term target binder replacement substituted depth limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Ok value => rw [hp]; exact substituted
  | Err error => cases error <;> exact hp

end FangSkolemCore
