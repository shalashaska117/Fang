/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Postconditions for the actual recursive Skolem transformer. -/
import TransformRelation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

def TransformResource (kind : Resource) : Prop :=
  kind = .Operations ∨ kind = .StoredNodes ∨ kind = .TermDepth ∨
    kind = .Functions ∨ kind = .SkolemSymbols

theorem copyResource_transform {kind} (resource : CopyResource kind) : TransformResource kind := by
  rcases resource with same | same | same <;> simp [TransformResource, same]

theorem introduceResource_transform {kind} (resource : IntroduceResource kind) : TransformResource kind := by
  rcases resource with same | same | same | same <;> simp [TransformResource, same]

/-- Scalar headroom for every nested universal push. Term substitution preserves
    the binder list, so this bound also applies to the substituted recursive call. -/
def TransformRoom (before : Transformer) (formula : Nnf) : Prop :=
  before.universals.active.val + (nnfBinders formula).length ≤ Usize.max

def TransformFailure : fang_skolem_core.Error → Prop
  | .Resource kind => TransformResource kind
  | .Core _ => False

/-- A successful value is related to the source by the checked Skolem relation.
    The caller's active stack and declaration are preserved on every outcome.
    Resource errors expose no transformed value. This predicate does not assert
    physical allocation bounds or sufficient credits for successful execution. -/
def TransformPost (before : Transformer) (formula : Nnf)
    (answer : core.result.Result Nnf fang_skolem_core.Error × Transformer) : Prop :=
  UniversalValid answer.2.universals ∧ UniversalFrame before.universals answer.2.universals ∧
  answer.2.declaration = before.declaration ∧
  before.work.statistics.operations.val ≤ answer.2.work.statistics.operations.val ∧
  match answer.1 with
  | .Ok value => Fang.QuantifiedFOF.Skolem.Skolemized (universalIds before.universals)
      before.functions.val.length (decodeNnf formula) (decodeNnf value) answer.2.functions.val.length
  | .Err error => TransformFailure error

theorem transformPost_work {before : Transformer} {formula : Nnf} {work : Work} {answer}
    (operations : before.work.statistics.operations.val ≤ work.statistics.operations.val)
    (post : TransformPost { before with work } formula answer) : TransformPost before formula answer := by
  obtain ⟨valid, frame, declaration, monotone, outcome⟩ := post
  exact ⟨valid, frame, declaration, Nat.le_trans operations monotone, outcome⟩

theorem transformPost_resource (before : Transformer) (formula : Nnf) (work : Work) (kind : Resource)
    (valid : UniversalValid before.universals)
    (operations : before.work.statistics.operations.val ≤ work.statistics.operations.val)
    (resource : TransformResource kind) :
    TransformPost before formula (.Err (.Resource kind), { before with work }) :=
  ⟨valid, universalFrame_refl _, rfl, operations, resource⟩

theorem transformPost_frame_ids {before : Transformer} {formula : Nnf} {answer}
    (post : TransformPost before formula answer) :
    universalIds answer.2.universals = universalIds before.universals := universalFrame_ids post.2.1

theorem transformPost_meaning {before after : Transformer} {source target : Nnf}
    (post : TransformPost before source (.Ok target, after))
    {D : Type} [Nonempty D] (original : Fang.Interpretation D)
    (reserved : Fang.QuantifiedFOF.Skolem.FormulaBelow before.functions.val.length (decodeNnf source)) :
    ∃ extended : Fang.Interpretation D,
      Fang.QuantifiedFOF.Skolem.PreservesBelow before.functions.val.length original extended ∧
      ∀ valuation, (decodeNnf source).Holds original valuation ↔ (decodeNnf target).Holds extended valuation :=
  Fang.QuantifiedFOF.Skolem.skolemized_extension post.2.2.2.2 reserved original

end FangSkolemCore
