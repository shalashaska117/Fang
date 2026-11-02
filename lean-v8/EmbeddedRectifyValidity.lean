/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedPublicRectification

namespace FangSkolemEmbeddedCore
open Aeneas.Std fang_skolem_core.fang_quantified_fof_core

/-- Renaming preserves the signature; all target IDs are admitted in this helper. -/
theorem termRenaming_signature {resolve source target} (renamed : TermRenaming resolve source target)
    (signature : Signature) (allowed : U32 → Prop) (valid : ScopedTerm signature allowed source) :
    ScopedTerm signature (fun _ => True) target := by
  induction renamed with
  | var id fresh binding => exact .var fresh trivial
  | fun_ symbol args target length children ih =>
    cases valid with
    | fun_ _ _ arity sourceChildren =>
      exact .fun_ symbol target (by simpa [length] using arity)
        (fun i hi => ih i (by omega) hi (sourceChildren i (by omega)))

theorem rectified_signature {resolve first source target last}
    (renamed : RectifiedFormula resolve first source target last)
    (signature : Signature) (allowed : U32 → Prop) (valid : FormulaValid signature allowed source) :
    FormulaValid signature (fun _ => True) target := by
  induction renamed generalizing allowed with
  | atom next predicate args target length children =>
    exact ⟨by simpa [length] using valid.1,
      fun i hi => termRenaming_signature (children i (by omega) hi) signature allowed (valid.2 i (by omega))⟩
  | truth next | falsity next => trivial
  | negation child ih => exact ih allowed valid
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    exact ⟨il allowed valid.1, ir allowed valid.2⟩
  | @universal resolve first last id fresh body target position child ih
    | @existential resolve first last id fresh body target position child ih =>
    exact (formulaValid_congr signature target (fun _ => True)
      (fun varId => fresh = varId ∨ True) (fun _ => by simp)).mp
        (ih (fun varId => id = varId ∨ allowed varId) valid)

end FangSkolemEmbeddedCore
