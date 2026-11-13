/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit of the model modules. The examples restate each endpoint with its exact type: the native model entries
   run the decoders and frames of the native refutation checkers (`decodeBytesLimited` at
   `NativeLimits.declarationLimit`, `BundleLimit.limited`, `V3.limited`), and acceptance concludes the positive meaning
   for the original bytes, with no premise about the certificate. Statements are decided by the step-counted
   evaluation of their rewritten forms (`ModelSteps`, `ModelRewrite`). The document exports restate what a printed
   finite model document is (`ModelExport`), and that the document determines the model (`ModelExportComplete`).
   Every theorem of the model modules is then audited for its axioms. -/
import ModelExclusive
import ModelControls
import ModelRewriteControls
import ModelExportControls
import ModelExportComplete

namespace Fang.TptpCandidate.FullFof.Model.Audit
open Fang.TptpCandidate.FullFof.Model

/-- Single file: a model of the original bytes. -/
example {limits : Limits} {bytes : List UInt8} {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsSingle limits Fang.NativeLimits.declarationLimit bytes maximumBytes certificate = .ok ()) :
    CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  acceptsSingle_satisfiable accepted

/-- Bundle: a model of the expanded bundle that keeps distinct objects apart, under the native bundle frame. -/
example {limits : Limits} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsBundle limits Coverage.BundleLimit.limited files maximumBytes certificate = .ok ()) :
    Coverage.FramerLimit.ByteBundleSatisfiable Coverage.BundleLimit.limitedSpecification files maximumBytes
      Coverage.BundleV8.bundleFuel :=
  acceptsBundleLimited_satisfiable accepted

/-- Signed bundle without a selected conjecture: a model of the positive inputs. -/
example {limits : Limits} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsInputs limits Roles.Bundle.V3.limited files maximumBytes certificate = .ok ()) :
    ∃ bundle items, Roles.Bundle.V3.Expanded Roles.Bundle.V3.limitedSpecification files maximumBytes
        Roles.Bundle.bundleFuel bundle items ∧ Roles.Bundle.goalItems bundle items = [] ∧
      ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Coverage.FramerV2.NamedSeparated model (Roles.Bundle.V2.objectsOf bundle items) ∧
        Roles.AllHold (Roles.Bytes.sentence (D := D))
          (Roles.positiveInputs (Roles.Bytes.source (Roles.Bundle.entriesOf bundle items))) model :=
  acceptsInputsLimited_satisfiable accepted

/-- Signed bundle with selected conjectures: the returned item is a selected conjecture that fails in a model of the
    selected premises. -/
example {limits : Limits} {files : List (Coverage.Key × List UInt8)} {maximumBytes index : Nat}
    {certificate : String} {item : Coverage.Item}
    (accepted : acceptsGoal limits Roles.Bundle.V3.limited files maximumBytes index certificate = .ok item) :
    ∃ bundle items entry, Roles.Bundle.V3.Expanded Roles.Bundle.V3.limitedSpecification files maximumBytes
        Roles.Bundle.bundleFuel bundle items ∧ (item, entry) ∈ Roles.Bundle.goalItems bundle items ∧
      ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Coverage.FramerV2.NamedSeparated model (Roles.Bundle.V2.objectsOf bundle items) ∧
        Roles.AllHold (Roles.Bytes.sentence (D := D))
          (Roles.premises (Roles.Bytes.source (Roles.Bundle.entriesOf bundle items))) model ∧
        ¬ Roles.Bytes.sentence model entry.original.body.formula :=
  acceptsGoalLimited_countermodel accepted

/-- Single-file document: printed only after acceptance, true in the accepted model with its element names. -/
example {limits : Limits} {layout : Layout} {declarationLimit : Nat} {bytes : List UInt8} {maximumBytes : Nat}
    {certificate text : String}
    (exported : exportSingle limits layout declarationLimit bytes maximumBytes certificate = .ok text) :
    CnfBoolean.BytesSatisfiable bytes maximumBytes ∧
      ∃ values model, Integration.decodeBytesLimited declarationLimit bytes maximumBytes = .ok values ∧
        readModel limits certificate (source values) = .ok model ∧
        (∀ formula ∈ source values, ∀ valuation, formula.Holds model.interpretation valuation) ∧
        Describes layout model (source values) none text :=
  exportSingle_describes exported

/-- Bundle document under the native bundle frame. -/
example {limits : Limits} {layout : Layout} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat}
    {certificate text : String} (exported : exportBundle limits layout files maximumBytes certificate = .ok text) :
    Coverage.FramerLimit.ByteBundleSatisfiable Coverage.BundleLimit.limitedSpecification files maximumBytes
        Coverage.BundleV8.bundleFuel ∧
      ∃ bundle items model, Coverage.BundleLimit.limitedSpecification files maximumBytes = .ok bundle ∧
        Coverage.expand bundle Coverage.BundleV8.bundleFuel = .ok items ∧
        readModel limits certificate (source (Coverage.declarationsOf bundle items)) = .ok model ∧
        (∀ formula ∈ source (Coverage.declarationsOf bundle items), ∀ valuation,
          formula.Holds model.interpretation valuation) ∧
        Describes layout model (source (Coverage.declarationsOf bundle items)) none text :=
  exportBundle_describes exported

/-- Document of a signed bundle without conjectures under the role frame. -/
example {limits : Limits} {layout : Layout} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat}
    {certificate text : String} (exported : exportInputs limits layout files maximumBytes certificate = .ok text) :
    Roles.Bundle.V3.ByteInputsSatisfiable Roles.Bundle.V3.limitedSpecification files maximumBytes
        Roles.Bundle.bundleFuel ∧
      ∃ read model, readRoles Roles.Bundle.V3.limitedSpecification files maximumBytes = .ok read ∧
        readModel limits certificate (roleStatements read.1 read.2) = .ok model ∧
        (∀ formula ∈ (Roles.positiveInputs (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
          Roles.Declaration.original, ∀ valuation, formula.Holds model.interpretation valuation) ∧
        Describes layout model (roleStatements read.1 read.2) none text :=
  exportInputs_describes exported

/-- Countermodel document under the role frame: the premises hold, the selected conjecture fails, and the comment
    names it. -/
example {limits : Limits} {layout : Layout} {files : List (Coverage.Key × List UInt8)} {maximumBytes index : Nat}
    {certificate text : String} (exported : exportGoal limits layout files maximumBytes index certificate = .ok text) :
    Roles.Bundle.V3.ByteCounterSatisfiable Roles.Bundle.V3.limitedSpecification files maximumBytes
        Roles.Bundle.bundleFuel ∧
      ∃ read pair model comment, readRoles Roles.Bundle.V3.limitedSpecification files maximumBytes = .ok read ∧
        (Roles.Bundle.goalItems read.1 read.2)[index]? = some pair ∧
        goalComment pair.2.original.name = .ok comment ∧
        readModel limits certificate (roleStatements read.1 read.2) = .ok model ∧
        (∀ formula ∈ (Roles.premises (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
          Roles.Declaration.original, ∀ valuation, formula.Holds model.interpretation valuation) ∧
        (¬ ∀ valuation, pair.2.original.body.formula.Holds model.interpretation valuation) ∧
        Describes layout model (roleStatements read.1 read.2) (some comment) text :=
  exportGoal_describes exported

/-- The printed document determines the model: an interpretation in which its statements hold and its element names
    stay apart renames the accepted model on every described symbol, and on the input distinct objects when the model
    keeps them apart. -/
example {limits : Limits} {layout : Layout} {model : FiniteModel} {statements : List Formula} {objects : List String}
    {comment : Option String} {text : String}
    (exported : exportDocument limits layout model statements objects comment = .ok text) :
    ∃ names rows, documentText false comment rows = .ok text ∧
      ∀ (D : Type) (J : Source.Interpretation D), (∀ row ∈ rows, ∀ valuation, row.formula.Holds J valuation) →
        NamesApart J names →
        Function.Injective (elementOf J model names) ∧ Function.Surjective (elementOf J model names) ∧
        (∀ symbol ∈ describedFunctions statements, ∀ cells : List model.Element, cells.length = symbol.2 →
          J.function symbol.1 (cells.map (elementOf J model names)) =
            elementOf J model names (model.function symbol.1 cells)) ∧
        (∀ symbol ∈ describedPredicates statements, ∀ cells : List model.Element, cells.length = symbol.2 →
          (J.predicate symbol.1 (cells.map (elementOf J model names)) ↔ model.predicate symbol.1 cells = true)) ∧
        (separated model objects = true → ∀ object ∈ objects,
          J.function object [] = elementOf J model names (model.function object [])) :=
  exportDocument_determines exported

end Fang.TptpCandidate.FullFof.Model.Audit

#print axioms Fang.TptpCandidate.FullFof.Model.evalFormula_iff
#print axioms Fang.TptpCandidate.FullFof.Model.term_eval_agree
#print axioms Fang.TptpCandidate.FullFof.Model.update_agree
#print axioms Fang.TptpCandidate.FullFof.Model.holds_agree
#print axioms Fang.TptpCandidate.FullFof.Model.termWithin_iff
#print axioms Fang.TptpCandidate.FullFof.Model.termsWithin_iff
#print axioms Fang.TptpCandidate.FullFof.Model.formulaWithin_iff
#print axioms Fang.TptpCandidate.FullFof.Model.evalAll_complete
#print axioms Fang.TptpCandidate.FullFof.Model.evalAll_sound
#print axioms Fang.TptpCandidate.FullFof.Model.sentenceValue_iff
#print axioms Fang.TptpCandidate.FullFof.Model.separated_iff
#print axioms Fang.TptpCandidate.FullFof.Model.checkFrom_sound
#print axioms Fang.TptpCandidate.FullFof.Model.bind_ok
#print axioms Fang.TptpCandidate.FullFof.Model.mapError_ok
#print axioms Fang.TptpCandidate.FullFof.Model.update_same
#print axioms Fang.TptpCandidate.FullFof.Model.update_comm
#print axioms Fang.TptpCandidate.FullFof.Model.term_update_eval
#print axioms Fang.TptpCandidate.FullFof.Model.terms_update_eval
#print axioms Fang.TptpCandidate.FullFof.Model.holds_update_absent
#print axioms Fang.TptpCandidate.FullFof.Model.fallbackAll_holds
#print axioms Fang.TptpCandidate.FullFof.Model.fallbackEx_holds
#print axioms Fang.TptpCandidate.FullFof.Model.absent_of_not
#print axioms Fang.TptpCandidate.FullFof.Model.push_holds
#print axioms Fang.TptpCandidate.FullFof.Model.curryImplies_holds
#print axioms Fang.TptpCandidate.FullFof.Model.rewrite_holds
#print axioms Fang.TptpCandidate.FullFof.Model.allSteps_value
#print axioms Fang.TptpCandidate.FullFof.Model.anySteps_value
#print axioms Fang.TptpCandidate.FullFof.Model.evalSteps_value
#print axioms Fang.TptpCandidate.FullFof.Model.assignSteps_value
#print axioms Fang.TptpCandidate.FullFof.Model.sentenceSteps_iff
#print axioms Fang.TptpCandidate.FullFof.Model.checkSteps_sound
#print axioms Fang.TptpCandidate.FullFof.Model.checkAll_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.inputsSatisfiable_not_unsatisfiable
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.countermodel_not_entailed
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.counterSatisfiable_not_theorem
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsSingle_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsBundle_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsBundleLimited_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Model.readRoles_expanded
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsInputs_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsInputsLimited_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsGoal_countermodel
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsGoalLimited_countermodel
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsGoalLimited_counterSatisfiable
#print axioms Fang.TptpCandidate.FullFof.Model.single_exclusive
#print axioms Fang.TptpCandidate.FullFof.Model.bundle_exclusive
#print axioms Fang.TptpCandidate.FullFof.Model.inputs_exclusive
#print axioms Fang.TptpCandidate.FullFof.Model.goal_exclusive
#print axioms Fang.TptpCandidate.FullFof.Model.goal_not_theorem
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.single_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.single_meaning
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.single_false_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.single_missing_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.single_unused_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.clause_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.clause_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.quantifiers_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.quantifiers_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.work_refused
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.objects_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.objects_collide_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.inputs_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.inputs_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.goal_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.goal_holds_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.goal_index_rejected
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.static_estimate_refuses
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.steps_accept
#print axioms Fang.TptpCandidate.FullFof.Model.Controls.steps_run_out
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_swap_all
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_swap_ex
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_conj
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_ex_disj
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_disj_right
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_disj_left
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_ex_conj_right
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_implies_antecedent
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_implies_consequent
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_ex_implies
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_reverse
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_nor
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_ex_nand
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_neg
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_vacuous
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_curry
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_all_iff
#print axioms Fang.TptpCandidate.FullFof.Model.RewriteControls.rewrite_injectivity
#print axioms Fang.TptpCandidate.FullFof.Model.firstOccurrences_mem
#print axioms Fang.TptpCandidate.FullFof.Model.firstOccurrences_nodup
#print axioms Fang.TptpCandidate.FullFof.Model.mem_allFunctions
#print axioms Fang.TptpCandidate.FullFof.Model.mem_describedFunctions
#print axioms Fang.TptpCandidate.FullFof.Model.mem_describedPredicates
#print axioms Fang.TptpCandidate.FullFof.Model.describedFunctions_nodup
#print axioms Fang.TptpCandidate.FullFof.Model.describedPredicates_nodup
#print axioms Fang.TptpCandidate.FullFof.Model.insertNames_other
#print axioms Fang.TptpCandidate.FullFof.Model.insertNames_at
#print axioms Fang.TptpCandidate.FullFof.Model.named_element
#print axioms Fang.TptpCandidate.FullFof.Model.elementTerm_eval
#print axioms Fang.TptpCandidate.FullFof.Model.named_function_agree
#print axioms Fang.TptpCandidate.FullFof.Model.eval_functions_agree
#print axioms Fang.TptpCandidate.FullFof.Model.holds_functions_agree
#print axioms Fang.TptpCandidate.FullFof.Model.named_holds_iff
#print axioms Fang.TptpCandidate.FullFof.Model.tuples_complete
#print axioms Fang.TptpCandidate.FullFof.Model.chainOf_conj
#print axioms Fang.TptpCandidate.FullFof.Model.chainOf_disj
#print axioms Fang.TptpCandidate.FullFof.Model.chainAll_conj
#print axioms Fang.TptpCandidate.FullFof.Model.chainAll_disj
#print axioms Fang.TptpCandidate.FullFof.Model.treeWith_conj
#print axioms Fang.TptpCandidate.FullFof.Model.treeWith_disj
#print axioms Fang.TptpCandidate.FullFof.Model.treeOf_conj
#print axioms Fang.TptpCandidate.FullFof.Model.treeOf_disj
#print axioms Fang.TptpCandidate.FullFof.Model.variablesFor_length
#print axioms Fang.TptpCandidate.FullFof.Model.closeAll_holds
#print axioms Fang.TptpCandidate.FullFof.Model.argumentsOf_eval
#print axioms Fang.TptpCandidate.FullFof.Model.functionCell_holds
#print axioms Fang.TptpCandidate.FullFof.Model.predicateCell_holds
#print axioms Fang.TptpCandidate.FullFof.Model.bindings_hold
#print axioms Fang.TptpCandidate.FullFof.Model.defaultFormula_holds
#print axioms Fang.TptpCandidate.FullFof.Model.symbolRows_hold
#print axioms Fang.TptpCandidate.FullFof.Model.domainFormula_holds
#print axioms Fang.TptpCandidate.FullFof.Model.functionRows_hold
#print axioms Fang.TptpCandidate.FullFof.Model.predicateRows_hold
#print axioms Fang.TptpCandidate.FullFof.Model.documentRows_hold
#print axioms Fang.TptpCandidate.FullFof.Model.buildDocument_facts
#print axioms Fang.TptpCandidate.FullFof.Model.framedFormulas_rows
#print axioms Fang.TptpCandidate.FullFof.Model.exportDocument_describes
#print axioms Fang.TptpCandidate.FullFof.Model.mapError_ok_of
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsSingle_holds
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsBundle_holds
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsInputs_holds
#print axioms Fang.TptpCandidate.FullFof.Model.acceptsGoal_holds
#print axioms Fang.TptpCandidate.FullFof.Model.exportSingle_describes
#print axioms Fang.TptpCandidate.FullFof.Model.exportBundle_describes
#print axioms Fang.TptpCandidate.FullFof.Model.exportInputs_describes
#print axioms Fang.TptpCandidate.FullFof.Model.exportGoal_describes
#print axioms Fang.TptpCandidate.FullFof.Model.chainOf_conj_leaves
#print axioms Fang.TptpCandidate.FullFof.Model.chainOf_disj_some
#print axioms Fang.TptpCandidate.FullFof.Model.chainAll_conj_leaves
#print axioms Fang.TptpCandidate.FullFof.Model.chainAll_disj_some
#print axioms Fang.TptpCandidate.FullFof.Model.treeWith_conj_leaves
#print axioms Fang.TptpCandidate.FullFof.Model.treeWith_disj_some
#print axioms Fang.TptpCandidate.FullFof.Model.treeOf_conj_leaves
#print axioms Fang.TptpCandidate.FullFof.Model.treeOf_disj_some
#print axioms Fang.TptpCandidate.FullFof.Model.closeAll_inverse
#print axioms Fang.TptpCandidate.FullFof.Model.assign_map
#print axioms Fang.TptpCandidate.FullFof.Model.map_injective
#print axioms Fang.TptpCandidate.FullFof.Model.variablesFor_nodup
#print axioms Fang.TptpCandidate.FullFof.Model.tuples_length
#print axioms Fang.TptpCandidate.FullFof.Model.tuples_kept
#print axioms Fang.TptpCandidate.FullFof.Model.elementTerm_eval_in
#print axioms Fang.TptpCandidate.FullFof.Model.argumentsOf_eval_in
#print axioms Fang.TptpCandidate.FullFof.Model.functionCell_in
#print axioms Fang.TptpCandidate.FullFof.Model.predicateCell_in
#print axioms Fang.TptpCandidate.FullFof.Model.bindings_values
#print axioms Fang.TptpCandidate.FullFof.Model.elementOf_injective
#print axioms Fang.TptpCandidate.FullFof.Model.domainFormula_surjective
#print axioms Fang.TptpCandidate.FullFof.Model.defaultFormula_fallback
#print axioms Fang.TptpCandidate.FullFof.Model.functionRows_determine
#print axioms Fang.TptpCandidate.FullFof.Model.predicateRows_determine
#print axioms Fang.TptpCandidate.FullFof.Model.symbolRows_find
#print axioms Fang.TptpCandidate.FullFof.Model.documentRows_determine
#print axioms Fang.TptpCandidate.FullFof.Model.buildDocument_checks
#print axioms Fang.TptpCandidate.FullFof.Model.elementName_object
#print axioms Fang.TptpCandidate.FullFof.Model.elementNames_getD
#print axioms Fang.TptpCandidate.FullFof.Model.exportDocument_determines
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.single_document
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.single_document_meaning
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.inputs_document
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.bundle_objects_document
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.stem_avoids_objects
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.goal_document
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.default_document
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.predicate_default_document
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.export_fails_model_accepted
#print axioms Fang.TptpCandidate.FullFof.Model.ExportControls.rejected_no_document
