/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ExpandedDocument

namespace Fang.QuantifiedEqualityTstp.Expanded.DocumentControls
open Fang.TptpCandidate Fang.TptpCandidate.FullFof

theorem integer_parent : (parentText (.integer "12")).toOption = some "12" := by decide +kernel

theorem quoted_parent : (parentText (.atom "12")).toOption = some "'12'" := by decide +kernel

theorem escaped_parent : (parentText (.atom "it's")).toOption = some "'it\\'s'" := by decide +kernel

theorem leading_zero_rejected : (parentText (.integer "012")).toOption = none := by decide +kernel

theorem signed_integer_rejected : (parentText (.integer "+1")).toOption = none := by decide +kernel

theorem sap_parents :
    ((([.atom "a", .integer "12"] : List Name).mapM parentText).map groupAnnotation).toOption =
      some "inference(fang_preprocessing,[status(sap)],['a',12])" := by
  decide +kernel

/-- `12` and `'12'` are different TPTP names. -/
theorem integer_and_quoted_distinct : (documentNames [.integer "12", .atom "12"] "g" ["c1"]).Nodup := by
  decide +kernel

theorem group_collision_rejected : ¬ (documentNames [.atom "a"] "a" ["c1"]).Nodup := by decide +kernel

theorem row_collision_rejected : ¬ (documentNames [.atom "a"] "g" ["a"]).Nodup := by decide +kernel

theorem small_text_kept : (capText "fof(a,axiom,p).\n").toOption = some "fof(a,axiom,p).\n" := by
  decide +kernel

theorem capText_rejects {text : String} (over : maximumDocumentBytes < text.utf8ByteSize) :
    capText text = .error "resource-exhaustion: TSTP document exceeds 16 MiB" := by
  unfold capText
  split
  · rename_i capped
    exact absurd capped (Nat.not_le_of_lt over)
  · rfl

theorem first_prefix_free : freshPrefix [] "f" "n" = "fn" := by decide +kernel

/-- `skf` and `sk_f` start taken spellings, so the third candidate is chosen. -/
theorem taken_prefixes_skipped : freshPrefix ["skf", "sk_f1", "sk"] "sk" "f" = "sk__f" := by decide +kernel

#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.integer_parent
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.quoted_parent
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.escaped_parent
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.leading_zero_rejected
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.signed_integer_rejected
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.sap_parents
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.integer_and_quoted_distinct
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.group_collision_rejected
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.row_collision_rejected
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.small_text_kept
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.capText_rejects
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.first_prefix_free
#print axioms Fang.QuantifiedEqualityTstp.Expanded.DocumentControls.taken_prefixes_skipped

end Fang.QuantifiedEqualityTstp.Expanded.DocumentControls
