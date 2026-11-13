/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import WitnessMetadata

namespace Fang.TstpText

def statusThm : Datum := .function "status" [.atom "thm"]
def nodeInfo (index : Nat) : Datum := .function "fang_node" [.natural index]
def pivotInfo (left right : Nat) : Datum := .function "pivots" [.natural left, .natural right]
def parityInfo (right : Bool) : Datum :=
  .function "renaming" [.atom (if right then "odd" else "even")]

theorem quoted_data {input text : String} (accepted : TstpExport.quote input = .ok text) :
    DataText text (.atom input) := .atom (.quoted (quote_grammar accepted))

theorem status_text : DataText "status(thm)" statusThm :=
  (function_one "status" (by decide) (.atom (checked_lower "thm" (by decide)))).spelling_eq
    (by string_shape)

theorem node_text (index : Nat) : DataText s!"fang_node({index})" (nodeInfo index) :=
  (function_one "fang_node" (by decide) (.natural (natural_spelling index))).spelling_eq
    (by string_shape)

theorem pivots_text (left right : Nat) : DataText s!"pivots({left},{right})" (pivotInfo left right) :=
  (function_two "pivots" (by decide)
    (.natural (natural_spelling left)) (.natural (natural_spelling right))).spelling_eq
      (by string_shape)

theorem parity_text (right : Bool) :
    DataText ("renaming(" ++ (if right then "odd" else "even") ++ ")") (parityInfo right) := by
  cases right
  · exact (function_one "renaming" (by decide)
      (.atom (checked_lower "even" (by decide)))).spelling_eq (by string_shape)
  · exact (function_one "renaming" (by decide)
      (.atom (checked_lower "odd" (by decide)))).spelling_eq (by string_shape)

theorem inference_text (rule : String) (valid : Frontend.lowerName rule = true)
    {infoTexts infos parentTexts parents}
    (info : DataTexts infoTexts infos) (parent : DataTexts parentTexts parents) :
    DataText ("inference(" ++ rule ++ ",[" ++ String.intercalate "," infoTexts ++
      "],[" ++ String.intercalate "," parentTexts ++ "])")
      (.function "inference" [.atom rule, .list infos, .list parents]) :=
  (function_three "inference" (by decide) (.atom (checked_lower rule valid))
    (.list info) (.list parent)).spelling_eq (by string_shape)

/-- The fields actually printed. Internal source indices have no textual
counterpart and are deliberately absent from the resulting metadata AST. -/
inductive SourceMeaning (problem : TstpExport.NamedProblem) (fileLabel : String) :
    TstpExport.Origin → Datum → Prop where
  | input (index : Nat) (sourceName : String) :
      SourceMeaning problem fileLabel (.input index sourceName)
        (.function "file" [.atom fileLabel, .atom sourceName])
  | deduplicate (nodeId sourceIndex : Nat) (parent : String) :
      SourceMeaning problem fileLabel (.deduplicate nodeId sourceIndex parent)
        (.function "inference" [.atom "fang_deduplicate",
          .list [statusThm, nodeInfo nodeId], .list [.atom parent]])
  | rename (nodeId : Nat) (right : Bool) (parent : String) :
      SourceMeaning problem fileLabel (.rename nodeId right parent)
        (.function "inference" [.atom "fang_standardize_apart",
          .list [statusThm, nodeInfo nodeId, parityInfo right], .list [.atom parent]])
  | factor (nodeId first second : Nat) (parent : String) (substitution : Subst)
      {bindings : List Datum} (witness : BindingsMeaning problem.functions substitution bindings) :
      SourceMeaning problem fileLabel (.factor nodeId first second parent substitution)
        (.function "inference" [.atom "fang_factoring",
          .list [statusThm, nodeInfo nodeId, pivotInfo first second,
            .function "fang_substitution" [.list bindings]], .list [.atom parent]])
  | resolve (nodeId leftPos rightPos : Nat) (left right : String) (substitution : Subst)
      {bindings : List Datum} (witness : BindingsMeaning problem.functions substitution bindings) :
      SourceMeaning problem fileLabel (.resolve nodeId leftPos rightPos left right substitution)
        (.function "inference" [.atom "fang_resolution",
          .list [statusThm, nodeInfo nodeId, pivotInfo leftPos rightPos,
            .function "fang_substitution" [.list bindings]], .list [.atom left, .atom right]])

inductive SourceRecord : Datum → Prop where
  | file (label name : String) : SourceRecord (.function "file" [.atom label, .atom name])
  | inference (rule : String) (info : List Datum) (parents : List String) :
      SourceRecord (.function "inference" [.atom rule, .list info, .list (parents.map Datum.atom)])

theorem SourceMeaning.record {problem label origin data}
    (h : SourceMeaning problem label origin data) : SourceRecord data := by
  cases h with
  | input index name => exact .file label name
  | deduplicate node index parent => exact .inference _ _ [parent]
  | rename node right parent => exact .inference _ _ [parent]
  | factor node first second parent substitution witness => exact .inference _ _ [parent]
  | resolve node leftPos rightPos left right substitution witness => exact .inference _ _ [left, right]

theorem source_correspondence {problem : TstpExport.NamedProblem} (fileLabel : String)
    (origin : TstpExport.Origin) {text : String}
    (accepted : TstpExport.source problem fileLabel origin = .ok text) :
    ∃ data, SourceMeaning problem fileLabel origin data ∧ DataText text data := by
  cases origin with
  | input index name =>
    cases hf : TstpExport.quote fileLabel with
    | error e => simp [TstpExport.source, hf, bind, Except.bind] at accepted
    | ok fileText =>
      cases hn : TstpExport.quote name with
      | error e => simp [TstpExport.source, hf, hn, bind, Except.bind] at accepted
      | ok nameText =>
        simp [TstpExport.source, hf, hn, bind, Except.bind, pure, Except.pure] at accepted
        subst text
        exact ⟨_, .input index name,
          (function_two "file" (by decide) (quoted_data hf) (quoted_data hn)).spelling_eq
            (by string_shape)⟩
  | deduplicate nodeId sourceIndex parent =>
    cases hp : TstpExport.quote parent with
    | error e => simp [TstpExport.source, hp, bind, Except.bind] at accepted
    | ok parentText =>
      simp [TstpExport.source, hp, bind, Except.bind, pure, Except.pure] at accepted
      subst text
      refine ⟨_, .deduplicate nodeId sourceIndex parent, ?_⟩
      exact (inference_text "fang_deduplicate" (by decide)
        (.cons status_text (.cons (node_text nodeId) .nil))
        (.cons (quoted_data hp) .nil)).spelling_eq (by string_shape)
  | rename nodeId right parent =>
    cases hp : TstpExport.quote parent with
    | error e => simp [TstpExport.source, hp, bind, Except.bind] at accepted
    | ok parentText =>
      simp [TstpExport.source, hp, bind, Except.bind, pure, Except.pure] at accepted
      subst text
      refine ⟨_, .rename nodeId right parent, ?_⟩
      exact (inference_text "fang_standardize_apart" (by decide)
        (.cons status_text (.cons (node_text nodeId) (.cons (parity_text right) .nil)))
        (.cons (quoted_data hp) .nil)).spelling_eq (by string_shape)
  | factor nodeId first second parent substitution =>
    cases hw : TstpExport.witness problem substitution with
    | error e => simp [TstpExport.source, hw, bind, Except.bind] at accepted
    | ok witnessText =>
      cases hp : TstpExport.quote parent with
      | error e => simp [TstpExport.source, hw, hp, bind, Except.bind] at accepted
      | ok parentText =>
        simp [TstpExport.source, hw, hp, bind, Except.bind, pure, Except.pure] at accepted
        subst text
        obtain ⟨bindings, meaning, grammar⟩ := witness_correspondence substitution hw
        refine ⟨_, .factor nodeId first second parent substitution meaning, ?_⟩
        exact (inference_text "fang_factoring" (by decide)
          (.cons status_text (.cons (node_text nodeId) (.cons (pivots_text first second)
            (.cons grammar .nil)))) (.cons (quoted_data hp) .nil)).spelling_eq (by string_shape)
  | resolve nodeId leftPos rightPos left right substitution =>
    cases hw : TstpExport.witness problem substitution with
    | error e => simp [TstpExport.source, hw, bind, Except.bind] at accepted
    | ok witnessText =>
      cases hl : TstpExport.quote left with
      | error e => simp [TstpExport.source, hw, hl, bind, Except.bind] at accepted
      | ok leftText =>
        cases hr : TstpExport.quote right with
        | error e => simp [TstpExport.source, hw, hl, hr, bind, Except.bind] at accepted
        | ok rightText =>
          simp [TstpExport.source, hw, hl, hr, bind, Except.bind, pure, Except.pure] at accepted
          subst text
          obtain ⟨bindings, meaning, grammar⟩ := witness_correspondence substitution hw
          refine ⟨_, .resolve nodeId leftPos rightPos left right substitution meaning, ?_⟩
          exact (inference_text "fang_resolution" (by decide)
            (.cons status_text (.cons (node_text nodeId) (.cons (pivots_text leftPos rightPos)
              (.cons grammar .nil))))
            (.cons (quoted_data hl) (.cons (quoted_data hr) .nil))).spelling_eq (by string_shape)

end Fang.TstpText
