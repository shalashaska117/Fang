/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.Ancestry
import Fang.FOF.TSTP.SourceIdentity
import Fang.FOF.TSTP.PrefixLexer
import Fang.FOF.TSTP.FormulaPrefix
import Fang.FOF.TSTP.PrefixBridge
import Fang.FOF.TSTP.CompoundPrefix
import Fang.FOF.TSTP.FormulaRows
import Fang.FOF.TSTP.MixedRows
import Fang.FOF.TSTP.RenderProcess
import Fang.FOF.TSTP.RenderGrammar
import Fang.FOF.TSTP.BuildTrace
import Fang.FOF.TSTP.RenderEndpoint
import Fang.FOF.TSTP.GuardControls
import Fang.FOF.TSTP.RenderEvents
import Fang.FOF.TSTP.EventSources
import Fang.FOF.TSTP.EventProjection
import Fang.FOF.TSTP.EventParents
import Fang.FOF.TSTP.EventDecoding
import Fang.FOF.TSTP.ParsedEndpoint
import Fang.FOF.TSTP.CheckedText

#print axioms Fang.FofTstpExport.declarationLeaves_origin
#print axioms Fang.FofTstpExport.collectLeaves_origin
#print axioms Fang.FofTstpExport.leaves_origin
#print axioms Fang.FofTstpExport.build_source
#print axioms Fang.FofTstpExport.build_checked
#print axioms Fang.FofTstpExport.export_original_unsat
#print axioms Fang.FofTstpExport.clausification_consequence
#print axioms Fang.FofTstpExport.indexed_clausification_consequence
#print axioms Fang.FofTstpExport.original_declaration_consequence
#print axioms Fang.FofTstpExport.build_leaf_consequence

#print axioms Fang.FofTstpText.formula_correspondence
#print axioms Fang.FofTstpText.symbol_name
#print axioms Fang.FofTstpText.term_meaning
#print axioms Fang.FofTstpText.terms_meaning
#print axioms Fang.FofTstpText.NamedFormula.holds
#print axioms Fang.FofTstpText.printed_formula_meaning
#print axioms Fang.FofTstpText.source_formula_correspondence
#print axioms Fang.FofTstpText.clausification_record
#print axioms Fang.FofTstpText.clausified_row_correspondence
#print axioms Fang.FofTstpText.ground_term_identity
#print axioms Fang.FofTstpText.ground_terms_identity
#print axioms Fang.FofTstpText.ground_formula_identity
#print axioms Fang.FofTstpText.source_row_identity
#print axioms Fang.FofTstpPrefix.read_old
#print axioms Fang.FofTstpPrefix.read_unique
#print axioms Fang.FofTstpPrefix.read_conjunction
#print axioms Fang.FofTstpPrefix.read_implication
#print axioms Fang.FofTstpPrefix.read_truth
#print axioms Fang.FofTstpPrefix.truth_requires_word_boundary
#print axioms Fang.FofTstpPrefix.implication_requires_both_chars
#print axioms Fang.FofTstpPrefix.Connective.token_injective
#print axioms Fang.FofTstpPrefix.atom_read
#print axioms Fang.FofTstpPrefix.FormulaPrefix.unique
#print axioms Fang.FofTstpPrefix.read_space
#print axioms Fang.FofTstpPrefix.empty_prefix_read
#print axioms Fang.FofTstpPrefix.term_terminal_prefix
#print axioms Fang.FofTstpPrefix.atom_text_prefix
#print axioms Fang.FofTstpPrefix.FormulaPrefix.whitespace
#print axioms Fang.FofTstpPrefix.read_operator
#print axioms Fang.FofTstpPrefix.formula_text_prefix
#print axioms Fang.FofTstpPrefix.printed_formula_prefix
#print axioms Fang.FofTstpText.ParsedFormulaRow.unique
#print axioms Fang.FofTstpText.FormulaRowText.prefix
#print axioms Fang.FofTstpText.FormulaRowText.prefix_unique
#print axioms Fang.FofTstpText.source_formula_parses
#print axioms Fang.FofTstpText.ParsedFormulaRow.nonempty
#print axioms Fang.FofTstpText.ParsedFormulaRow.not_cnf
#print axioms Fang.FofTstpText.ParsedMixedRow.nonempty
#print axioms Fang.FofTstpText.ParsedMixedRow.unique
#print axioms Fang.FofTstpText.MixedRowText.prefix
#print axioms Fang.FofTstpText.ParsedMixedRows.unique
#print axioms Fang.FofTstpText.mixed_rows_parse
#print axioms Fang.FofTstpText.mixed_rows_unique
#print axioms Fang.FofTstpExport.RenderProof.render_eq_run
#print axioms Fang.FofTstpExport.RenderProof.LinesHaveSyntax.append_row
#print axioms Fang.FofTstpExport.RenderProof.process_preserves_syntax
#print axioms Fang.FofTstpExport.RenderProof.forIn_preserves_syntax
#print axioms Fang.FofTstpExport.RenderProof.render_syntax
#print axioms Fang.FofTstpExport.RenderProof.render_unique_parse
#print axioms Fang.TstpExport.BuilderProof.lower_names_disjoint
#print axioms Fang.TstpExport.BuilderProof.generated_fresh_disjoint
#print axioms Fang.TstpExport.BuilderProof.source_fresh_disjoint
#print axioms Fang.TstpExport.BuilderProof.row_invariant_input_disjoint
#print axioms Fang.TstpExport.BuilderProof.row_invariant_generated_disjoint
#print axioms Fang.TstpExport.BuilderProof.row_invariant_resolution_disjoint
#print axioms Fang.TstpExport.BuilderProof.process_derives_disjoint
#print axioms Fang.TstpExport.BuilderProof.forIn_zipIdx_derives_disjoint
#print axioms Fang.TstpExport.BuilderProof.runCollector_derives_disjoint
#print axioms Fang.TstpExport.BuilderProof.collect_derives_disjoint
#print axioms Fang.TstpExport.BuilderProof.build_derivation_disjoint
#print axioms Fang.TstpExport.BuilderProof.decoded_build_derivation_disjoint
#print axioms Fang.FofTstpExport.leaf_name_chars
#print axioms Fang.FofTstpExport.leaf_name_injective
#print axioms Fang.FofTstpExport.leaf_name_not_lower
#print axioms Fang.FofTstpExport.source_leaf_distinct
#print axioms Fang.FofTstpExport.leaf_generated_distinct
#print axioms Fang.FofTstpExport.declarationLeaves_names_nodup
#print axioms Fang.FofTstpExport.collectLeaves_lower_sources
#print axioms Fang.FofTstpExport.collectLeaves_generated_disjoint
#print axioms Fang.FofTstpExport.collectLeaves_names_nodup
#print axioms Fang.FofTstpExport.build_trace
#print axioms Fang.FofTstpExport.build_trace_endpoint
#print axioms Fang.FofTstpExport.build_typed_derivation
#print axioms Fang.FofTstpExport.decoded_source_names_unique
#print axioms Fang.FofTstpExport.decoded_build_typed_derivation
#print axioms Fang.FofTstpExport.RenderProof.process_ends
#print axioms Fang.FofTstpExport.RenderProof.forIn_ends
#print axioms Fang.FofTstpExport.RenderProof.render_ends
#print axioms Fang.FofTstpExport.RenderProof.built_render_empty_endpoint
#print axioms Fang.FofTstpExport.GuardControls.missing_leaf_rejected
#print axioms Fang.FofTstpExport.GuardControls.changed_name_rejected
#print axioms Fang.FofTstpExport.GuardControls.changed_nested_term_rejected
#print axioms Fang.FofTstpExport.GuardControls.matching_empty_clause_printed
#print axioms Fang.FofTstpExport.RenderProof.process_events
#print axioms Fang.FofTstpExport.RenderProof.forIn_events
#print axioms Fang.FofTstpExport.RenderProof.render_events
#print axioms Fang.FofTstpExport.RenderProof.leaf_source_unique
#print axioms Fang.FofTstpExport.RenderProof.SourcesReady.append
#print axioms Fang.FofTstpExport.RenderProof.row_events_sources
#print axioms Fang.FofTstpExport.RenderProof.SourcesBefore.append
#print axioms Fang.FofTstpExport.RenderProof.trace_events_sources
#print axioms Fang.FofTstpExport.RenderProof.built_render_sources
#print axioms Fang.FofTstpExport.RenderProof.row_events_clause_view
#print axioms Fang.FofTstpExport.RenderProof.trace_events_clause_view
#print axioms Fang.FofTstpExport.RenderProof.row_events_original
#print axioms Fang.FofTstpExport.RenderProof.trace_events_original
#print axioms Fang.FofTstpExport.RenderProof.original_clausification_valid
#print axioms Fang.FofTstpExport.RenderProof.parent_in_events
#print axioms Fang.FofTstpExport.RenderProof.justified_in_events
#print axioms Fang.FofTstpExport.RenderProof.trace_events_split
#print axioms Fang.FofTstpExport.RenderProof.trace_events_singleton
#print axioms Fang.FofTstpExport.RenderProof.derivation_in_events
#print axioms Fang.FofTstpExport.RenderProof.decoded_render_derivation
#print axioms Fang.FofTstpExport.RenderProof.event_text_decode
#print axioms Fang.FofTstpExport.RenderProof.events_text_decode
#print axioms Fang.FofTstpExport.RenderProof.decoded_render_unique_derivation
#print axioms Fang.FofTstpExport.RenderProof.export_text_unique_derivation
#print axioms Fang.FofTstpExport.RenderProof.row_events_last
#print axioms Fang.FofTstpExport.RenderProof.trace_events_last
#print axioms Fang.FofTstpExport.RenderProof.related_last_event
#print axioms Fang.FofTstpExport.RenderProof.EventMeaning.empty_clause
#print axioms Fang.FofTstpExport.RenderProof.decoded_render_parsed_endpoint
#print axioms Fang.FofTstpExport.RenderProof.collected_name_class
#print axioms Fang.FofTstpExport.RenderProof.builder_name_class
#print axioms Fang.FofTstpExport.RenderProof.fof_builder_name_class
#print axioms Fang.FofTstpExport.RenderProof.source_leaf_name_distinct
#print axioms Fang.FofTstpExport.RenderProof.source_clause_name_distinct
#print axioms Fang.FofTstpExport.RenderProof.trace_source_ids_fresh
#print axioms Fang.FofTstpExport.RenderProof.source_name_member
#print axioms Fang.FofTstpExport.RenderProof.name_member_class
#print axioms Fang.FofTstpExport.RenderProof.partition_names_nodup
#print axioms Fang.FofTstpExport.RenderProof.source_names_related
#print axioms Fang.FofTstpExport.RenderProof.related_lookup_nodup
#print axioms Fang.FofTstpExport.RenderProof.derivation_names_nodup
#print axioms Fang.FofTstpExport.RenderProof.trace_clause_names
#print axioms Fang.FofTstpExport.RenderProof.rendered_event_names_nodup
#print axioms Fang.FofTstpExport.RenderProof.decoded_original_tables
#print axioms Fang.FofTstpExport.RenderProof.related_index_right
#print axioms Fang.FofTstpExport.RenderProof.source_event_original_identity
#print axioms Fang.FofTstpExport.RenderProof.EventMeaning.name_eq
#print axioms Fang.FofTstpExport.RenderProof.event_meaning_names
#print axioms Fang.FofTstpExport.RenderProof.decoded_render_checked_text
