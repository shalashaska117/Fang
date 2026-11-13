/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFConsumption
import Fang.FOF.FOFLexing
import Fang.FOF.FOFGrammar
import Fang.FOF.FOFTermGrammar
import Fang.FOF.FOFFormulaGrammar
import Fang.FOF.FOFGroundDeclarationGrammar
import Fang.FOF.FOFProblemGrammar
import Fang.FOF.FOFFormulaUniqueness
import Fang.FOF.FOFByteSemantics

#print axioms Fang.FOFFrontend.formula_consumes
#print axioms Fang.FOFFrontend.statement_consumes
#print axioms Fang.FOFFrontend.statements_consumes
#print axioms Fang.FOFFrontend.statements_exhaust
#print axioms Fang.FOFFrontend.decode_exhausts
#print axioms Fang.FOFFrontend.fof_lexAux_sound
#print axioms Fang.FOFFrontend.fof_lexAux_complete
#print axioms Fang.FOFFrontend.fof_tokenize_iff
#print axioms Fang.FOFGrammar.TermTokens.suffix
#print axioms Fang.FOFGrammar.ArgumentsTokens.suffix
#print axioms Fang.FOFGrammar.FormulaTokens.suffix
#print axioms Fang.FOFGrammar.FormulaTokens.consumes
#print axioms Fang.FOFFrontend.raw_term_grammar
#print axioms Fang.FOFFrontend.raw_terms_grammar
#print axioms Fang.FOFFrontend.raw_atom_grammar
#print axioms Fang.FOFFrontend.raw_formula_grammar
#print axioms Fang.FOFFrontend.raw_formula_ground
#print axioms Fang.FOFFrontend.fof_tokenize_bytes_iff
#print axioms Fang.FOFFrontend.fof_tokenize_offsets
#print axioms Fang.FOFFrontend.FofTokenization.token_ascii
#print axioms Fang.FOFFrontend.raw_ground_statement_grammar
#print axioms Fang.FOFFrontend.raw_statement_grammar
#print axioms Fang.FOFFrontend.raw_statements_grammar
#print axioms Fang.FOFFrontend.decode_byte_grammar
#print axioms Fang.FOFGrammar.FormulaTokens.unique
#print axioms Fang.FOFGrammar.GroundDeclarationTokens.unique
#print axioms Fang.FOFGrammar.DeclarationTokens.unique
#print axioms Fang.FOFGrammar.DeclarationsTokens.unique
#print axioms Fang.FOFFrontend.FofByteTokenization.unique
#print axioms Fang.FOFGrammar.Parses.unique
#print axioms Fang.FOFFrontend.decode_prepared_satisfiable_iff
#print axioms Fang.FOFFrontend.decode_check_original_unsat
