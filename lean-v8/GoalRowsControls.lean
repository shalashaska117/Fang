/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed goal-row controls. Each positive row is the exact text returned after
   the accepted lexer has checked every token kind. -/
import GoalRows

namespace Fang.TptpCandidate.FullFof.GoalRows.Controls
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.GoalRows

def declaration (name : Name) (body : Body) : Declaration := ⟨name, body, 0, 0, 0, 0⟩

def entry (name : String) (role : Roles.Role) : Roles.Bytes.Entry :=
  ⟨declaration (.atom name) (.fof (.atom "p" [])), role, 0, 0⟩

def p : Formula := .atom "p" []
def q : Formula := .atom "q" []

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

theorem role_words :
    [Roles.Role.axiomRole, .hypothesis, .definition, .assumption, .lemma, .theoremRole, .corollary, .conjecture,
      .negatedConjecture, .plain, .typeRole, .interpretation, .logic, .unknown].map roleWord =
      ["axiom", "hypothesis", "definition", "assumption", "lemma", "theorem", "corollary", "conjecture",
        "negated_conjecture", "plain", "type", "interpretation", "logic", "unknown"] := rfl

theorem negated_row_text :
    negatedRow "goal_negated" (.atom "goal") (.pair .implies p q) =
      .ok "fof ( goal_negated , negated_conjecture , ( ~ ( p => q ) ) , inference ( negate_conjecture , [ status ( cth ) ] , [ goal ] ) ) ." := by cbv

theorem negated_quoted_goal :
    negatedRow "n" (.atom "it's a\\b") (.all "X" (.atom "p" [.var "X"])) =
      .ok "fof ( n , negated_conjecture , ( ~ ! [ X ] : p ( X ) ) , inference ( negate_conjecture , [ status ( cth ) ] , [ 'it\\'s a\\\\b' ] ) ) ." := by cbv

theorem negated_integer_goal :
    negatedRow "n" (.integer "7") (.neg p) =
      .ok "fof ( n , negated_conjecture , ( ~ ~ p ) , inference ( negate_conjecture , [ status ( cth ) ] , [ 7 ] ) ) ." := by cbv

theorem negated_label_rejected : (negatedRow "é" (.atom "goal") p).isOk = false := by cbv

theorem conjecture_entry_row :
    entryRow "input.p" ⟨declaration (.atom "g") (.fof (.pair .implies p q)), .conjecture, 0, 0⟩ =
      .ok "fof ( g , conjecture , ( p => q ) , file ( 'input.p' , g ) ) ." := by cbv

theorem negated_input_row :
    entryRow "input.p" ⟨declaration (.atom "n") (.cnf [.neg p]), .negatedConjecture, 0, 0⟩ =
      .ok "cnf ( n , negated_conjecture , ( ~ p ) , file ( 'input.p' , n ) ) ." := by cbv

theorem integer_and_atom_names_differ : (goalNames [.integer "12"] "12" "g" []).Nodup := by decide

theorem premise_policy :
    (premiseEntries [entry "a" .axiomRole, entry "c" .conjecture, entry "n" .negatedConjecture,
      entry "h" .hypothesis, entry "u" .unknown, entry "l" .lemma]).map (fun value => value.original.name) =
      [.atom "a", .atom "h", .atom "l"] := by cbv

theorem repeated_name_rejected : ¬ (goalNames [.atom "a", .integer "1"] "n" "g" ["c", "a"]).Nodup := by decide

#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.role_words
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.negated_row_text
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.negated_quoted_goal
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.negated_integer_goal
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.negated_label_rejected
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.conjecture_entry_row
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.negated_input_row
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.integer_and_atom_names_differ
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.premise_policy
#print axioms Fang.TptpCandidate.FullFof.GoalRows.Controls.repeated_name_rejected

end Fang.TptpCandidate.FullFof.GoalRows.Controls
