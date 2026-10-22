/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import TstpExport
import Fang.FrontendSoundness

namespace Fang.TstpExport

open Source.Grammar

/-- Keeping names does not change the established decoder's signature or AST. -/
theorem decodeNamed_signature (input : String) :
    (decodeNamed input).map NamedProblem.signature = decodeProblemWithSignature input := by
  cases ht : Frontend.tokenize input with
  | error e => simp [decodeNamed, decodeProblemWithSignature, ht, bind, Except.bind, Except.map]
  | ok tokens =>
    cases hs : Frontend.statements (tokens.length + 1)
        { tokens, endOffset := input.utf8ByteSize } <;>
      simp [decodeNamed, decodeProblemWithSignature, ht, hs, bind, Except.bind,
        pure, Except.pure, Except.map]

theorem decodeNamed_problem {input : String} {problem : NamedProblem}
    (h : decodeNamed input = .ok problem) :
    decodeProblem input = .ok problem.signature.problem := by
  have hs := decodeNamed_signature input
  rw [h] at hs
  simp only [Except.map] at hs
  simp [decodeProblem, ← hs, bind, Except.bind, pure, Except.pure]

/-- A successful export build has passed the existing logical certificate check.
    This theorem makes no claim about the rows or their printed syntax. -/
theorem build_checked {problem : NamedProblem} {certificate : Certificate} {output : Export}
    (h : build problem certificate = .ok output) :
    check (preprocess problem.signature.problem) certificate = true := by
  by_cases length : certificate.steps.length > 1000
  · simp [build, length, bind, Except.bind, pure, Except.pure, throw] at h
  by_cases wellFormed : certificateWellFormed problem.signature certificate = true
  · by_cases checked : check (preprocess problem.signature.problem) certificate = true
    · exact checked
    · simp [build, length, wellFormed, checked, bind, Except.bind, pure, Except.pure, throw] at h
  · simp [build, length, wellFormed, bind, Except.bind, pure, Except.pure, throw] at h

theorem build_problem_unsat {problem : NamedProblem} {certificate : Certificate} {output : Export}
    (h : build problem certificate = .ok output) : ¬ Satisfiable problem.signature.problem :=
  check_preprocessed_sound problem.signature.problem certificate (build_checked h)

private theorem empty_clause_guard (c : Option Clause) :
    (c != some []) = false ↔ c = some [] := by
  cases c with
  | none => decide
  | some c =>
    cases c with
    | nil => decide
    | cons a rest =>
      constructor
      · intro h
        change true = false at h
        cases h
      · intro h
        cases h

/-- The export result retains its source and ends at its named empty clause.
    This endpoint invariant is separate from the correctness of earlier rows. -/
theorem build_endpoint {problem : NamedProblem} {certificate : Certificate} {output : Export}
    (h : build problem certificate = .ok output) :
    output.signature = problem ∧
      output.rows.getLast?.map Row.name = some output.finalName ∧
      output.rows.getLast?.map Row.clause = some [] := by
  have checked := build_checked h
  by_cases length : certificate.steps.length > 1000
  · simp [build, length, bind, Except.bind, pure, Except.pure, throw] at h
  by_cases wellFormed : certificateWellFormed problem.signature certificate = true
  · simp only [build, length, wellFormed, checked, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
    repeat first | split at h | simp_all [throw, throwThe, empty_clause_guard]
    all_goals cases h
    all_goals simp_all
  · simp [build, length, wellFormed, bind, Except.bind, pure, Except.pure, throw] at h

/-- Export success cannot turn a rejected source/certificate pair into an UNSAT
    claim. The meaning of the printed TSTP still requires separate correspondence. -/
theorem export_original_unsat {input proof fileLabel text : String}
    (h : exportText input proof fileLabel = .ok text) :
    ¬ Source.Grammar.BytesSatisfiable (spelling input) := by
  cases hn : decodeNamed input with
  | error e => simp [exportText, hn, bind, Except.bind] at h
  | ok problem =>
    cases hc : decodeCertificate proof with
    | error e => simp [exportText, hn, hc, bind, Except.bind] at h
    | ok certificate =>
      cases hb : build problem certificate with
      | error e => simp [exportText, hn, hc, hb, bind, Except.bind] at h
      | ok output =>
        exact decoded_refutation_unsat (decodeNamed_problem hn) certificate (build_checked hb)

end Fang.TstpExport
