/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Generated declarative byte witness. The Lean kernel checks every constructor.
This certifies one byte value; generic executable decoder correctness is open.
-/
import Fang.SourceLexing
import Fang.SourceGrammarExamples
import Fang.CertificateInput
import Lean.Elab.Tactic.Cbv

namespace Fang.Source.Grammar.OriginalExample

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def originalInput : String := "cnf(c0,axiom,(p(X)|p(Y)|p(X))).\ncnf(c1,axiom,(~p(a))).\n"

def originalBytes : Bytes := spelling originalInput

def engineCertificate : String := "(fang-proof 1\n  (input 0 0)\n  (input 1 1)\n  (factor 2 0 0 1 (subst (1 (v 0))) (clause (pos 0 (v 0))))\n  (resolve 3 2 0 1 0 (subst (0 (f 0))) (clause))\n  (final 3))\n"

theorem engine_certificate_decodes : Fang.decodeCertificate engineCertificate = .ok Fang.Examples.certificate := by cbv

theorem tokenizes : Tokenization originalBytes Examples.documentedTokens := by
  exact (.token (.word (front := [99, 110, 102]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "cnf" rfl ⟨99, [110, 102], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .lparen)
    (.token (.word (front := [99, 48]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "c0" rfl ⟨99, [48], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .comma)
    (.token (.word (front := [97, 120, 105, 111, 109]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "axiom" rfl ⟨97, [120, 105, 111, 109], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .comma)
    (.token (.punctuation .lparen)
    (.token (.word (front := [112]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "p" rfl ⟨112, [], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .lparen)
    (.token (.word (front := [88]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.variableWord "X" rfl ⟨88, [], rfl, by simp [IsUpper], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .rparen)
    (.token (.punctuation .disjoin)
    (.token (.word (front := [112]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "p" rfl ⟨112, [], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .lparen)
    (.token (.word (front := [89]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.variableWord "Y" rfl ⟨89, [], rfl, by simp [IsUpper], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .rparen)
    (.token (.punctuation .disjoin)
    (.token (.word (front := [112]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "p" rfl ⟨112, [], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .lparen)
    (.token (.word (front := [88]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.variableWord "X" rfl ⟨88, [], rfl, by simp [IsUpper], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .rparen)
    (.token (.punctuation .rparen)
    (.token (.punctuation .rparen)
    (.token (.punctuation .period)
    (.whitespace (by simp [IsSpace])
    (.token (.word (front := [99, 110, 102]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "cnf" rfl ⟨99, [110, 102], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .lparen)
    (.token (.word (front := [99, 49]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "c1" rfl ⟨99, [49], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .comma)
    (.token (.word (front := [97, 120, 105, 111, 109]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "axiom" rfl ⟨97, [120, 105, 111, 109], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .comma)
    (.token (.punctuation .lparen)
    (.token (.punctuation .negate)
    (.token (.word (front := [112]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "p" rfl ⟨112, [], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .lparen)
    (.token (.word (front := [97]) rfl ⟨by simp [IsWord, IsLower, IsUpper, IsDigit], by intro byte tail same; have equal := (List.cons.inj same).1; subst byte; simp [IsWord, IsLower, IsUpper, IsDigit]⟩ (.lower "a" rfl ⟨97, [], rfl, by simp [IsLower], by simp [IsLower, IsUpper, IsDigit]⟩))
    (.token (.punctuation .rparen)
    (.token (.punctuation .rparen)
    (.token (.punctuation .rparen)
    (.token (.punctuation .period)
    (.whitespace (by simp [IsSpace])
    .empty)))))))))))))))))))))))))))))))))))))))))

theorem parses : Parses originalBytes Source.Examples.problem :=
  ⟨Examples.documentedTokens, tokenizes, Examples.documented_parse⟩

theorem original_input_unsat : ¬ BytesSatisfiable originalBytes :=
  original_bytes_unsat_of_witness parses Source.Examples.encoded
    Fang.Examples.certificate Fang.Examples.accepted

#print axioms tokenizes
#print axioms engine_certificate_decodes
#print axioms original_input_unsat

end Fang.Source.Grammar.OriginalExample
