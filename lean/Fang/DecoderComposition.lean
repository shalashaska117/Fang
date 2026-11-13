/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Composition of checked decoder computations. These lemmas do not assert a
declarative grammar or the meaning of source names.
-/
import Fang.CertificateInput

namespace Fang

theorem tokenize_of_characters (input : String) (characters : List Char)
    (tokens : List Frontend.Token)
    (text : input.toList = characters)
    (ascii : characters.findIdx? (fun c => c.toNat > 127) = none)
    (lexed : Frontend.lexAux (characters.length + 1) characters 0 = .ok tokens) :
    Frontend.tokenize input = .ok tokens := by
  simp only [Frontend.tokenize, text, ascii]
  exact lexed

theorem decodeCertificate_of_tokens (input : String) (tokens : List Frontend.Token)
    (certificate : Certificate) (finalState : Frontend.State)
    (lexed : Frontend.tokenize input = .ok tokens)
    (parsed : CertificateInput.certificate (tokens.length + 1)
      { tokens, endOffset := input.utf8ByteSize } = .ok (certificate, finalState)) :
    decodeCertificate input = .ok certificate := by
  simp only [decodeCertificate, lexed]
  change (do
    let result ← CertificateInput.certificate (tokens.length + 1)
      { tokens, endOffset := input.utf8ByteSize }
    pure result.1) = .ok certificate
  rw [parsed]
  rfl

end Fang
