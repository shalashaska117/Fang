/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.CertificateInput

namespace Fang.FOFVersioned
open Frontend

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Version 2 fixes the interpretation of input leaves. The existing version-1
   decoder remains restricted to its original CNF input language. -/
def certificate (fuel : Nat) : Parser Certificate := do
  expect "("
  expect "fang-proof"
  let version ← natural
  if version != 2 then fail "unsupported: FOF certificate version"
  expect "("
  expect "preprocessing"
  expect "ground-fof-distributive-v1"
  expect ")"
  let (steps, finalId) ← CertificateInput.nodes fuel 0
  expect ")"
  if (← peek).isSome then fail "invalid-certificate: trailing tokens"
  pure { steps, final := finalId }

def decodeCertificate (input : String) : Except String Certificate := do
  let tokens ← Frontend.tokenize input
  let (result, _) ← certificate (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize
  }
  pure result

def decodes (input : String) : Bool :=
  match decodeCertificate input with
  | .ok _ => true
  | .error _ => false

theorem version_two_control :
    decodeCertificate "(fang-proof 2 (preprocessing ground-fof-distributive-v1) (input 0 0) (final 0))" =
      .ok { steps := [.input 0], final := 0 } := by cbv

theorem version_one_rejected :
    decodes "(fang-proof 1 (input 0 0) (final 0))" = false := by cbv

theorem unknown_version_rejected :
    decodes "(fang-proof 3 (preprocessing ground-fof-distributive-v1) (input 0 0) (final 0))" = false := by cbv

theorem missing_tag_rejected :
    decodes "(fang-proof 2 (input 0 0) (final 0))" = false := by cbv

theorem unknown_tag_rejected :
    decodes "(fang-proof 2 (preprocessing other) (input 0 0) (final 0))" = false := by cbv

theorem duplicate_tag_rejected :
    decodes "(fang-proof 2 (preprocessing ground-fof-distributive-v1) (preprocessing ground-fof-distributive-v1) (input 0 0) (final 0))" = false := by cbv

theorem trailing_tokens_rejected :
    decodes "(fang-proof 2 (preprocessing ground-fof-distributive-v1) (input 0 0) (final 0)) extra" = false := by cbv

theorem v1_decoder_rejects_v2 :
    (match Fang.decodeCertificate "(fang-proof 2 (preprocessing ground-fof-distributive-v1) (input 0 0) (final 0))" with
      | .ok _ => true | .error _ => false) = false := by cbv

end Fang.FOFVersioned
