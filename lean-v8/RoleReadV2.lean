/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The bundle read over the revision-2 role framer, before any replay. It also refuses a conjecture together with a negated conjecture, as the single-file role decoder does. -/
import RoleMeaningV2
import BundleRead

namespace Fang.TptpCandidate.Roles.Bundle.V2
open FullFof Numeric

inductive ReadError where
  | frame : Error → ReadError
  | expand : Coverage.Failure → ReadError
  | shape
  /-- A selected conjecture and a selected negated conjecture together (`Bytes.modesValid`). -/
  | modes
  | nonliteral

/-- Expansion errors precede the shape check, as in the bundle version-8 entry. -/
def readBundle (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) :
    Except ReadError BundleRead :=
  match frameBundle tokenize files maximumBytes with
  | .error problem => .error (.frame problem)
  | .ok bundle =>
    match Coverage.expand (forget bundle) bundleFuel with
    | .error problem => .error (.expand problem)
    | .ok items =>
      if Coverage.FramerV2.wellShaped (forget bundle) bundleFuel then
        if Bytes.modesValid (entriesOf bundle items) then
          match readSigned (entriesOf bundle items) with
          | none => .error .nonliteral
          | some input => .ok ⟨bundle, items, input⟩
        else .error .modes
      else .error .shape

theorem readBundle_witness {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat}
    {read : BundleRead} (success : readBundle tokenize files maximumBytes = .ok read) :
    Expanded tokenize files maximumBytes bundleFuel read.bundle read.items ∧
      Bytes.modesValid (entriesOf read.bundle read.items) = true ∧
      readSigned (entriesOf read.bundle read.items) = some read.input := by
  unfold readBundle at success
  split at success
  · cases success
  · rename_i bundle framed
    split at success
    · cases success
    · rename_i items expanded
      split at success
      · rename_i shaped
        split at success
        · rename_i modes
          split at success
          · cases success
          · rename_i input signed
            cases success
            exact ⟨⟨framed, shaped, expanded⟩, modes, signed⟩
        · cases success
      · cases success

#print axioms Fang.TptpCandidate.Roles.Bundle.V2.readBundle_witness

end Fang.TptpCandidate.Roles.Bundle.V2
