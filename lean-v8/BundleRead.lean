/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The bundle read before any replay: framing with roles, expansion, the shape check and the complete signed tables. -/
import BundleRoles

namespace Fang.TptpCandidate.Roles.Bundle
open FullFof Numeric

/-- The expansion fuel of the bundle version-8 entry. -/
def bundleFuel : Nat := 17

inductive BundleReadError where
  | frame : Error → BundleReadError
  | shape
  | expand : Coverage.Failure → BundleReadError
  | nonliteral

structure BundleRead where
  bundle : RoleBundle
  items : List Coverage.Item
  input : SignedInput

/-- Expansion errors precede the shape check, as in the bundle version-8 entry. -/
def readBundle (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) : Except BundleReadError BundleRead :=
  match frameBundle files maximumBytes with
  | .error problem => .error (.frame problem)
  | .ok bundle =>
    match Coverage.expand (forget bundle) bundleFuel with
    | .error problem => .error (.expand problem)
    | .ok items =>
      if Coverage.Framer.wellShaped (forget bundle) bundleFuel then
        match readSigned (entriesOf bundle items) with
        | none => .error .nonliteral
        | some input => .ok ⟨bundle, items, input⟩
      else .error .shape

theorem readBundle_witness {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {read : BundleRead}
    (success : readBundle files maximumBytes = .ok read) :
    Expanded files maximumBytes bundleFuel read.bundle read.items ∧
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
        · cases success
        · rename_i input signed
          cases success
          exact ⟨⟨framed, shaped, expanded⟩, signed⟩
      · cases success

#print axioms Fang.TptpCandidate.Roles.Bundle.readBundle_witness

end Fang.TptpCandidate.Roles.Bundle
