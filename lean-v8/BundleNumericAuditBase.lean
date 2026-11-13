/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Audit helpers: the outcome kind of the bundle framer (`frameFile`,
   the bundle path) and of the accepted version-8 decoder
   (`CnfBoolean.decodeBytes`, the single-file path) on a sample text. The
   audit rows are in `BundleNumericAudit*`. Imports only
   the framer. -/
import BundleFramer

namespace Fang.TptpCandidate.FullFof.Coverage.NumericAudit

open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

/-- `none` when the framer reads the file, otherwise the kind of its error. -/
def framerKind (text : String) : Option Fang.TptpCandidate.ErrorKind :=
  match frameFile (bytesOf text) 4096 with
  | .error failure => some failure.kind
  | .ok _ => none

/-- `none` when the accepted decoder reads the file, otherwise the kind of its error. -/
def decoderKind (text : String) : Option Fang.TptpCandidate.ErrorKind :=
  match CnfBoolean.decodeBytes (bytesOf text) 4096 with
  | .error failure => some failure.kind
  | .ok _ => none

end Fang.TptpCandidate.FullFof.Coverage.NumericAudit
