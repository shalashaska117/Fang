/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.VersionedCheck
import Fang.SourceAscii

namespace Fang.FOFKernelReplay

def resultKind : Except String Bool → String
  | .ok true => "accepted"
  | .ok false => "rejected"
  | .error _ => "error"

def certificateKind : Except String Certificate → String
  | .ok _ => "decoded"
  | .error _ => "error"

theorem size_ofList (characters : List Char) :
    (String.ofList characters).utf8ByteSize = (characters.map Char.utf8Size).sum := by
  induction characters with
  | nil => rfl
  | cons c cs ih =>
    change (String.ofList ([c] ++ cs)).utf8ByteSize = _
    rw [String.ofList_append, String.utf8ByteSize_append,
      ← String.singleton_eq_ofList, String.utf8ByteSize_singleton, ih]
    rfl

end Fang.FOFKernelReplay
