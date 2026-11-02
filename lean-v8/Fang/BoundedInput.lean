/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Bounded native file loading. Handle I/O and physical allocation remain runtime
assumptions, separate from the pure certificate-checker soundness theorem.
-/

namespace Fang.Runtime

/-- Read through EOF or the byte allowance, including across short reads. -/
def readAtMost (handle : IO.FS.Handle) (remaining : Nat) (accumulated : ByteArray := .empty) :
    IO ByteArray := do
  if _exhausted : remaining = 0 then
    return accumulated
  let requested := min remaining 65536
  let chunk ← handle.read requested.toUSize
  if _empty : chunk.size = 0 then
    return accumulated
  if _excessive : requested < chunk.size then
    throw (IO.userError "file reader returned more bytes than requested")
  readAtMost handle (remaining - chunk.size) (accumulated ++ chunk)
termination_by remaining
decreasing_by omega

def readAscii (path : String) (limit : Nat) : IO (Except String String) := do
  let bytes ← IO.FS.withFile path .read fun handle => readAtMost handle (limit + 1)
  if bytes.size > limit then
    return .error s!"resource-exhaustion: {path} exceeds {limit} bytes"
  if let some offset := bytes.data.findIdx? (fun byte => byte.toNat > 127) then
    return .error s!"unsupported at byte {offset}: {path} must contain ASCII bytes only"
  match String.fromUTF8? bytes with
  | none => return .error s!"invalid-syntax: {path} is not UTF-8"
  | some text => return .ok text

end Fang.Runtime
