/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFFuelBound

namespace Fang.FOFFrontend
open Frontend

/-- A grammar-completeness proof may choose any fuel, then use the actual public decoder. -/
theorem decode_of_success_at_any_fuel {input : String} {tokens : List Token} {fuel : Nat}
    {declarations : List GroundFOF.Declaration} {final : State}
    (scanned : tokenize input = .ok tokens)
    (parsed : statements fuel { tokens, endOffset := input.utf8ByteSize } = .ok (declarations, final)) :
    decode input = .ok { declarations, state := final } := by
  have sufficient := statements_token_count_fuel parsed
  simp only at sufficient
  simp [decode, scanned, sufficient, bind, Except.bind, pure, Except.pure]

end Fang.FOFFrontend
