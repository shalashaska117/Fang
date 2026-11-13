/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A source-row control in its own module: quoted and integer declaration
   names keep their spelling in the row and in its file source. -/
import BundleDocumentControls

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls

open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Coverage (Key Item Bundle expand)
open Fang.QuantifiedEqualityTstp.Expanded.Bundle

set_option maxRecDepth 20000 in
theorem names_keep_spelling :
    texts (rowsOf [(top, "fof('a b',axiom,?[Y]:r(Y,'c d')). fof(2,axiom,~r(e,'c d') | $true).")]) =
      ["fof ( 'a b' , axiom , ( ? [ Y ] : r ( Y , 'c d' ) ) , file ( 'top.p' , 'a b' ) ) .",
       "fof ( 2 , axiom , ( ~ r ( e , 'c d' ) | $true ) , file ( 'top.p' , 2 ) ) ."] := by
  cbv

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls.names_keep_spelling

end Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls
