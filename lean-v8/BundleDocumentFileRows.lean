/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A source-row control in its own module: rows follow expansion order and
   name the file that holds each declaration. -/
import BundleDocumentControls

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls

open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Coverage (Key Item Bundle expand)
open Fang.QuantifiedEqualityTstp.Expanded.Bundle

set_option maxRecDepth 20000 in
/-- The included file's row comes first, as in the expansion, and each row
    names its own file. -/
theorem rows_name_their_files :
    texts (rowsOf [(top, "include('ax.ax'). fof(t,axiom,q)."),
      (⟨.base, ["ax.ax"]⟩, "fof(x,axiom,![X]:(s(X) => X = \"o\")).")]) =
      ["fof ( x , axiom , ( ! [ X ] : ( s ( X ) => X = \"o\" ) ) , file ( 'ax.ax' , x ) ) .",
       "fof ( t , axiom , ( q ) , file ( 'top.p' , t ) ) ."] := by
  cbv

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls.rows_name_their_files

end Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls
