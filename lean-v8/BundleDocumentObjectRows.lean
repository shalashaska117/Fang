/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A source-row control in its own module: distinct objects print between
   double quotes and the rows frame back. -/
import BundleDocumentControls

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls

open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Coverage (Key Item Bundle expand)
open Fang.QuantifiedEqualityTstp.Expanded.Bundle

set_option maxRecDepth 20000 in
/-- Distinct objects print between double quotes, `\` escaped, and the row
    frames back to the same declaration; the annotation becomes the file source. -/
theorem objects_print_quoted :
    texts (rowsOf [(top, "fof(a,axiom,p(\"u\") & ~p(\"v\\\\w\"),file(f,a)). cnf(b,axiom,\"u\" != c | q).")]) =
      ["fof ( a , axiom , ( p ( \"u\" ) & ~ p ( \"v\\\\w\" ) ) , file ( 'top.p' , a ) ) .",
       "cnf ( b , axiom , ( ~ \"u\" = c | q ) , file ( 'top.p' , b ) ) ."] := by
  cbv

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls.objects_print_quoted

end Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls
