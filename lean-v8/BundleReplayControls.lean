/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed controls for bundle acceptance: a bundle that frames and expands but
   is not well shaped is rejected before the certificate is read, whatever the
   certificate, limits and caps are. -/
import BundleReplay
import BundleNumericControls

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls

open Aeneas.Std
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2
open Fang.TptpCandidate.FullFof.Coverage.BundleV8
open Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls (bytesOf top axioms run)

def sealed (files : List (Key × String)) : List (Key × List UInt8) :=
  files.map fun pair => (pair.1, bytesOf pair.2)

theorem rejected_before_certificate {files : List (Key × String)} {error : BundleError}
    (failed : run files = .error error) (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (sealed files) 4096 proof limits maximumPredicates maximumLiterals =
      .error (.replay (.bundle error)) := by
  unfold run at failed
  simp only [acceptsBundle, prepareBundle, sealed, failed, Except.mapError, Bind.bind, Except.bind]

def second : Key := ⟨.base, ["b.ax"]⟩

theorem unreached_file_rejected (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (sealed [(top, "fof(x,axiom,p)."), (axioms, "fof(y,axiom,~p).")]) 4096
      proof limits maximumPredicates maximumLiterals = .error (.replay (.bundle .shape)) :=
  rejected_before_certificate (by cbv) proof limits maximumPredicates maximumLiterals

theorem misordered_files_rejected (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (sealed [(top, "include('a.ax'). include('b.ax')."), (second, "fof(y,axiom,~p)."),
      (axioms, "fof(x,axiom,p).")]) 4096 proof limits maximumPredicates maximumLiterals =
      .error (.replay (.bundle .shape)) :=
  rejected_before_certificate (by cbv) proof limits maximumPredicates maximumLiterals

theorem duplicate_keys_rejected (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (sealed [(top, "include('a.ax')."), (axioms, "fof(x,axiom,p)."),
      (axioms, "fof(y,axiom,~p).")]) 4096 proof limits maximumPredicates maximumLiterals =
      .error (.replay (.bundle .shape)) :=
  rejected_before_certificate (by cbv) proof limits maximumPredicates maximumLiterals

/-- Keys need nonempty components without `/`. -/
theorem malformed_key_rejected (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (sealed [(⟨.base, ["", "top.p"]⟩, "fof(x,axiom,p). fof(y,axiom,~p).")]) 4096
      proof limits maximumPredicates maximumLiterals = .error (.replay (.bundle .shape)) :=
  rejected_before_certificate (by cbv) proof limits maximumPredicates maximumLiterals

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls.rejected_before_certificate
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls.unreached_file_rejected
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls.misordered_files_rejected
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls.duplicate_keys_rejected
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls.malformed_key_rejected

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.ReplayControls
