/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The byte premises of `acceptsBundle_single` for the accepted decoder's own
   output, stated over the framer and the accepted decoder alone, and controls
   where the reduction does not apply. This module imports only `BundleFramer`,
   so the four modules that evaluate the premises load no certificate closure;
   the reductions to the accepted `accepts` are in `BundleSingleReductions`.
   Same definitions as `BundleSingleControls`, in the namespace `Single`. -/
import BundleFramer

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single

open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

def top : Key := ⟨.base, ["top.p"]⟩

/-- The declarations the accepted decoder reads, or none when it rejects. -/
def decodedValues (bytes : List UInt8) : List Declaration :=
  match CnfBoolean.decodeBytes bytes 4096 with
  | .ok values => values
  | .error _ => []

def decoderRejects (bytes : List UInt8) : Bool :=
  match CnfBoolean.decodeBytes bytes 4096 with
  | .ok _ => false
  | .error _ => true

/-- The byte premises of `acceptsBundle_single` for the decoder's own output.
    The framer must return the same declarations, spans included. -/
def SinglePremises (bytes : List UInt8) : Prop :=
  CnfBoolean.decodeBytes bytes 4096 = .ok (decodedValues bytes) ∧
  frameFile bytes 4096 = .ok ((decodedValues bytes).map .formula) ∧
  (readInput (decodedValues bytes)).isSome = true ∧
  objectNames (decodedValues bytes) = []

theorem top_wellFormed : keyWellFormed top = true := by cbv

/-- Outside the reduction: the accepted decoder rejects an annotation, an
    include directive and a distinct object, which the framer reads. -/
theorem outside_reduction :
    decoderRejects (bytesOf "fof(a,axiom,p,file(f,a)).") = true ∧
    decoderRejects (bytesOf "include('a.ax'). fof(a,axiom,p).") = true ∧
    decoderRejects (bytesOf "fof(a,axiom,p(\"o\")).") = true := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.top_wellFormed
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.outside_reduction

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single
