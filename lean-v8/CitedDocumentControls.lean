/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Self-contained controls for cited source selection and complete documents. -/
import CitedDocumentNativeCore

namespace FangCitedDocumentControls
open Fang.TptpCandidate FullFof

private def file (path text : String) : Coverage.Key × List UInt8 :=
  (⟨.base, [path]⟩, text.toUTF8.data.toList)

private def trace : String :=
  "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1) (input 0 0) (input 1 1) (resolve 2 1 0 0 0 (subst) (clause)) (final 2))"

private def proof : String := "(premises (item 1 0))\n" ++ trace
private def inputProof : String := "(premises (item 1 0) (item 0 1))\n" ++ trace

private def accepted (result : Except String String) : Bool :=
  match result with | .ok _ => true | .error _ => false

private def require (label : String) (value : Bool) : IO Unit := do
  if !value then throw (IO.userError s!"FAIL {label}")
  IO.println s!"PASS {label}"

#eval do
  let goalFiles := [file "top.p" "include('axioms.ax').\nfof(goal,conjecture,p).",
    file "axioms.ax" "fof(premise,hypothesis,p)."]
  let .ok text := FangCitedDocumentNative.render (.goal 0) goalFiles proof
    | throw (IO.userError "cited goal document missing")
  require "cited goal has all seven rows" ((text.splitOn "\n").length == 8)
  require "original hypothesis role retained" ((text.splitOn "hypothesis").length == 2)
  require "group cites premise and goal negation" ((text.splitOn "['premise','fn0']").length == 2)
  let second := [file "top.p" "include('axioms.ax').\nfof(unused,conjecture,q).\nfof(goal,conjecture,p).",
    file "axioms.ax" "fof(premise,hypothesis,p)."]
  require "second original goal accepted" (accepted (FangCitedDocumentNative.render (.goal 1) second proof))
  require "wrong original goal rejected" (!(accepted (FangCitedDocumentNative.render (.goal 0) second proof)))
  let nested := [file "top.p" "include('middle.ax',[selected]).\nfof(goal,conjecture,p).",
    file "middle.ax" "include('leaf.ax').\nfof(selected,axiom,q).", file "leaf.ax" "fof(excluded,axiom,p)."]
  require "nested selection excludes cited formula" (!(accepted (FangCitedDocumentNative.render (.goal 0) nested
    ("(premises (item 2 0))\n" ++ trace))))
  let inputs := [file "top.p" "include('axioms.ax').\nfof(negative,negated_conjecture,~p).",
    file "axioms.ax" "fof(positive,hypothesis,p)."]
  let .ok inputText := FangCitedDocumentNative.render .inputs inputs inputProof
    | throw (IO.userError "cited inputs document missing")
  require "inputs group cites both positive input roles" ((inputText.splitOn "['positive','negative']").length == 2)
  require "inputs reject selected conjecture" (!(accepted (FangCitedDocumentNative.render .inputs goalFiles proof)))
  require "future proof parent rejected" (!(accepted (FangCitedDocumentNative.render .inputs inputs
    (inputProof.replace "(resolve 2 1 0" "(resolve 2 2 0"))))
  require "duplicate cited item rejected" (!(accepted (FangCitedDocumentNative.render (.goal 0) goalFiles
    ("(premises (item 1 0) (item 1 0))\n" ++ trace))))
  require "missing cited envelope rejected" (!(accepted (FangCitedDocumentNative.render (.goal 0) goalFiles trace)))
  let objects := [file "top.p" "include('axioms.ax').\nfof(goal,conjecture,p(\"a\",\"b\")).",
    file "axioms.ax" "fof(premise,hypothesis,p(\"a\",\"b\"))."]
  let .ok objectText := FangCitedDocumentNative.render (.goal 0) objects proof
    | throw (IO.userError "object document missing")
  require "distinct objects printed without internal NUL" (!objectText.toUTF8.data.contains 0)

end FangCitedDocumentControls
