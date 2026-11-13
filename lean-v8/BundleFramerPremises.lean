/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The closure and object-coverage premises of the byte-bundle endpoint follow
   from framing; only `readInput` success and ID distinctness remain. -/
import BundleFramerSound

namespace Fang.TptpCandidate.FullFof.Coverage.FramerV2

open Fang.TptpCandidate.FullFof.Coverage

theorem framed_closed {files : List (Key × List UInt8)} {maximum : Nat} {bundle : Bundle}
    (framed : frameBundle files maximum = .ok bundle) (items : List Item) :
    Grammar.Closed (declarationsOf bundle items) := by
  intro value member
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := framed_declarations_sound framed items member
  exact CnfBoolean.declaration_closed decoded

theorem framed_objects_covered {files : List (Key × List UInt8)} {maximum : Nat} {bundle : Bundle}
    (framed : frameBundle files maximum = .ok bundle) (items : List Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (declarationsOf bundle items) = some input) :
    ∀ label ∈ objectNames (declarationsOf bundle items), (label, 0) ∈ input.functions := by
  intro label member
  rw [(Integration.readInput_tables encoded).1]
  simp only [objectNames, List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap] at member
  obtain ⟨symbol, ⟨formula, formulaMember, present⟩, chosen⟩ := member
  by_cases object : isObject symbol.1 = true
  · simp only [object, ↓reduceIte, Option.some.injEq] at chosen
    subst chosen
    simp only [source, List.mem_map, Function.comp] at formulaMember
    obtain ⟨value, valueMember, rfl⟩ := formulaMember
    obtain ⟨_, _, _, _, used⟩ := framed_declarations_sound framed items valueMember
    have arity : symbol.2 = 0 := by
      simp only [objectsWellUsed, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at used
      have := used.2 symbol present
      simp only [object, bne_iff_ne, ne_eq] at this
      exact Classical.byContradiction fun different => this ⟨trivial, different⟩
    have inSource : value.body.formula ∈ source (declarationsOf bundle items) :=
      List.mem_map.mpr ⟨value, valueMember, rfl⟩
    have covered := (collected_covered inSource).functions symbol present
    have shape : symbol = (symbol.1, 0) := Prod.ext rfl arity
    rw [← shape]
    exact covered
  · simp [object] at chosen

/-- The endpoint with the derivable premises discharged. -/
theorem byte_bundle_unsat_of_check {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} {input : Integration.NumericInput}
    (framed : frameBundle files maximum = .ok bundle) (expanded : expand bundle fuel = .ok items)
    (encoded : Integration.readInput (declarationsOf bundle items) = some input)
    (nodup : ((objectNames (declarationsOf bundle items)).map
      fun label => Arity.id input.functions (label, 0)).Nodup)
    (refuted : ¬ ReservedSatisfiable input.predicates.length
      (input.declarations ++ distinctAxioms input.predicates.length
        ((objectNames (declarationsOf bundle items)).map fun label => Arity.id input.functions (label, 0)))) :
    ¬ ByteBundleSatisfiable files maximum fuel :=
  byte_bundle_generated_unsat framed expanded encoded (framed_closed framed items)
    (framed_objects_covered framed items encoded) nodup refuted

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.framed_closed
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.framed_objects_covered
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.byte_bundle_unsat_of_check

end Fang.TptpCandidate.FullFof.Coverage.FramerV2
