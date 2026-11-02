/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Object IDs are distinct by construction, so the byte-bundle endpoint needs
   only framing, expansion, `readInput` success and the refutation. -/
import BundleFramerPremises

namespace Fang.TptpCandidate.FullFof.Coverage.FramerV2

open Fang.TptpCandidate.FullFof.Coverage

theorem eraseDups_loop_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (rest accumulated : List α), accumulated.Nodup →
      (List.eraseDupsBy.loop (· == ·) rest accumulated).Nodup := by
  intro rest
  induction rest with
  | nil =>
    intro accumulated nodup
    simp only [List.eraseDupsBy.loop]
    exact List.pairwise_reverse.mpr (nodup.imp fun different same => different same.symm)
  | cons first more ih =>
    intro accumulated nodup
    unfold List.eraseDupsBy.loop
    split
    · exact ih accumulated nodup
    · rename_i absent
      apply ih
      refine List.nodup_cons.mpr ⟨fun member => ?_, nodup⟩
      have found : accumulated.any (fun other => first == other) = true :=
        List.any_eq_true.mpr ⟨first, member, beq_self_eq_true first⟩
      rw [found] at absent
      cases absent

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (values : List α) : values.eraseDups.Nodup := by
  unfold List.eraseDups List.eraseDupsBy
  exact eraseDups_loop_nodup values [] List.nodup_nil

theorem objectNames_nodup (values : List Declaration) : (objectNames values).Nodup :=
  eraseDups_nodup _

/-- Different object names get different IDs in the complete function table. -/
theorem framed_object_ids_nodup {files : List (Key × List UInt8)} {maximum : Nat} {bundle : Bundle}
    (framed : frameBundle files maximum = .ok bundle) (items : List Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (declarationsOf bundle items) = some input) :
    ((objectNames (declarationsOf bundle items)).map
      fun label => Arity.id input.functions (label, 0)).Nodup := by
  have covered := framed_objects_covered framed items encoded
  apply List.pairwise_map.mpr
  refine (objectNames_nodup (declarationsOf bundle items)).imp_of_mem ?_
  intro first second firstMember secondMember different same
  exact different (Prod.mk.inj (Arity.id_injective (covered first firstMember)
    (covered second secondMember) same)).1

/-- The byte-bundle endpoint: a successful framing, expansion and `readInput`,
    and a refutation of the numeric problem with the generated pairwise
    disequalities, refute the sealed bundle. -/
theorem byte_bundle_unsat_of_refutation {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} {input : Integration.NumericInput}
    (framed : frameBundle files maximum = .ok bundle) (expanded : expand bundle fuel = .ok items)
    (encoded : Integration.readInput (declarationsOf bundle items) = some input)
    (refuted : ¬ ReservedSatisfiable input.predicates.length
      (input.declarations ++ distinctAxioms input.predicates.length
        ((objectNames (declarationsOf bundle items)).map fun label => Arity.id input.functions (label, 0)))) :
    ¬ ByteBundleSatisfiable files maximum fuel :=
  byte_bundle_unsat_of_check framed expanded encoded (framed_object_ids_nodup framed items encoded) refuted

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.eraseDups_loop_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.eraseDups_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.objectNames_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.framed_object_ids_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.byte_bundle_unsat_of_refutation

end Fang.TptpCandidate.FullFof.Coverage.FramerV2
