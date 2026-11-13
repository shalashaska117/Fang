/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Bounded retained terms for the depth-parametric role bundle framer. -/
import RoleFramerDepth

namespace Fang.TptpCandidate.Roles.Bundle.V3.Depth
open FullFof Numeric

theorem distinct_below {bundle : RoleBundle} (sound : SoundBundle bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses (V2.distinctItems input bundle items)) := by
  have covered := objects_covered sound items (read_tables read)
  have bound : ∀ id ∈ V2.objectIds input bundle items, id < input.functions.length := by
    intro id member
    simp only [V2.objectIds, List.mem_map] at member
    obtain ⟨label, labelMember, rfl⟩ := member
    exact Arity.id_bound (covered label labelMember)
  intro clause member literal literalMember term termMember
  have present := mem_retainedClauses member
  simp only [V2.distinctItems, Coverage.distinctAxioms, List.map_map, List.mem_map, Function.comp_def] at present
  obtain ⟨⟨left, right⟩, pairMember, shape⟩ := present
  simp only [Coverage.disequality, positive, SignedNumeric.cnf.injEq] at shape
  subst shape
  obtain ⟨leftMember, rightMember, _⟩ := Coverage.pairs_mem pairMember
  simp only [List.mem_singleton] at literalMember
  subst literalMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at termMember
  rcases termMember with rfl | rfl
  · simp only [Fang.QuantifiedFOF.Skolem.TermBelow]
    exact ⟨bound left leftMember, by simp⟩
  · simp only [Fang.QuantifiedFOF.Skolem.TermBelow]
    exact ⟨bound right rightMember, by simp⟩

theorem task_below {bundle : RoleBundle} (sound : SoundBundle bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) {task : List SignedNumeric}
    (fromRows : FromRows input task) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length
      (retainedClauses (task ++ V2.distinctItems input bundle items)) := by
  rw [retainedClauses_append]
  intro clause member
  rcases List.mem_append.mp member with original | generated
  · exact retained_below read fromRows clause original
  · exact distinct_below sound read clause generated

end Fang.TptpCandidate.Roles.Bundle.V3.Depth
