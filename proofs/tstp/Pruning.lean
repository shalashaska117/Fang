/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Origins

namespace Fang.TstpExport.BuilderProof

/-- Backward graph reachability from the declared final certificate node. -/
inductive Reachable (certificate : Certificate) : Nat → Prop where
  | final : Reachable certificate certificate.final
  | parent {node source : Nat} {step : Step}
      (child : Reachable certificate node)
      (lookup : certificate.steps[node]? = some step)
      (edge : source ∈ parents step) : Reachable certificate source

theorem zipIdx_position (certificate : Certificate) (entry : Step × Nat)
    (member : entry ∈ certificate.steps.zipIdx) : certificate.steps[entry.2]? = some entry.1 := by
  obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
  have lookup := List.getElem?_zipIdx (l := certificate.steps) (i := 0) (j := index)
  rw [indexed] at lookup
  cases stepAt : certificate.steps[index]? with
  | none => simp [stepAt] at lookup
  | some step =>
    have pair : entry = (step, index) := by simpa [stepAt] using lookup
    simpa [pair] using stepAt

theorem ancestor_step_sound (certificate : Certificate) (needed : List Nat) (entry : Step × Nat)
    (reachable : ∀ node ∈ needed, Reachable certificate node)
    (position : certificate.steps[entry.2]? = some entry.1) :
    ∀ node ∈ (if needed.contains entry.2 then needed ++ parents entry.1 else needed),
      Reachable certificate node := by
  by_cases selected : entry.2 ∈ needed
  · simp only [List.contains_iff_mem.mpr selected, ↓reduceIte]
    intro node member
    rcases List.mem_append.mp member with old | edge
    · exact reachable node old
    · exact .parent (reachable entry.2 selected) position edge
  · simpa [selected] using reachable

theorem ancestor_fold_sound (certificate : Certificate) (entries : List (Step × Nat)) (needed : List Nat)
    (positions : ∀ entry ∈ entries, certificate.steps[entry.2]? = some entry.1)
    (reachable : ∀ node ∈ needed, Reachable certificate node) :
    ∀ node ∈ entries.foldl (fun needed entry =>
      if needed.contains entry.2 then needed ++ parents entry.1 else needed) needed,
      Reachable certificate node := by
  induction entries generalizing needed with
  | nil => exact reachable
  | cons entry entries ih =>
    apply ih _ (fun other member => positions other (List.mem_cons_of_mem _ member))
    exact ancestor_step_sound certificate needed entry reachable (positions entry (by simp))

theorem ancestors_sound (certificate : Certificate) (node : Nat)
    (member : node ∈ ancestors certificate) : Reachable certificate node := by
  apply ancestor_fold_sound certificate certificate.steps.zipIdx.reverse [certificate.final] _ _ node member
  · intro entry inReverse
    exact zipIdx_position certificate entry (List.mem_reverse.mp inReverse)
  · intro source inFinal
    have same := List.mem_singleton.mp inFinal
    subst source
    exact .final

def RowReachable (certificate : Certificate) (row : Row) : Prop :=
  match row.origin with
  | .input source _ => ∃ node, Reachable certificate node ∧
      certificate.steps[node]? = some (.input source)
  | .deduplicate node _ _ | .rename node _ _ | .factor node _ _ _ _ | .resolve node _ _ _ _ _ =>
      Reachable certificate node

theorem certificate_row_reachable (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (row : Row) (origin : CertificateRow problem certificate clauses row) :
    RowReachable certificate row := by
  cases tag : row.origin with
  | input source name =>
    simp only [CertificateRow, tag] at origin
    obtain ⟨node, needed, position, _⟩ := origin
    simp only [RowReachable, tag]
    exact ⟨node, ancestors_sound certificate node needed, position⟩
  | deduplicate node source name =>
    simp only [CertificateRow, tag] at origin
    simpa only [RowReachable, tag] using ancestors_sound certificate node origin.1
  | rename node right name =>
    simp only [CertificateRow, tag] at origin
    simpa only [RowReachable, tag] using ancestors_sound certificate node origin.1
  | factor node i j name σ =>
    simp only [CertificateRow, tag] at origin
    simpa only [RowReachable, tag] using ancestors_sound certificate node origin.1
  | resolve node i j left right σ =>
    simp only [CertificateRow, tag] at origin
    simpa only [RowReachable, tag] using ancestors_sound certificate node origin.1

/-- Successful actual output contains no row from a node unrelated to the
    final refutation. Raw input rows belong to reachable input nodes. -/
theorem build_relevant (problem : NamedProblem) (certificate : Certificate) (output : Export)
    (success : build problem certificate = .ok output) :
    ∀ row ∈ output.rows, RowReachable certificate row := by
  obtain ⟨clauses, _, origins⟩ := build_origins problem certificate output success
  intro row member
  exact certificate_row_reachable problem certificate clauses row (origins row member)

end Fang.TstpExport.BuilderProof
