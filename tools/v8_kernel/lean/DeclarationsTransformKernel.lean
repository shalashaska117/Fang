/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact ordered composition of the two captured preprocessing calls. -/
import SkolemLoopKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core
open SkolemWork
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def initialTransformer : Transformer := { firstBefore with work := work 12#usize 1#usize }
def afterFirstDeclaration : Transformer := {
  firstAfter with declaration := 1#usize, work := work 31#usize 14#usize }
def finalTransformer : Transformer := {
  secondAfter with declaration := 2#usize, work := work 50#usize 29#usize }
def bothNnfs : alloc.vec.Vec fang_quantified_fof_core.Nnf :=
  vector [firstNnf, secondNnf] (by simp; scalar_tac)

theorem transform_second_declaration :
    transform_declarations_loop declarations signature skolemLimits afterFirstDeclaration
      (vector [firstNnf] (by simp; scalar_tac)) = .ok (.Ok bothNnfs, finalTransformer) := by
  apply declaration_step declarations signature skolemLimits afterFirstDeclaration
    (vector [firstNnf] (by simp; scalar_tac)) ⟨secondFormula, true⟩
    (work 32#usize 14#usize) (coreLimits 4999968#usize 999986#usize)
    ⟨.Exists 0#u32 (.Literal ⟨true, 0#u32, arguments⟩),
      (coreWork 11#usize 2#usize 1#usize 7#usize 1#usize).statistics⟩
    (work 43#usize 21#usize) secondNnf secondAfter (work 50#usize 29#usize)
    bothNnfs 2#usize bothNnfs finalTransformer
  · simp [afterFirstDeclaration, declarations]
  · change Work.tick (work 31#usize 14#usize) skolemLimits = _
    reduce_skolem_work
  · simp (disch := scalar_tac) [afterFirstDeclaration, declarations, Slice.index_usize]
  · exact remaining_value 32#usize 14#usize (by scalar_tac) (by scalar_tac)
  · exact normalization_second 4999968#usize 999986#usize (by scalar_tac) (by scalar_tac)
  · simp only [coreWork]
    reduce_skolem_work
  · exact second_transform
  · change Work.allocate (work 50#usize 28#usize) 1#usize skolemLimits = _
    reduce_skolem_work
  · exact push_values _ _ (by simp [vector, alloc.vec.Vec.val]; scalar_tac)
  · exact add_value 1#usize 1#usize (by scalar_tac)
  · rfl
  · exact declarations_finished declarations signature skolemLimits finalTransformer bothNnfs
      (by simp [finalTransformer, declarations])

theorem transform_declarations_exact :
    transform_declarations declarations signature skolemLimits initialTransformer =
      .ok (.Ok bothNnfs, finalTransformer) := by
  unfold transform_declarations
  apply declaration_step declarations signature skolemLimits initialTransformer
    (alloc.vec.Vec.new _) ⟨firstFormula, true⟩
    (work 13#usize 1#usize) (coreLimits 4999987#usize 999999#usize)
    ⟨firstNnf, (coreWork 14#usize 3#usize 1#usize 8#usize 1#usize).statistics⟩
    (work 27#usize 9#usize) firstNnf firstAfter (work 31#usize 14#usize)
    (vector [firstNnf] (by simp; scalar_tac)) 1#usize bothNnfs finalTransformer
  · simp [initialTransformer, firstBefore, declarations]
  · change Work.tick (work 12#usize 1#usize) skolemLimits = _
    reduce_skolem_work
  · simp (disch := scalar_tac) [initialTransformer, firstBefore, declarations, Slice.index_usize]
  · exact remaining_value 13#usize 1#usize (by scalar_tac) (by scalar_tac)
  · exact normalization_first 4999987#usize 999999#usize (by scalar_tac) (by scalar_tac)
  · simp only [coreWork]
    reduce_skolem_work
  · exact first_transform
  · change Work.allocate (work 31#usize 13#usize) 1#usize skolemLimits = _
    reduce_skolem_work
  · exact push_empty _
  · exact add_value 0#usize 1#usize (by scalar_tac)
  · rfl
  · exact transform_second_declaration

#print axioms FangQuantifiedKernel.transform_second_declaration
#print axioms FangQuantifiedKernel.transform_declarations_exact
end FangQuantifiedKernel
