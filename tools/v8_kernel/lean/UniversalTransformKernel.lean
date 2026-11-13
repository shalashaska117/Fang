/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The actual retained universal branch for the first captured declaration. -/
import SkolemCopyKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core
open SkolemWork
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def firstBefore : Transformer := {
  functions := alloc.vec.Vec.new _
  introduced := alloc.vec.Vec.new _
  universals := ⟨alloc.vec.Vec.new _, 0#usize⟩
  declaration := 0#usize
  work := work 27#usize 9#usize }

def firstAfter : Transformer := {
  firstBefore with
  universals := ⟨vector [0#u32] (by simp; scalar_tac), 0#usize⟩
  work := work 31#usize 13#usize }

theorem first_transform : Transformer.transform firstBefore firstNnf skolemLimits =
    .ok (.Ok firstNnf, firstAfter) := by
  have termCopy := SkolemCopy.variable_term 0#u32
    (work 30#usize 12#usize) (work 31#usize 12#usize) (work 31#usize 13#usize)
    (by reduce_skolem_work) (by reduce_skolem_work)
  have literalCopy := SkolemCopy.literal_one false 0#u32 (.Var 0#u32) (.Var 0#u32)
    skolemLimits (work 30#usize 12#usize) (work 31#usize 13#usize) termCopy
  unfold firstBefore firstNnf
  erw [Transformer.transform]
  reduce_skolem_work
  simp only [Universals.push]
  reduce_skolem_work
  simp only [push_empty, bind_ok]
  erw [Transformer.transform]
  reduce_skolem_work
  erw [literalCopy]
  simp (disch := scalar_tac) [firstAfter, firstBefore, arguments, vector, work,
    Universals.pop, sub_value, Aeneas.Std.uncurry]

#print axioms FangQuantifiedKernel.first_transform
end FangQuantifiedKernel
