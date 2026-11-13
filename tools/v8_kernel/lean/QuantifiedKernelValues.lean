/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Values observed from the retained negative-quantifier Rust fixture.
   These definitions alone make no claim about generated execution. -/
import QuantifiedKernelPrimitives

open Aeneas Aeneas.Std
namespace FangQuantifiedKernel

def arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term :=
  vector [.Var 0#u32] (by simp; scalar_tac)

def firstFormula : fang_skolem_core.fang_quantified_fof_core.Formula :=
  .Not (.Exists 0#u32 (.Atom 0#u32 arguments))

def secondFormula : fang_skolem_core.fang_quantified_fof_core.Formula :=
  .Exists 0#u32 (.Atom 0#u32 arguments)

def declarations : Slice fang_skolem_core.Declaration :=
  Slice.from [⟨firstFormula, true⟩, ⟨secondFormula, true⟩] (by simp; scalar_tac)

def signature : fang_skolem_core.fang_quantified_fof_core.Signature :=
  ⟨vector [] (by simp), vector [1#usize] (by simp; scalar_tac)⟩

def firstNnf : fang_skolem_core.fang_quantified_fof_core.Nnf :=
  .Forall 0#u32 (.Literal ⟨false, 0#u32, arguments⟩)

def secondNnf : fang_skolem_core.fang_quantified_fof_core.Nnf :=
  .Literal ⟨true, 0#u32,
    vector [.Fun 0#u32 (vector [] (by simp))] (by simp; scalar_tac)⟩

def transformed : fang_skolem_core.Skolemized := {
  formulas := vector [firstNnf, secondNnf] (by simp; scalar_tac)
  signature := ⟨vector [0#usize] (by simp; scalar_tac), signature.predicates⟩
  introduced := vector [⟨1#usize, 0#u32, 0#u32, vector [] (by simp)⟩] (by simp; scalar_tac)
  statistics := ⟨50#usize, 29#usize⟩ }

end FangQuantifiedKernel
