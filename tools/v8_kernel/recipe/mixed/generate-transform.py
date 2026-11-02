#!/usr/bin/env python3
"""Emit an actual public Skolem equation with the observed complete result."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.


def emit(g, render_nnf, witness, namespace):
    g.require(g.re.fullmatch(r'[A-Z][A-Za-z0-9]*', namespace), 'Invalid namespace')
    observed = witness['skolem']
    code = '/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Complete observed output is an untrusted witness to the actual public call. -/\n'
    code += f'import {namespace}Preparation\nimport TransformPrimitives\nimport SkolemProblemKernel\nopen Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    code += 'def skolemized : fang_skolem_core.Skolemized := {\n  formulas := ' + g.vec([render_nnf(g, value) for value in observed['formulas']]) + '\n'
    code += '  signature := ⟨' + g.vec([str(n) + '#usize' for n in observed['functions']]) + ', ' + g.vec([str(n) + '#usize' for n in observed['predicates']]) + '⟩\n'
    origins = ['⟨' + str(declaration) + '#usize, ' + str(binder) + '#u32, ' + str(function) + '#u32, ' + g.vec([str(n) + '#u32' for n in universals]) + '⟩' for declaration, binder, function, universals in observed['introduced']]
    code += '  introduced := ' + g.vec(origins) + '\n  statistics := ⟨' + ', '.join(str(n) + '#usize' for n in observed['statistics']) + '⟩ }\n'
    code += 'theorem skolemize_eq : fang_skolem_core.skolemize_problem declarations signature skolemLimits =\n    .ok (.Ok skolemized) := by\n'
    code += '  have declarationsFit : ¬ Slice.len declarations > skolemLimits.max_declarations := by\n    simp [declarations, skolemLimits]\n'
    code += '  have functionsFit : ¬ alloc.vec.Vec.len signature.functions >\n      core.cmp.impls.OrdUsize.min skolemLimits.max_functions\n        (UScalar.cast .Usize core.num.U32.MAX) := by\n    rw [FangQuantifiedKernel.function_cap]\n    simp [signature, FangQuantifiedKernel.vector, alloc.vec.Vec.val]\n'
    code += '  unfold fang_skolem_core.skolemize_problem\n  rw [ite_eq_right declarationsFit]\n  simp only [lift, bind_ok]\n  rw [ite_eq_right functionsFit]\n  simp only [fang_skolem_core.Statistics.Insts.CoreDefaultDefault.default, default_value, bind_ok]\n  erw [validate_declarations_eq]\n  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry]\n  erw [copy_functions_eq]\n  simp only [bind_ok, Aeneas.Std.uncurry]\n  erw [copy_predicates_eq]\n  simp only [bind_ok, Aeneas.Std.uncurry]\n'
    code += '  simp only [declarations, signature, preparedWork, skolemized, ' + ', '.join('formula' + str(i) for i in range(len(witness['declarations']))) + ']\n  generated_transform\n'
    code += f'#print axioms {namespace}.skolemize_eq\nend {namespace}\n'
    return {namespace + 'Skolem': code}
