/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Validate proposed output names against actual source and prepared tables.
   Rust chooses fresh names; this independent checker does not generate them. -/
import EqualityBody
import ExtendedTables

namespace Fang.QuantifiedEqualityTstp.Naming

def symbols (entries : List (String × Nat)) : List Frontend.Symbol :=
  entries.map (fun entry => ⟨entry.1, some entry.2⟩)

def keys (entries : List Frontend.Symbol) : List (String × Option Nat) :=
  entries.map (fun entry => (entry.name, entry.arity))

def originalNames (functions predicates : List (String × Nat)) : List String :=
  functions.map Prod.fst ++ predicates.map Prod.fst

/-- New symbols use distinct spellings and avoid both original namespaces.
    Original symbols may share a spelling when their arities differ. -/
def fresh (original : List String) (extra : List Frontend.Symbol) : Bool :=
  decide (extra.map Frontend.Symbol.name).Nodup &&
    (extra.map Frontend.Symbol.name).all (fun value => !original.contains value)

theorem fresh_spec {original extra} (checked : fresh original extra = true) :
    (extra.map Frontend.Symbol.name).Nodup ∧
      ∀ value ∈ extra.map Frontend.Symbol.name, value ∉ original := by
  simp only [fresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
  refine ⟨checked.1, ?_⟩
  intro value member
  simpa using checked.2 value member

theorem drop_prefix {α : Type} (before after : List α) :
    (before ++ after).drop before.length = after := by
  induction before with
  | nil => rfl
  | cons head tail ih => exact ih

structure Checked (originalFunctions originalPredicates : List (String × Nat))
    (prepared : FangQuantifiedEqualityReplay.Prepared) (names : Body.Names) : Prop where
  originalPrefix : ∃ extra, names.functions = symbols originalFunctions ++ extra ∧
    fresh (originalNames originalFunctions originalPredicates) extra = true
  originalPredicates : names.predicates = symbols originalPredicates
  functionArities : names.functions.map Frontend.Symbol.arity = prepared.functionArities.map some
  predicateArities : names.predicates.map Frontend.Symbol.arity = prepared.predicateArities.map some
  functionKeys : (keys names.functions).Nodup
  predicateKeys : (keys names.predicates).Nodup

/-- Printability is checked by the renderer. This check preserves the complete
    original prefix, including unused symbols, and admits arity overloading. -/
def check (originalFunctions originalPredicates : List (String × Nat))
    (prepared : FangQuantifiedEqualityReplay.Prepared) (functions : List Frontend.Symbol) :
    Except String Body.Names :=
  if !QuantifiedTstp.Tables.isPrefix (symbols originalFunctions) functions then
    .error "export-error: original function table changed"
  else if functions.map Frontend.Symbol.arity ≠ prepared.functionArities.map some then
    .error "export-error: prepared function arities differ"
  else if (symbols originalPredicates).map Frontend.Symbol.arity ≠ prepared.predicateArities.map some then
    .error "export-error: prepared predicate arities differ"
  else if ¬ ((keys functions).Nodup ∧ (keys (symbols originalPredicates)).Nodup) then
    .error "export-error: duplicate symbol name and arity"
  else if !fresh (originalNames originalFunctions originalPredicates)
      (functions.drop (symbols originalFunctions).length) then
    .error "export-error: fresh function name collision"
  else .ok ⟨functions, symbols originalPredicates⟩

theorem check_spec {originalFunctions originalPredicates prepared functions names}
    (success : check originalFunctions originalPredicates prepared functions = .ok names) :
    Checked originalFunctions originalPredicates prepared names := by
  unfold check at success
  split at success
  · cases success
  rename_i prefixValid
  split at success
  · cases success
  rename_i functionsValid
  split at success
  · cases success
  rename_i predicatesValid
  split at success
  · cases success
  rename_i keysValid
  split at success
  · cases success
  rename_i freshValid
  cases success
  have prefixChecked : QuantifiedTstp.Tables.isPrefix (symbols originalFunctions) functions = true := by
    simpa using prefixValid
  obtain ⟨extra, extended⟩ := QuantifiedTstp.Tables.prefix_append prefixChecked
  have freshChecked : fresh (originalNames originalFunctions originalPredicates) extra = true := by
    have dropped := drop_prefix (symbols originalFunctions) extra
    rw [← extended] at dropped
    rw [← dropped]
    simpa using freshValid
  have keysChecked := Decidable.of_not_not keysValid
  exact ⟨⟨extra, extended, freshChecked⟩, rfl, Decidable.of_not_not functionsValid,
    Decidable.of_not_not predicatesValid, keysChecked.1, keysChecked.2⟩

theorem check_ok {originalFunctions originalPredicates prepared functions}
    (accepted : (check originalFunctions originalPredicates prepared functions).toBool = true) :
    ∃ names, check originalFunctions originalPredicates prepared functions = .ok names := by
  cases result : check originalFunctions originalPredicates prepared functions with
  | error reason => simp [result, Except.toBool] at accepted
  | ok names => exact ⟨names, rfl⟩

inductive Error where
  | build : FangQuantifiedEqualityCertificate.Error → Error
  | input : FangQuantifiedEqualityInput.Error → Error
  | table : String → Error

/-- Re-decode the captured original input to bind names. Preprocessing and
    inference checking are not repeated here. The source table is not supplied
    by the caller and the temporary equality predicate is never exported. -/
def attach (input : String) (maximumPredicates : Aeneas.Std.Usize)
    (output : Output) (functions : List Frontend.Symbol) : Except Error Body.Names :=
  match FangQuantifiedEqualityInput.prepareInput input maximumPredicates with
  | .error reason => .error (.input reason)
  | .ok encoded =>
    match check encoded.original.functions encoded.original.originalPredicates output.prepared functions with
    | .error reason => .error (.table reason)
    | .ok names => .ok names

theorem attach_witness {input maximumPredicates output functions names}
    (success : attach input maximumPredicates output functions = .ok names) :
    ∃ encoded, FangQuantifiedEqualityInput.prepareInput input maximumPredicates = .ok encoded ∧
      Checked encoded.original.functions encoded.original.originalPredicates output.prepared names := by
  cases encodedRun : FangQuantifiedEqualityInput.prepareInput input maximumPredicates with
  | error reason =>
    rw [attach, encodedRun] at success
    cases success
  | ok encoded =>
    cases checked : check encoded.original.functions encoded.original.originalPredicates output.prepared functions with
    | error reason =>
      rw [attach, encodedRun] at success
      dsimp only at success
      rw [checked] at success
      cases success
    | ok result =>
      rw [attach, encodedRun] at success
      dsimp only at success
      rw [checked] at success
      cases success
      exact ⟨encoded, rfl, check_spec checked⟩

structure NamedOutput where
  core : Output
  names : Body.Names

def buildNamed (input proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (functions : List Frontend.Symbol) : Except Error NamedOutput :=
  match build input proof limits maximumPredicates maximumLiterals with
  | .error reason => .error (.build reason)
  | .ok output =>
    match attach input maximumPredicates output functions with
    | .error reason => .error reason
    | .ok names => .ok ⟨output, names⟩

theorem buildNamed_witness {input proof limits maximumPredicates maximumLiterals functions output}
    (success : buildNamed input proof limits maximumPredicates maximumLiterals functions = .ok output) :
    build input proof limits maximumPredicates maximumLiterals = .ok output.core ∧
      ∃ encoded, FangQuantifiedEqualityInput.prepareInput input maximumPredicates = .ok encoded ∧
        Checked encoded.original.functions encoded.original.originalPredicates output.core.prepared output.names := by
  cases coreRun : build input proof limits maximumPredicates maximumLiterals with
  | error reason =>
    rw [buildNamed, coreRun] at success
    cases success
  | ok core =>
    cases namesRun : attach input maximumPredicates core functions with
    | error reason =>
      rw [buildNamed, coreRun] at success
      dsimp only at success
      rw [namesRun] at success
      cases success
    | ok names =>
      rw [buildNamed, coreRun] at success
      dsimp only at success
      rw [namesRun] at success
      cases success
      exact ⟨rfl, attach_witness namesRun⟩

theorem buildNamed_original_unsat {input proof limits maximumPredicates maximumLiterals functions output}
    (success : buildNamed input proof limits maximumPredicates maximumLiterals functions = .ok output) :
    ¬ NamedQuantifiedEquality.Grammar.BytesSatisfiable (Source.Grammar.spelling input) :=
  build_original_unsat (buildNamed_witness success).1

theorem buildNamed_original_decode {input proof limits maximumPredicates maximumLiterals functions output}
    (success : buildNamed input proof limits maximumPredicates maximumLiterals functions = .ok output) :
    ∃ decoded, QuantifiedEqualityFrontend.decode input = .ok decoded ∧
      Checked decoded.functions decoded.originalPredicates output.core.prepared output.names := by
  obtain ⟨_, encoded, prepared, checked⟩ := buildNamed_witness success
  exact ⟨encoded.original, (FangQuantifiedEqualityInput.prepareInput_runs prepared).1, checked⟩

/-- The exported predicate table is exactly the decoded original table. The
    temporary equality predicate reserved after it is never a named symbol. -/
theorem buildNamed_predicates {input proof limits maximumPredicates maximumLiterals functions output}
    (success : buildNamed input proof limits maximumPredicates maximumLiterals functions = .ok output) :
    ∃ decoded, QuantifiedEqualityFrontend.decode input = .ok decoded ∧
      output.names.predicates = symbols decoded.originalPredicates ∧
      output.names.predicates.length = decoded.originalPredicates.length := by
  obtain ⟨decoded, decodedRun, checked⟩ := buildNamed_original_decode success
  refine ⟨decoded, decodedRun, checked.originalPredicates, ?_⟩
  rw [checked.originalPredicates, symbols, List.length_map]

#print axioms Fang.QuantifiedEqualityTstp.Naming.fresh_spec
#print axioms Fang.QuantifiedEqualityTstp.Naming.drop_prefix
#print axioms Fang.QuantifiedEqualityTstp.Naming.check_spec
#print axioms Fang.QuantifiedEqualityTstp.Naming.check_ok
#print axioms Fang.QuantifiedEqualityTstp.Naming.attach_witness
#print axioms Fang.QuantifiedEqualityTstp.Naming.buildNamed_witness
#print axioms Fang.QuantifiedEqualityTstp.Naming.buildNamed_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.Naming.buildNamed_original_decode
#print axioms Fang.QuantifiedEqualityTstp.Naming.buildNamed_predicates

end Fang.QuantifiedEqualityTstp.Naming
