/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The expanded replay with definitional clausification (NAMING-DESIGN.md,
   NAMING-DEVIATIONS.md). Each FOF block is renamed and clausified by the
   generated naming entry, with fresh predicates numbered from the one after the
   equality slot and threaded from block to block. After assembly the equality
   slot moves above the named predicates, and the equality conversion runs with
   a fresh reservation over the original arities and the named ones. Acceptance
   proves, as without naming, that the original bytes have no model. -/
import ExpandedLimitDecoder
import NamingEntry

namespace Fang.TptpCandidate.FullFof.Integration.Named
open Aeneas Aeneas.Std
open Fang.QuantifiedCertificate FangQuantifiedPipeline FangNaming
open Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-- Every predicate of a clausifier formula is below `bound`. -/
def nnfBelow (bound : Nat) : fang_fof_core.Nnf → Bool
  | .Literal literal => decide (literal.predicate.val < bound)
  | .True | .False => true
  | .And left right | .Or left right => nnfBelow bound left && nnfBelow bound right

theorem nnfBelow_sound (bound : Nat) :
    ∀ formula, nnfBelow bound formula = true → PredsBelow bound (FangScopedFof.decodeNnf formula)
  | .Literal literal, check => by
    simpa [nnfBelow, FangScopedFof.decodeNnf, FangScopedFof.decodeLiteral, PredsBelow] using check
  | .True, _ | .False, _ => by simp [FangScopedFof.decodeNnf, PredsBelow]
  | .And left right, check | .Or left right, check => by
    simp only [nnfBelow, Bool.and_eq_true] at check
    exact ⟨nnfBelow_sound bound left check.1, nnfBelow_sound bound right check.2⟩

/-- Every predicate of a problem is below `bound`. -/
def problemBelow (bound : Nat) (problem : Fang.Problem) : Bool :=
  problem.all fun clause => clause.all fun literal => decide (literal.atom.pred < bound)

theorem problemBelow_sound {bound : Nat} {problem : Fang.Problem} (check : problemBelow bound problem = true) :
    ∀ clause ∈ problem, ∀ literal ∈ clause, literal.atom.pred < bound := by
  intro clause member literal inside
  simp only [problemBelow, List.all_eq_true, decide_eq_true_eq] at check
  exact check clause member literal inside

/-- A problem over predicates below `bound` keeps its models when only predicates
    at or above `bound` change. -/
theorem problem_agreeBelow {D : Type} {bound : Nat} {first second : Fang.Interpretation D}
    (agree : AgreeBelow bound first second) {problem : Fang.Problem}
    (below : ∀ clause ∈ problem, ∀ literal ∈ clause, literal.atom.pred < bound)
    (models : problem.Models first) : problem.Models second := by
  intro clause member valuation
  obtain ⟨literal, inside, holds⟩ := models clause member valuation
  refine ⟨literal, inside, ?_⟩
  have same := holds_agreeBelow agree valuation (.lit literal) (below clause member literal inside)
  exact same.mp holds

/-- Remove binders, check the predicate range, then rename and clausify each block,
    threading the next fresh predicate. Returns the blocks, the next free index and
    the arities of the named predicates in order. -/
def replayNamedBlocks (limits : FangOriginalReplay.Limits) (threshold : Usize) (base : Nat) :
    U32 → List fang_skolem_core.fang_quantified_fof_core.Nnf →
      Except FangOriginalReplay.Error (List Fang.Problem × U32 × List Usize)
  | next, [] => .ok ([], next, [])
  | next, formula :: rest => do
    let removed ← FangOriginalReplay.observe (fang_binder_removal_core.remove_universals
      (skolemNnf formula) limits.removal) .removal
    if nnfBelow base (removedNnf removed.formula) then
      let named ← FangOriginalReplay.observe (fang_fof_core.naming.name_then_clausify
        (removedNnf removed.formula) threshold next limits.clausification FangOriginalReplay.initialStatistics)
        .clausification
      let after ← replayNamedBlocks limits threshold base named.next rest
      pure (FangScopedFof.decodeClauses named.clauses.val :: after.1, after.2.1,
        named.definitions.val.map (fun definition => alloc.vec.Vec.len definition.arguments) ++ after.2.2)
    else .error (.input "block predicate at or above the first named predicate")

/-- Obligation 4 for the blocks: a model in which every Skolemized formula holds
    extends, from `next` on, to a model of every clause block. -/
theorem replayNamedBlocks_models (limits : FangOriginalReplay.Limits) (threshold : Usize) (base : Nat)
    {D : Type} [Nonempty D] (source : Fang.Interpretation D) :
    ∀ (formulas : List fang_skolem_core.fang_quantified_fof_core.Nnf) (next : U32)
      (result : List Fang.Problem × U32 × List Usize),
      replayNamedBlocks limits threshold base next formulas = .ok result → base ≤ next.val →
      (∀ formula ∈ formulas, (∃ signature count, InputScoped signature (.Bound count) (skolemNnf formula)) ∧
        Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin [] (FangSkolemCore.decodeIndependentNnf formula) ∧
        ∀ valuation, (FangSkolemCore.decodeIndependentNnf formula).Holds source valuation) →
      ∀ current : Fang.Interpretation D, AgreeBelow base source current →
      ∃ extended : Fang.Interpretation D, AgreeBelow next.val current extended ∧
        Fang.Problem.Models extended result.1.flatten ∧
        (∀ clause ∈ result.1.flatten, ∀ literal ∈ clause, literal.atom.pred < result.2.1.val) ∧
        next.val ≤ result.2.1.val := by
  intro formulas
  induction formulas with
  | nil =>
    intro next result success _ _ current _
    simp only [replayNamedBlocks] at success
    cases Except.ok.inj success
    exact ⟨current, agreeBelow_refl _ current, by simp [Fang.Problem.Models], by simp, le_refl _⟩
  | cons formula rest ih =>
    intro next result success low facts current agree
    simp only [replayNamedBlocks] at success
    obtain ⟨removed, removalRun, success⟩ := bind_success success
    split at success
    next check =>
      obtain ⟨named, namedRun, success⟩ := bind_success success
      obtain ⟨after, afterRun, success⟩ := bind_success success
      cases Except.ok.inj success
      obtain ⟨⟨signature, count, inScope⟩, safe, holds⟩ := facts formula List.mem_cons_self
      have removal := FangOriginalReplay.observe_success removalRun
      have block := nnfBelow_sound base _ check
      have valid := remove_universals_scoped removal signature (.Bound count) inScope
      have removedHolds := (FangBinderRemovalCore.remove_universals_models source removal []
        (by simpa only [skolemNnf_decode] using safe)).mp (by simpa only [skolemNnf_decode] using holds)
      have blockHolds : ∀ valuation,
          (FangScopedFof.decodeNnf (removedNnf removed.formula)).Holds current valuation := by
        intro valuation
        rw [removedNnf_decode] at block ⊢
        exact (holds_agreeBelow agree valuation _ block).mp (removedHolds valuation)
      obtain ⟨grows, below, meaning⟩ := name_then_clausify_spec _ threshold next _ _ named valid
        (predsBelow_mono low _ (nnfBelow_sound base _ check)) (FangOriginalReplay.observe_success namedRun)
      obtain ⟨extended, agreeNext, models⟩ := meaning current blockHolds
      obtain ⟨final, agreeFinal, restModels, restBelow, restGrows⟩ :=
        ih named.next after afterRun (by omega) (fun other member => facts other (List.mem_cons_of_mem _ member))
          extended (agreeBelow_trans agree (agreeBelow_mono low agreeNext))
      refine ⟨final, agreeBelow_trans agreeNext (agreeBelow_mono grows agreeFinal), ?_, ?_, by dsimp only; omega⟩
      · rw [List.flatten_cons, FangQuantifiedPipeline.models_append]
        exact ⟨problem_agreeBelow agreeFinal below models, restModels⟩
      · intro clause member literal inside
        rw [List.flatten_cons, List.mem_append] at member
        rcases member with head | tail
        · exact Nat.lt_of_lt_of_le (below clause head literal inside) restGrows
        · exact restBelow clause tail literal inside
    next => cases success

/-- The new index of predicate `predicate`: the slot moves above the `count` named
    predicates that follow it, and they move down by one. -/
def renumber (slot count predicate : Nat) : Nat :=
  if predicate < slot then predicate else if predicate = slot then slot + count else predicate - 1

/-- The old index of the predicate now at `predicate`. -/
def previous (slot count predicate : Nat) : Nat :=
  if predicate < slot then predicate
  else if predicate = slot + count then slot
  else if predicate < slot + count then predicate + 1 else predicate

theorem previous_renumber (slot count predicate : Nat) (below : predicate ≤ slot + count) :
    previous slot count (renumber slot count predicate) = predicate := by
  unfold previous renumber
  split_ifs <;> omega

def renumberProblem (slot count : Nat) (problem : Fang.Problem) : Fang.Problem :=
  problem.map fun clause => clause.map fun literal =>
    ⟨literal.positive, ⟨renumber slot count literal.atom.pred, literal.atom.args⟩⟩

/-- The interpretation of the renumbered problem: each predicate reads its old index. -/
def renumberedModel {D : Type} (slot count : Nat) (model : Fang.Interpretation D) : Fang.Interpretation D where
  function := model.function
  predicate predicate arguments := model.predicate (previous slot count predicate) arguments

theorem renumber_models {D : Type} (slot count : Nat) (problem : Fang.Problem)
    (below : ∀ clause ∈ problem, ∀ literal ∈ clause, literal.atom.pred ≤ slot + count)
    (model : Fang.Interpretation D) (models : problem.Models model) :
    (renumberProblem slot count problem).Models (renumberedModel slot count model) := by
  intro clause member valuation
  simp only [renumberProblem, List.mem_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  obtain ⟨literal, inside, holds⟩ := models original originalMember valuation
  refine ⟨⟨literal.positive, ⟨renumber slot count literal.atom.pred, literal.atom.args⟩⟩,
    List.mem_map_of_mem inside, ?_⟩
  have arguments : literal.atom.args.map (Fang.Term.eval (renumberedModel slot count model) valuation) =
      literal.atom.args.map (Fang.Term.eval model valuation) :=
    List.map_congr_left (fun term _ =>
      eval_functions (first := renumberedModel slot count model) (second := model) rfl valuation term)
  simp only [Fang.Literal.Holds, Fang.Atom.Holds] at holds ⊢
  rw [arguments]
  simp only [renumberedModel, previous_renumber slot count _ (below original originalMember literal inside)]
  exact holds

inductive NamedError where
  | replay : ReplayError → NamedError
  | slot
  | range
  | table
  | reservation : fang_fof_equality_bridge.Error → NamedError
  | reservationEffect

def observeReservation
    (action : Result (core.result.Result fang_fof_equality_bridge.Reservation fang_fof_equality_bridge.Error)) :
    Except NamedError fang_fof_equality_bridge.Reservation :=
  match action.match with
  | .ok (.Ok value) => .ok value
  | .ok (.Err error) => .error (.reservation error)
  | _ => .error .reservationEffect

theorem observeReservation_success {action value} (success : observeReservation action = .ok value) :
    action = .ok (.Ok value) := by
  unfold observeReservation at success
  split at success
  · rename_i matched
    cases success
    exact Result.match.isOk.mp matched
  · cases success
  · cases success

def tableOf (values : List Usize) : Except NamedError (alloc.vec.Vec Usize) :=
  if bound : values.length ≤ Usize.max then .ok (alloc.vec.Vec.from values bound) else .error .table

theorem tableOf_success {values table} (success : tableOf values = .ok table) : table.val = values := by
  unfold tableOf at success
  split at success
  · cases success
    simp
  · cases success

/-- The first named predicate, one after the equality slot. -/
def firstNamed (slot : U32) : Except NamedError U32 :=
  match U32.checked_add slot 1#u32 with
  | some value => .ok value
  | none => .error .slot

theorem firstNamed_success {slot first : U32} (success : firstNamed slot = .ok first) :
    first.val = slot.val + 1 := by
  unfold firstNamed at success
  split at success
  · rename_i value checked
    cases success
    exact checked_add_eq_some checked
  · cases success

/-- After assembly: check the predicate ranges, move the equality slot above the
    named predicates, reserve it over the original and the named arities, and convert. -/
def finishNamed (numeric : NumericInput) (original : fang_fof_equality_bridge.Reservation)
    (functions : List Nat) (first : U32) (named : List Fang.Problem × U32 × List Usize) (ordinary : Fang.Problem)
    (maximumPredicates maximumLiterals : Usize) : Except NamedError ReplayPrepared :=
  if problemBelow first.val (retained numeric.declarations) && problemBelow named.2.1.val ordinary &&
      named.2.2.length == named.2.1.val - first.val then do
    let table ← tableOf (original.original_predicates.val ++ named.2.2)
    let reservation ← observeReservation (fang_fof_equality_bridge.Reservation.new table maximumPredicates)
    let equality ← ((FangQuantifiedEqualityReplay.Conversion.problem reservation maximumLiterals
      (renumberProblem original.equality.val (named.2.1.val - first.val) ordinary)).mapError .conversion).mapError
      .replay
    pure ⟨numeric, equality, functions, numeric.predicates.map Prod.snd ++ named.2.2.map (fun value => value.val)⟩
  else .error .range

/-- The limited preparation of `ExpandedLimitDecoder` with naming. -/
def prepareNamed (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except NamedError ReplayPrepared := do
  let numeric ← (decodeNumericLimited limit bytes maximumBytes).mapError .replay
  let encoded ← ((transport numeric maximumPredicates).mapError .transport).mapError .replay
  let transformed ← ((FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing).mapError .replay
  let first ← firstNamed encoded.reservation.equality
  let named ← ((replayNamedBlocks limits threshold first.val first transformed.formulas.val).mapError
    .preprocessing).mapError .replay
  let ordinary ← ((FangOriginalReplay.assemble numeric.declarations named.1).mapError .preprocessing).mapError .replay
  finishNamed numeric encoded.reservation (transformed.signature.functions.val.map (fun value => value.val)) first
    named ordinary maximumPredicates maximumLiterals

theorem mapError_twice {α ε₁ ε₂ ε₃ : Type} {action : Except ε₁ α} {first : ε₁ → ε₂} {second : ε₂ → ε₃} {value : α}
    (success : (action.mapError first).mapError second = .ok value) : action = .ok value :=
  mapError_success (mapError_success success)

/-- Acceptance of the named preparation excludes every original byte model, for every
    declaration limit and threshold. -/
theorem prepareNamed_check_original_unsat {limit bytes maximumBytes limits threshold maximumPredicates
    maximumLiterals prepared}
    (success : prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  unfold prepareNamed at success
  obtain ⟨numeric, decoded, success⟩ := bind_success success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨first, firstRun, success⟩ := bind_success success
  obtain ⟨named, namedRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  unfold finishNamed at success
  split at success
  next checks =>
    obtain ⟨table, tableRun, success⟩ := bind_success success
    obtain ⟨reservation, reservationRun, success⟩ := bind_success success
    obtain ⟨equality, conversionRun, success⟩ := bind_success success
    cases Except.ok.inj success
    simp only [Bool.and_eq_true, beq_iff_eq] at checks
    obtain ⟨⟨retainedCheck, ordinaryCheck⟩, countCheck⟩ := checks
    have firstValue := firstNamed_success firstRun
    obtain ⟨values, parsed, numericRun⟩ := decodeNumericLimited_witness (mapError_success decoded)
    apply decodeUpTo_readInput_unsat parsed numericRun
    rintro ⟨D, nonempty, original, holds⟩
    let : Nonempty D := nonempty
    have inputSuccess := mapError_twice inputRun
    obtain ⟨valid, _, slotEq, _, _, _⟩ := transport_tables inputSuccess
    have originalHolds := transport_models inputSuccess holds
    have reservedHolds :
        (retained numeric.declarations).Models
          (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
        SignedDeclarationsHold
          (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
          encoded.declarations.val := by
      rw [slotEq, ← reserve_interpretation]
      exact originalHolds
    have skolemSuccess := FangOriginalReplay.observe_success (mapError_twice skolemRun)
    obtain ⟨skolemized, preserved, meaning⟩ := FangSkolemCore.skolemize_problem_independent_meaning
      skolemSuccess (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
    have formulasHold : ∀ formula ∈ transformed.formulas.val, ∀ valuation,
        (FangSkolemCore.decodeIndependentNnf formula).Holds skolemized valuation :=
      fun formula member valuation =>
        (meaning valuation).mp (fun declaration present => reservedHolds.2 declaration present valuation) formula member
    have retainedSkolem : (retained numeric.declarations).Models skolemized :=
      (problem_preserved preserved _ (transport_retained_below numericRun inputSuccess)).mpr reservedHolds.1
    obtain ⟨extended, agree, blocksModels, blocksBelow, grows⟩ :=
      replayNamedBlocks_models limits threshold first.val skolemized transformed.formulas.val first named
        (mapError_twice namedRun) (le_refl _)
        (fun formula member =>
          ⟨⟨_, skolemize_problem_scoped skolemSuccess formula member⟩,
            (FangSkolemCore.skolemize_problem_output skolemSuccess formula member).1,
            formulasHold formula member⟩)
        skolemized (agreeBelow_refl _ skolemized)
    have retainedModels : (retained numeric.declarations).Models extended :=
      problem_agreeBelow agree (problemBelow_sound retainedCheck) retainedSkolem
    have layout := FangOriginalReplay.assemble_layout (mapError_twice assemblyRun)
    have ordinaryModels : ordinary.Models extended :=
      (mixedLayout_models layout extended).mpr ⟨retainedModels, blocksModels⟩
    have renumbered := renumber_models encoded.reservation.equality.val (named.2.1.val - first.val) ordinary
      (fun clause member literal inside => by
        have := problemBelow_sound ordinaryCheck clause member literal inside
        omega)
      extended ordinaryModels
    have reservationPost := spec_eq_ok (FangEqualityBridge.reservation_new_spec table maximumPredicates)
      (observeReservation_success reservationRun)
    obtain ⟨tableSame, reservationValid, _⟩ := reservationPost
    have slotLength : encoded.reservation.equality.val = encoded.reservation.original_predicates.val.length := valid
    have equalityIndex : reservation.equality.val =
        encoded.reservation.equality.val + (named.2.1.val - first.val) := by
      have lengths := reservationValid
      unfold FangEqualityBridge.ValidReservation at lengths
      rw [lengths, tableSame, tableOf_success tableRun, List.length_append, countCheck, ← slotLength]
    have preserved' : Fang.QuantifiedFOF.Skolem.PreservesBelow 0
        (Fang.EqualityBridge.reserveInterpretation reservation.equality.val
          (renumberedModel encoded.reservation.equality.val (named.2.1.val - first.val) extended))
        (renumberedModel encoded.reservation.equality.val (named.2.1.val - first.val) extended) := by
      refine ⟨fun symbol below => absurd below (Nat.not_lt_zero _), fun predicate arguments => ?_⟩
      simp only [Fang.EqualityBridge.reserveInterpretation]
      split
      · rename_i atSlot
        rw [atSlot, equalityIndex]
        have back : previous encoded.reservation.equality.val (named.2.1.val - first.val)
            (encoded.reservation.equality.val + (named.2.1.val - first.val)) = encoded.reservation.equality.val := by
          unfold previous
          split_ifs <;> omega
        simp only [renumberedModel, back]
        rw [← agree.2 _ (by omega), preserved.2]
        simp [Fang.EqualityBridge.reserveInterpretation]
      · rfl
    have converted := FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_twice conversionRun)
    have equalityModel := (FangQuantifiedEquality.actualProblem_models _ _ reservation 0 reservationValid
      preserved' converted).mp renumbered
    exact Fang.Equality.Ordered.check_unsat _ certificate accepted
      ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation _ _, equalityModel⟩
  next => cases success

inductive AcceptNamedError where
  | replay : NamedError → AcceptNamedError
  | certificate : CertificateError → AcceptNamedError

/-- The native entry with naming: the same envelope and checker as `acceptsLimited`. -/
def acceptsNamed (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except AcceptNamedError Unit := do
  let prepared ← (prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals).mapError
    .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

/-- Acceptance proves that the original bytes have no model, for every declaration limit and threshold. -/
theorem acceptsNamed_original_unsat {limit bytes maximumBytes proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  exact prepareNamed_check_original_unsat (mapError_success replayRun) parsed refuted

/-- The arities of the named predicates come from the definitions of the naming
    run, which the theorems above do not describe. On acceptance every atom of the
    checked problem has exactly the arity the table lists for its predicate, so a
    table that disagrees with the clauses can only be refused. -/
theorem acceptsNamed_signature {limit bytes maximumBytes proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    ∃ prepared, prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed prepared.functionArities
        prepared.predicateArities) = true := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  obtain ⟨_, _, wellFormed, _, _⟩ := checkProblem_success (mapError_success checked)
  exact ⟨prepared, mapError_success replayRun, wellFormed⟩

end Fang.TptpCandidate.FullFof.Integration.Named
