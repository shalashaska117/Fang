/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Model acceptance on the three checking paths, over the decoders and framers the refutation checkers run: the
   counted single-file decoder `decodeBytesLimited`, the bundle frame `BundleLimit.limited` and the role frame
   `V3.limited`. Each endpoint concludes the positive meaning of its path for the original bytes, with no premise
   about the certificate: `CnfBoolean.BytesSatisfiable`, `FramerLimit.ByteBundleSatisfiable`,
   `V3.ByteInputsSatisfiable` and `V3.GoalCountermodel`. Statements are decided by the step-counted evaluation of
   `ModelSteps` on their rewritten forms, with one budget of `Limits.maximumWork` steps for the whole task. -/
import ModelCertificate
import ModelSteps
import ModelMeanings
import ExpandedLimitDecoder
import BundleReplayLimit
import RoleReplayLimit

namespace Fang.TptpCandidate.FullFof.Model

inductive ModelError where
  | input : Fang.TptpCandidate.Error → ModelError
  | expand : Coverage.Failure → ModelError
  | shape
  | modes
  | noGoal
  | goalsPresent
  | certificate : CertificateError → ModelError
  /-- The evaluation used up `Limits.maximumWork` steps. -/
  | work
  | rejected : Rejection → ModelError
  | goalHolds
  | goalScope
  | objects

/-- The certificate read against every statement of the input. -/
def readModel (limits : Limits) (certificate : String) (statements : List Formula) :
    Except ModelError FiniteModel :=
  match readCertificate limits certificate statements with
  | .error problem => .error (.certificate problem)
  | .ok model => .ok model

def stepFailure : StepFailure → ModelError
  | .rejected reason => .rejected reason
  | .work => .work

/-- Every statement decided with the step budget `limits.maximumWork`; the steps left. -/
def checkAll (limits : Limits) (model : FiniteModel) (formulas : List Formula) : Except ModelError Nat :=
  (checkSteps model 0 formulas limits.maximumWork).mapError stepFailure

theorem checkAll_sound {limits : Limits} {model : FiniteModel} {formulas : List Formula} {left : Nat}
    (accepted : checkAll limits model formulas = .ok left) :
    ∀ formula ∈ formulas, ∀ valuation, formula.Holds model.interpretation valuation :=
  checkSteps_sound model formulas 0 limits.maximumWork left (mapError_ok accepted)

/-! Single file. -/

def acceptsSingle (limits : Limits) (declarationLimit : Nat) (bytes : List UInt8) (maximumBytes : Nat)
    (certificate : String) : Except ModelError Unit := do
  let values ← (Integration.decodeBytesLimited declarationLimit bytes maximumBytes).mapError .input
  let model ← readModel limits certificate (source values)
  let _ ← checkAll limits model (source values)
  pure ()

/-- Acceptance proves that the original bytes have a model, for every declaration limit and every bound. -/
theorem acceptsSingle_satisfiable {limits : Limits} {declarationLimit : Nat} {bytes : List UInt8}
    {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsSingle limits declarationLimit bytes maximumBytes certificate = .ok ()) :
    CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨values, decoded, rest⟩ := bind_ok accepted
  obtain ⟨model, _, rest⟩ := bind_ok rest
  obtain ⟨_, checked, _⟩ := bind_ok rest
  have holds := checkAll_sound checked
  have parsed := mapError_ok decoded
  rw [Integration.decodeBytesLimited_eq] at parsed
  exact (Integration.decodeUpTo_bytes_satisfiable parsed).mpr ⟨model.Element, inferInstance, model.interpretation, holds⟩

/-! Bundle without roles other than axiom. -/

def acceptsBundle (limits : Limits) (frame : Coverage.FramerLimit.Frame) (files : List (Coverage.Key × List UInt8))
    (maximumBytes : Nat) (certificate : String) : Except ModelError Unit :=
  match frame files maximumBytes with
  | .error problem => .error (.input problem)
  | .ok bundle =>
    match Coverage.expand bundle Coverage.BundleV8.bundleFuel with
    | .error problem => .error (.expand problem)
    | .ok items =>
      if Coverage.FramerV2.wellShaped bundle Coverage.BundleV8.bundleFuel then do
        let model ← readModel limits certificate (source (Coverage.declarationsOf bundle items))
        let _ ← checkAll limits model (source (Coverage.declarationsOf bundle items))
        if separated model (Coverage.FramerV2.objectNames (Coverage.declarationsOf bundle items)) then pure ()
        else .error .objects
      else .error .shape

theorem acceptsBundle_satisfiable {limits : Limits} {frame : Coverage.FramerLimit.Frame}
    {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsBundle limits frame files maximumBytes certificate = .ok ()) :
    Coverage.FramerLimit.ByteBundleSatisfiable frame files maximumBytes Coverage.BundleV8.bundleFuel := by
  unfold acceptsBundle at accepted
  split at accepted
  · cases accepted
  · rename_i bundle framed
    split at accepted
    · cases accepted
    · rename_i items expanded
      split at accepted
      · rename_i shaped
        obtain ⟨model, _, rest⟩ := bind_ok accepted
        obtain ⟨_, checked, final⟩ := bind_ok rest
        split at final
        · rename_i apart
          exact ⟨bundle, items, framed, shaped, expanded, model.Element, inferInstance, model.interpretation,
            checkAll_sound checked, (separated_iff model _).mp apart⟩
        · cases final
      · cases accepted

/-- The native bundle frame; the meaning is stated over the list framer it equals. -/
theorem acceptsBundleLimited_satisfiable {limits : Limits} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsBundle limits Coverage.BundleLimit.limited files maximumBytes certificate = .ok ()) :
    Coverage.FramerLimit.ByteBundleSatisfiable Coverage.BundleLimit.limitedSpecification files maximumBytes
      Coverage.BundleV8.bundleFuel := by
  rw [Coverage.BundleLimit.limited_eq] at accepted
  exact acceptsBundle_satisfiable accepted

/-! Signed bundle: the role frame, expansion, shape and mode checks of `V3.readBundle`, without the replay. -/

open Roles.Bundle in
def readRoles (frame : Roles.Bundle.V3.Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) :
    Except ModelError (RoleBundle × List Coverage.Item) :=
  match frame files maximumBytes with
  | .error problem => .error (.input problem)
  | .ok bundle =>
    match Coverage.expand (forget bundle) bundleFuel with
    | .error problem => .error (.expand problem)
    | .ok items =>
      if Coverage.FramerV2.wellShaped (forget bundle) bundleFuel then
        if Roles.Bytes.modesValid (entriesOf bundle items) then .ok (bundle, items) else .error .modes
      else .error .shape

open Roles.Bundle in
theorem readRoles_expanded {frame : V3.Frame} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat}
    {read : RoleBundle × List Coverage.Item} (success : readRoles frame files maximumBytes = .ok read) :
    V3.Expanded frame files maximumBytes bundleFuel read.1 read.2 := by
  unfold readRoles at success
  split at success
  · cases success
  · rename_i bundle framed
    split at success
    · cases success
    · rename_i items expanded
      split at success
      · rename_i shaped
        split at success
        · cases success
          exact ⟨framed, shaped, expanded⟩
        · cases success
      · cases success

/-- Every statement of the expanded bundle, whatever its role. -/
def roleStatements (bundle : Roles.Bundle.RoleBundle) (items : List Coverage.Item) : List Formula :=
  (Roles.Bytes.source (Roles.Bundle.entriesOf bundle items)).map Roles.Declaration.original

def acceptsInputs (limits : Limits) (frame : Roles.Bundle.V3.Frame) (files : List (Coverage.Key × List UInt8))
    (maximumBytes : Nat) (certificate : String) : Except ModelError Unit := do
  let read ← readRoles frame files maximumBytes
  if (Roles.Bundle.goalItems read.1 read.2).isEmpty then do
    let model ← readModel limits certificate (roleStatements read.1 read.2)
    let _ ← checkAll limits model ((Roles.positiveInputs (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
      Roles.Declaration.original)
    if separated model (Roles.Bundle.V2.objectsOf read.1 read.2) then pure () else .error .objects
  else .error .goalsPresent

theorem acceptsInputs_satisfiable {limits : Limits} {frame : Roles.Bundle.V3.Frame}
    {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsInputs limits frame files maximumBytes certificate = .ok ()) :
    Roles.Bundle.V3.ByteInputsSatisfiable frame files maximumBytes Roles.Bundle.bundleFuel := by
  obtain ⟨read, readRun, rest⟩ := bind_ok accepted
  have expanded := readRoles_expanded readRun
  split at rest
  · rename_i empty
    obtain ⟨model, _, rest⟩ := bind_ok rest
    obtain ⟨_, checked, final⟩ := bind_ok rest
    split at final
    · rename_i apart
      refine ⟨read.1, read.2, expanded, List.isEmpty_iff.mp empty, model.Element, inferInstance,
        model.interpretation, (separated_iff model _).mp apart, ?_⟩
      intro declaration member
      exact checkAll_sound checked declaration.original (List.mem_map_of_mem member)
    · cases final
  · cases rest

theorem acceptsInputsLimited_satisfiable {limits : Limits} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes : Nat} {certificate : String}
    (accepted : acceptsInputs limits Roles.Bundle.V3.limited files maximumBytes certificate = .ok ()) :
    Roles.Bundle.V3.ByteInputsSatisfiable Roles.Bundle.V3.limitedSpecification files maximumBytes
      Roles.Bundle.bundleFuel := by
  rw [Roles.Bundle.V3.limited_eq] at accepted
  exact acceptsInputs_satisfiable accepted

/-- The countermodel task for the selected conjecture with this index in expansion order, the index the signed
    checker's `--goals` listing prints. Returns that conjecture's bundle item. -/
def acceptsGoal (limits : Limits) (frame : Roles.Bundle.V3.Frame) (files : List (Coverage.Key × List UInt8))
    (maximumBytes index : Nat) (certificate : String) : Except ModelError Coverage.Item := do
  let read ← readRoles frame files maximumBytes
  match (Roles.Bundle.goalItems read.1 read.2)[index]? with
  | none => .error .noGoal
  | some pair => do
    let model ← readModel limits certificate (roleStatements read.1 read.2)
    let left ← checkAll limits model ((Roles.premises (Roles.Bytes.source (Roles.Bundle.entriesOf read.1 read.2))).map
      Roles.Declaration.original)
    match sentenceSteps model pair.2.original.body.formula left with
    | .value false _ =>
      if separated model (Roles.Bundle.V2.objectsOf read.1 read.2) then pure pair.1 else .error .objects
    | .value true _ => .error .goalHolds
    | .scope => .error .goalScope
    | .work => .error .work

theorem acceptsGoal_countermodel {limits : Limits} {frame : Roles.Bundle.V3.Frame}
    {files : List (Coverage.Key × List UInt8)} {maximumBytes index : Nat} {certificate : String}
    {item : Coverage.Item}
    (accepted : acceptsGoal limits frame files maximumBytes index certificate = .ok item) :
    Roles.Bundle.V3.GoalCountermodel frame files maximumBytes Roles.Bundle.bundleFuel item := by
  obtain ⟨read, readRun, rest⟩ := bind_ok accepted
  have expanded := readRoles_expanded readRun
  split at rest
  · cases rest
  · rename_i pair selected
    obtain ⟨model, _, rest⟩ := bind_ok rest
    obtain ⟨_, checked, final⟩ := bind_ok rest
    split at final
    · rename_i computed
      split at final
      · rename_i apart
        cases final
        refine ⟨read.1, read.2, pair.2, expanded, List.mem_of_getElem? selected, model.Element, inferInstance,
          model.interpretation, (separated_iff model _).mp apart, ?_, ?_⟩
        · intro declaration member
          exact checkAll_sound checked declaration.original (List.mem_map_of_mem member)
        · intro holds
          exact absurd ((sentenceSteps_iff computed).mpr holds) (by decide)
      · cases final
    · cases final
    · cases final
    · cases final

theorem acceptsGoalLimited_countermodel {limits : Limits} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes index : Nat} {certificate : String} {item : Coverage.Item}
    (accepted : acceptsGoal limits Roles.Bundle.V3.limited files maximumBytes index certificate = .ok item) :
    Roles.Bundle.V3.GoalCountermodel Roles.Bundle.V3.limitedSpecification files maximumBytes
      Roles.Bundle.bundleFuel item := by
  rw [Roles.Bundle.V3.limited_eq] at accepted
  exact acceptsGoal_countermodel accepted

/-- The SZS CounterSatisfiable statement from one accepted countermodel. -/
theorem acceptsGoalLimited_counterSatisfiable {limits : Limits} {files : List (Coverage.Key × List UInt8)}
    {maximumBytes index : Nat} {certificate : String} {item : Coverage.Item}
    (accepted : acceptsGoal limits Roles.Bundle.V3.limited files maximumBytes index certificate = .ok item) :
    Roles.Bundle.V3.ByteCounterSatisfiable Roles.Bundle.V3.limitedSpecification files maximumBytes
      Roles.Bundle.bundleFuel :=
  ⟨item, acceptsGoalLimited_countermodel accepted⟩

end Fang.TptpCandidate.FullFof.Model
