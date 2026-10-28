import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionStartup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyProgramMain
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionController

namespace OAI.Algorithms

/-! The actual frontend/setup/splitter prefix of the new solver.  The leaf
callback is deliberately left as the only execution service in toExecution;
the numerical setup, normalization and emitted leaf stream are concrete. -/

namespace SubexponentialSAT.SqrtLog.Execution

open BitProgram StructuredCalls SubexpMainProgram Filter
open SubexpSetupProgram (Config mainExtraStacks helperSize)

def phases (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er)
    (leafPhases : Phases er (mainExtraStacks c)) : Phases er (mainExtraStacks c) :=
  { leafPhases with
    setup := Setup.Complete.procedure c er
    sparsify := SparsifyProgram.Main.procedure c hr }

structure Boot (c : Config) (er : ℕ) (hr : 32 ≤ workRegs er)
    {n : ℕ} (F : SubexpOrderedRawPrefix.Formula n) where
  startup : SetupRun c er F
  final : MainState er (mainExtraStacks c)
  leaves : List (ExecSparsifyObserved.Formula n)
  steps : ℕ
  trace : Eval (SparsifyProgram.Main.procedure c hr).invoke steps startup.afterSetup final
  outcome : SubexpOrderedRawSparsify.Outcome c F (SparsifyProgram.Main.M c n)
    startup.afterSetup final leaves

noncomputable def Boot.bootRun {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F)
    (leafPhases : Phases er (mainExtraStacks c)) : BootRun (phases c hr leafPhases) r.startup.before where
  afterSetup := r.startup.afterSetup
  afterSparsify := r.final
  setupSteps := r.startup.setupSteps
  sparsifySteps := r.steps
  setupTrace := r.startup.setupTrace
  sparsifyTrace := r.trace

def Boot.records {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) : List (List Bool) :=
  r.leaves.map ExecSparsifyObserved.encode

theorem Boot.source {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) :
    r.final.stacks (persistent (mainExtraStacks c) 7) = Encoding.encodeList id r.records := by
  rw [show Encoding.encodeList id r.records =
      Encoding.encodeList ExecSparsifyObserved.encode r.leaves from by
        simpa only [Boot.records, Function.comp_def, id_eq] using
          ExecSparsifyEncoding.encodeList_map ExecSparsifyObserved.encode id r.leaves]
  exact r.outcome.leaf_stream

theorem Boot.payload_empty {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) :
    r.final.stacks (persistent (mainExtraStacks c) 8) = [] :=
  (r.outcome.persistent_frame 8 (by decide) (by decide)).trans
    (r.startup.empty 8 (by decide) (by decide) (by decide) (by decide) (by decide))

theorem Boot.correct {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) (test : List Bool → Bool)
    (htest : ∀ G ∈ r.leaves,
      test (ExecSparsifyObserved.encode G) = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) :
    r.records.any test = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F) := by
  rw [r.outcome.satisfiable, List.any_eq_true]
  constructor
  · rintro ⟨bits, hbits, ht⟩
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hbits
    exact ⟨G,hG,(htest G hG).mp ht⟩
  · rintro ⟨G,hG,hSat⟩
    exact ⟨ExecSparsifyObserved.encode G,List.mem_map.mpr ⟨G,hG,rfl⟩,(htest G hG).mpr hSat⟩

/-- The frontend and setup are polynomial in the actual ordered input bits.
The splitter term and both leaf-size bounds concern the same emitted stream. -/
theorem eventually_boot (c : Config) (er : ℕ) (hr : 32 ≤ workRegs er) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧
      ∀ᶠ n : ℕ in atTop, ∀ F : SubexpOrderedRawPrefix.Formula n,
        ExecSunflowerSearch.RawWidthAtMost c.k F →
        ∃ r : Boot c er hr F,
          r.startup.prefixSteps + r.startup.setupSteps ≤
            C*(SubexpOrderedRawPrefix.bitLength F+1)^q ∧
          (r.steps : ℝ) ≤ (workRegs er+3577 : ℕ) *
            (((ExecSparsifyObserved.encode F).length : ℝ)+1)^2 *
            (2 : ℝ)^(130*Statement.runtimeScale n) ∧
          (r.leaves.length : ℝ) ≤ (2 : ℝ)^(129*Statement.runtimeScale n) ∧
          ((Encoding.encodeList ExecSparsifyObserved.encode r.leaves).length : ℝ) ≤
            2*(2 : ℝ)^(130*Statement.runtimeScale n) := by
  obtain ⟨C,q,hC,hq,hsetup⟩ := setup_runs c er
  refine ⟨C,q,hC,hq,?_⟩
  filter_upwards [SparsifyProgram.Main.eventually_invoke c hr] with n hn
  intro F hF
  obtain ⟨start,hstart⟩ := hsetup n F
  have hprep : SparsifyProgram.Main.Prepared c n start.afterSetup := by
    rw [SetupRun.afterSetup, Setup.Complete.install_eq_banks]
    exact SparsifyProgram.Main.prepared_install c start.before start.out start.values.banks
  obtain ⟨steps,final,leaves,ht,hbound,hout,hlen,hbits⟩ :=
    hn F hF start.afterSetup hprep start.body
      (start.empty 7 (by decide) (by decide) (by decide) (by decide) (by decide))
  exact ⟨⟨start,final,leaves,steps,ht,hout⟩,hstart,hbound,hlen,hbits⟩

/-- Closing the actual leaf callback closes the controller execution record.
There is no remaining setup or sparsification oracle in this interface. -/
noncomputable def Boot.toExecution {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F)
    (leafPhases : Phases er (mainExtraStacks c)) (leaf : MainCmd er (mainExtraStacks c))
    (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : MainState er (mainExtraStacks c) → Prop) (validPayload : List Bool → Prop)
    (callback : RecordPrograms.CallbackContractOn (ports er (mainExtraStacks c)) leaf
      test cost invariant validPayload)
    (validRecords : ∀ bits ∈ r.records, validPayload bits) (valid : invariant r.final)
    (test_spec : ∀ G ∈ r.leaves,
      test (ExecSparsifyObserved.encode G) = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) :
    SubexpOrderedRawRuntime.Execution (phases c hr leafPhases) leaf F where
  afterPrefix := r.startup.before
  prefixSteps := r.startup.prefixSteps
  prefixTrace := r.startup.prefixTrace
  boot := r.bootRun leafPhases
  records := r.records
  test := test
  cost := cost
  invariant := invariant
  validPayload := validPayload
  callback := callback
  validRecords := validRecords
  valid := valid
  source := r.source
  payload := r.payload_empty
  correct := r.correct test test_spec

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
