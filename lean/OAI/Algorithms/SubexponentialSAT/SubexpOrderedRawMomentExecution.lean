import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledCollector
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledOutput

namespace OAI.Algorithms

/-!
# Actual execution of the complete Main moment phase

Initialization, the one-time scratch clear, and the concrete ordered
collector are composed here. The record retains the actual intermediate
state and both component traces used by its runtime bound. Its output
readback is for the same physical factor system and constructed layout.
-/

namespace SubexponentialSAT.SubexpOrderedRawMomentExecution

noncomputable section

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters SubexpMainInvariant
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
  {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
  {a : MainState er (mainExtraStacks cfg)}
  (boot : SubexpOrderedRawBoot.Run cfg hrBoot F)
  (initial : Stored cfg boot.setupOutput B a)
  (ready : DyadicSchedule.Ready cfg.k cfg.T n)
  {G : SubexpLeafData.Leaf n}
  (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
  [NeZero (r n)]
  (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)

local notation "dim" => SubexpLayoutConstruction.dimension
  (SubexpMainLayout.Factors.sourceInputs alloc a)

/-- The stored bounds refer to these very states and actual traces. -/
structure Run where
  initialized : MainState er (mainExtraStacks cfg)
  setupSteps : ℕ
  setupBound : setupSteps ≤ SubexpMainNodeSetup.runtimeBound alloc actual.out dim
  setupTrace : Eval (SubexpMainNodeSetup.procedure er alloc).invoke
    setupSteps actual.out initialized
  initialization : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc actual.out) initialized dim
  out : SubexpNodeWideLoop.Data
  collectorTrace : RunsIn SubexpNodeConcretePipeline.program
    (SubexpOrderedRawScheduledCollector.runtimeBound boot initial ready input actual initialized)
    ((SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).withPC
      (some SubexpNodeConcretePipeline.program.entry)) (out.withPC none)
  outReady : SubexpNodeWideLoop.Ready
    (SubexpNodeWorkspace.Ready (SubexpMainMomentData.store alloc initialized)) out
  nodes : out.stacks 288 =
    (List.ofFn (SubexpNodeIndexSemantics.thetaWord (p n) dim)).flatten
  jets : out.stacks 297 =
    (List.ofFn (SubexpOrderedRawScheduledCollector.jet boot initial ready input actual)).flatten
  nodeMaster : out.stacks 332 =
    (SubexpMainMoments.projected alloc
      (SubexpMainNodeScratch.result alloc initialized)).stacks 332
  cleared333 : out.stacks 333 = []
  cleared334 : out.stacks 334 = []
  cleared335 : out.stacks 335 = []
  cleared336 : out.stacks 336 = []
  protectedFrame : ∀ j : Fin 288, SubexpNodeWideLoop.ProtectedBank j →
    out.stacks (SubexpNodeWideLoop.localPorts j) =
      (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).stacks
        (SubexpNodeWideLoop.localPorts j)
  steps : ℕ
  bound : steps ≤ setupSteps + SubexpMainNodeScratch.runtimeBound alloc initialized +
    SubexpOrderedRawScheduledCollector.runtimeBound boot initial ready input actual initialized + 2
  trace : Eval (SubexpMainMoments.procedure er alloc).invoke steps actual.out
    (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out)

theorem run_exists : Nonempty (Run boot initial ready input actual) := by
  obtain ⟨setupSteps, hsetupBound, initialized, hsetup, hi⟩ :=
    SubexpMainMomentOutput.setup_execution actual.result
  obtain ⟨out, hcollector, hout, hnodes, hjets, hmaster,
    h333, h334, h335, h336, hprotected⟩ :=
    SubexpOrderedRawScheduledCollector.program_runs boot initial ready input actual hi
  obtain ⟨steps, hbound, htrace⟩ := SubexpMainMoments.compose_runs alloc actual.out initialized out
    setupSteps (SubexpOrderedRawScheduledCollector.runtimeBound boot initial ready input actual initialized)
    hsetup hcollector
  exact ⟨{
    initialized := initialized
    setupSteps := setupSteps
    setupBound := hsetupBound
    setupTrace := hsetup
    initialization := hi
    out := out
    collectorTrace := hcollector
    outReady := hout
    nodes := hnodes
    jets := hjets
    nodeMaster := hmaster
    cleared333 := h333
    cleared334 := h334
    cleared335 := h335
    cleared336 := h336
    protectedFrame := hprotected
    steps := steps
    bound := hbound
    trace := htrace }⟩

variable (run : Run boot initial ready input actual)

def Run.finalState : MainState er (mainExtraStacks cfg) :=
  SubexpMainMoments.installed alloc
    (SubexpMainNodeScratch.result alloc run.initialized) run.out

def Run.runtimeBound : ℕ :=
  SubexpMainNodeSetup.runtimeBound alloc actual.out dim +
    SubexpMainNodeScratch.runtimeBound alloc run.initialized +
    SubexpOrderedRawScheduledCollector.runtimeBound boot initial ready input actual run.initialized + 2

theorem Run.steps_le : run.steps ≤ run.runtimeBound := by
  have hb := run.bound
  have hs := run.setupBound
  dsimp only [Run.runtimeBound]
  omega

theorem Run.execution :
    Eval (SubexpMainMoments.procedure er alloc).invoke run.steps actual.out run.finalState :=
  run.trace

def Run.readback (crtAlloc : SubexpMainCRT.Allocation (mainExtraStacks cfg)) :
    SubexpMainSystemReadback.Readback (SubexpOrderedRawScheduledReconstruction.system input)
      (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual)
      crtAlloc run.finalState :=
  SubexpOrderedRawScheduledOutput.readback boot initial ready input actual run.initialization
    run.out run.outReady crtAlloc run.nodes run.jets

theorem Run.persistent_frame (i : Fin 32) :
    (run.finalState).stacks (persistent (mainExtraStacks cfg) i) =
      actual.out.stacks (persistent (mainExtraStacks cfg) i) :=
  SubexpOrderedRawScheduledOutput.persistent_frame ready input actual run.initialization
    run.out run.outReady i

theorem Run.stored (halloc : alloc.ordinaryCount = helperSize cfg)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    Stored cfg boot.setupOutput B run.finalState :=
  SubexpOrderedRawScheduledOutput.stored boot initial ready input actual run.initialization
    run.out run.outReady halloc hB

end
end SubexponentialSAT.SubexpOrderedRawMomentExecution

#print axioms SubexponentialSAT.SubexpOrderedRawMomentExecution.run_exists
#print axioms SubexponentialSAT.SubexpOrderedRawMomentExecution.Run.readback

end OAI.Algorithms
