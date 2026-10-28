import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeExecution
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledJet

namespace OAI.Algorithms

/-! The complete ordered node-table execution. The worker is the installed
finite program; its source provenance, canonical jet output, and bound are
derived from the actual Main layout and initialization results. -/

namespace SubexponentialSAT.SubexpOrderedRawScheduledCollector

noncomputable section
set_option quotPrecheck false

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainScheduledLayout SubexpSymbolicCost
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation ordinary)
open SubexpNodeWorkspace

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
  {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
  {a : MainState er (mainExtraStacks cfg)}
  (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
  (ready : DyadicSchedule.Ready cfg.k cfg.T n)
  {G : SubexpLeafData.Leaf n}
  (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
  [NeZero (r n)] (actual : Run alloc hregs a G input ready)

local notation "dim" => SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)
local notation "C" => DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n
  (DyadicSchedule.ready_goodInput ready)
local notation "Physical" => SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual
local notation "Table" => SubexpMainCanonicalJetReadback.table (SubexpOrderedRawScheduledReconstruction.system input)
local notation "Target" => SubexpMainMomentData.target (p n) dim
local notation "Shape" => List.replicate (4*SubexpLiftRing.baseWidth (p n) (dim+1)) false

def jet : Fin ((p n)^4-1) → List Bool :=
  SubexpNodeCanonicalJet.canonicalJetBytes Physical Table

def iterationMax : ℕ := Finset.univ.sup fun i : Fin ((p n)^4-1) =>
  (SubexpOrderedRawScheduledEnumeration.numeric boot initial ready input actual i).iterationCount

theorem iteration_le (i : Fin ((p n)^4-1)) :
    (SubexpOrderedRawScheduledEnumeration.numeric boot initial ready input actual i).iterationCount ≤
      iterationMax boot initial ready input actual :=
  Finset.le_sup (f := fun i : Fin ((p n)^4-1) =>
    (SubexpOrderedRawScheduledEnumeration.numeric boot initial ready input actual i).iterationCount)
    (Finset.mem_univ i)

def workerBound (initialized : MainState er (mainExtraStacks cfg)) : ℕ :=
  SubexpNodeWorkerMasterBound.coefficient *
    (SubexpMainNodeExecution.inputSize C actual.result initialized)^3072 *
    2^(128*dim) * (iterationMax boot initial ready input actual+1)^8

/-- Exact outer-loop cost after using the one bound for every node. -/
def runtimeBound (initialized : MainState er (mainExtraStacks cfg)) : ℕ :=
  22+((p n)^4-1)*(workerBound boot initial ready input actual initialized+
    33*(4*SubexpLiftRing.baseWidth (p n) (dim+1))+
    6*(dim*(4*SubexpLiftRing.baseWidth (p n) (dim+1)))+
    2*(4*SubexpLiftRing.baseWidth (p n) (dim+1))+38)

variable {initialized : MainState er (mainExtraStacks cfg)}


local notation "Masters" => SubexpMainMomentData.store alloc initialized
local notation "HT" => SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready
local notation "HL" => SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready

theorem node_execution
    (hinit : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc actual.out) initialized dim)
    (i : Fin ((p n)^4-1)) (d : State 16 288)
    (hactive : d.stacks = activeStacks Masters (SubexpNodeIndexSemantics.thetaWord (p n) dim i)) :
    ∃ steps ≤ workerBound boot initial ready input actual initialized,
      ∃ out : State 16 288,
        Trace SubexpNodeConcretePipeline.worker steps
          (d.withPC (some SubexpNodeConcretePipeline.worker.entry)) (out.withPC none) ∧
        out.stacks = finalStacks Masters (jet boot initial ready input actual i) Shape := by
  let _ : One (QuarticCode (p n) dim) := ⟨(Target).one⟩
  have hp := SubexpMainLayoutPattern.bounded alloc a G input
    (by have := cfg.width_ge_two; omega)
  have hs : (C).Dstar ≤ dim := by
    rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
    exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready
  have hvalid := SubexpMainLayoutExecution.orderedScopes_valid
    (SubexpMainLayout.Factors.sourceInputs alloc a)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.dimension
  obtain ⟨indexState,basisState,rawState,templateState,out,steps,sourceBytes,family,
    hsteps,htrace,hout,hrel,hbytes,hsize,hindex,htemplated,hraw,hbasis⟩ :=
    SubexpMainNodeExecution.program_runs C rfl actual.result hinit hp hs HT HL i
      hvalid (SubexpOrderedRawScheduledRouting.table_count input)
      (SubexpOrderedRawScheduledRouting.table_answers input) input.R
      (SubexpMainNodeProvenance.reference C rfl actual.result hinit hp hs HT HL i)
      (SubexpMainNodeProvenance.provenance C rfl actual.result hinit hp hs HT HL i hvalid) d hactive
  have hj := SubexpOrderedRawScheduledJet.jet_eq_canonical boot initial ready input actual hinit i family hrel
  refine ⟨steps, ?_, out, htrace, ?_⟩
  · apply hsteps.trans
    unfold workerBound
    gcongr
    exact iteration_le boot initial ready input actual i
  · exact hout.trans (congrArg (fun bits => finalStacks Masters bits Shape) hj)

theorem master_word
    (hinit : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc actual.out) initialized dim) :
    (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).stacks 332 =
      ProgramEncoding.encodeRecords
        (SubexpNodeLiftData.liftedNodeWords (p n) (dim+1)
          (SubexpPreparedQuarticSetup.modulus (p n) 1)) := by
  change (SubexpMainNodeScratch.result alloc initialized).stacks (ordinary alloc 300) = _
  rw [SubexpMainNodeScratch.result_frame alloc initialized (ordinary alloc 300)]
  · have hf := SubexpMainMomentReady.initializer_frame hinit (332 : Fin 352)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    change initialized.stacks (ordinary alloc 300) =
      (SubexpMainNodeSetup.prepared alloc actual.out).stacks (ordinary alloc 300) at hf
    exact hf.trans ((SubexpMainMomentData.prepared_retained (alloc := alloc) (a := actual.out)
      300 (by decide)).trans (SubexpMainMomentData.layout_nodes actual.result))
  · intro he
    have hv := congrArg (fun i : Fin (totalStacks (mainExtraStacks cfg)) => i.val) he
    change (300 : ℕ) = 243 at hv
    omega

theorem program_runs
    (hinit : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc actual.out) initialized dim) :
    ∃ out : State 16 352,
      RunsIn SubexpNodeConcretePipeline.program
        (runtimeBound boot initial ready input actual initialized)
        ((SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).withPC
          (some SubexpNodeConcretePipeline.program.entry)) (out.withPC none) ∧
      SubexpNodeWideLoop.Ready (SubexpNodeWorkspace.Ready Masters) out ∧
      out.stacks 288 = (List.ofFn (SubexpNodeIndexSemantics.thetaWord (p n) dim)).flatten ∧
      out.stacks 297 = (List.ofFn (jet boot initial ready input actual)).flatten ∧
      out.stacks 332 =
        (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).stacks 332 ∧
      out.stacks 333 = [] ∧ out.stacks 334 = [] ∧ out.stacks 335 = [] ∧ out.stacks 336 = [] ∧
      (∀ j : Fin 288, SubexpNodeWideLoop.ProtectedBank j →
        out.stacks (SubexpNodeWideLoop.localPorts j) =
          (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).stacks
            (SubexpNodeWideLoop.localPorts j)) := by
  have he := SubexpNodeIndexedCollector.program_runs (p n) dim
    (SubexpPreparedQuarticSetup.modulus (p n) 1) Masters Shape
    (jet boot initial ready input actual) (workerBound boot initial ready input actual initialized)
    (node_execution boot initial ready input actual hinit)
    (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized))
    (SubexpMainMomentReady.collector_ready hinit) (master_word ready input actual hinit)
    (SubexpMainMomentReady.outer_empty hinit 333 (by decide) (by decide))
    (SubexpMainMomentReady.outer_empty hinit 334 (by decide) (by decide))
    (SubexpMainMomentReady.outer_empty hinit 335 (by decide) (by decide))
    (SubexpMainMomentReady.outer_empty hinit 336 (by decide) (by decide))
    (SubexpMainMomentReady.outer_empty hinit 288 (by decide) (by decide))
    (SubexpMainMomentReady.outer_empty hinit 297 (by decide) (by decide))
  have hc := SubexpNodeUniformBound.indexed_collector_cost (p n) dim
    (workerBound boot initial ready input actual initialized)
    (SubexpPreparedQuarticSetup.modulus (p n) 1) Shape
    (jet boot initial ready input actual) (dim*(4*SubexpLiftRing.baseWidth (p n) (dim+1)))
    (SubexpNodeCanonicalJet.canonicalJetBytes_length Physical Table)
  rw [hc] at he
  simpa only [List.length_replicate, runtimeBound] using he

end
end SubexponentialSAT.SubexpOrderedRawScheduledCollector

end OAI.Algorithms
