import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledLayout

namespace OAI.Algorithms

/-!
# From the scheduled layout and its actual moments to the original leaf

The remaining input is the readback of the concrete moment computation for
the same table-bearing factor system. Reconstruction and both dimension
transports preserve the actual machine states and measured prefix cost.
-/

namespace SubexponentialSAT.SubexpOrderedRawScheduledReconstruction

open StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainScheduledLayout
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
variable {a : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable (actual : Run alloc hregs a G input ready)

noncomputable abbrev system := SubexpMainPhysicalSystem.system
  (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
  input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension

noncomputable abbrev systemLayout :
    Layout (E := SubexpActualRing.E (p n)) (system input).toPattern (parameters cfg n ready) :=
  SubexpMainPhysicalSystem.layout
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (SubexpOrderedRawScheduledLayout.runLayout boot initial ready input actual)

theorem complete
    (crtAlloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (halloc : crtAlloc.ordinaryCount = helperSize cfg)
    (phases : Phases er (mainExtraStacks cfg))
    (hlayout : phases.layout = SubexpMainLayoutProgram.procedure er hregs alloc)
    (hcrt : phases.crt = SubexpMainCRT.procedure er crtAlloc)
    (start afterMoments : MainState er (mainExtraStacks cfg))
    (hstart : a = transferredData start) (momentSteps : ℕ)
    (momentTrace : Eval phases.moments.invoke momentSteps actual.out afterMoments)
    (readback : SubexpMainSystemReadback.Readback (system input)
      (systemLayout boot initial ready input actual) crtAlloc afterMoments)
    (stored : Stored cfg boot.setupOutput B afterMoments)
    (frame : ∀ i : Fin 32,
      afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
        actual.out.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i)) :
    ∃ original : Layout (E := SubexpActualRing.E (p n))
        (SubexpLEFactorSystem.packed (ell_pos (DyadicSchedule.ready_goodInput ready))
          (p_lower (DyadicSchedule.ready_goodInput ready)).le (ExecCNF.formulaSet G)).toPattern
        (parameters cfg n ready),
      ∃ stages : SubexpLeafContract.ReconstructionStages phases G
          (ell_pos (DyadicSchedule.ready_goodInput ready))
          (p_lower (DyadicSchedule.ready_goodInput ready)).le original start,
        stages.prefixSteps ≤ actual.steps + momentSteps + readback.bound ∧
        Stored cfg boot.setupOutput B stages.afterCRT := by
  have hl : Eval phases.layout.invoke actual.steps (transferredData start) actual.out := by
    rw [hlayout, ← hstart]
    exact actual.trace
  have hf (i : Fin 32) (hi : i ∉ SubexpMainCacheSetup.changedPersistent) :
      afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
        (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) :=
    (frame i).trans ((SubexpMainLayoutStored.persistent_frame actual.result i hi).trans
      (congrArg (fun b : MainState er (mainExtraStacks cfg) =>
        b.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i)) hstart))
  have hn : 0 < SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a) := by
    rw [input.variableCount]
    have h := goodInput_two_le (DyadicSchedule.ready_goodInput ready)
    omega
  obtain ⟨nativeLayout, nativeStages, hb, hs⟩ := SubexpMainPhysicalSystem.complete
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (by have := cfg.width_ge_two; omega) input.sparse input.no_empty input.delta
    (SubexpOrderedRawScheduledLayout.runLayout boot initial ready input actual) crtAlloc halloc phases hcrt
    start actual.out afterMoments actual.steps momentSteps hl momentTrace readback stored
    (hf 7 (by decide)) (hf 8 (by decide)) (hf 9 (by decide)) hn
  obtain ⟨original, stages, _, _, hstate, hsteps⟩ := SubexpMainPhysicalSystem.cast_back G
    input.variableCount.symm (SubexpOrderedRawParameterValues.sourceInputs_ell alloc boot initial).symm
    (ell_pos (DyadicSchedule.ready_goodInput ready))
    (p_lower (DyadicSchedule.ready_goodInput ready)).le input.ell_pos input.capacity
    phases start nativeLayout nativeStages
  refine ⟨original, stages, ?_, ?_⟩
  · rw [hsteps]
    exact hb
  · rw [hstate]
    exact hs

end SubexponentialSAT.SubexpOrderedRawScheduledReconstruction

end OAI.Algorithms
