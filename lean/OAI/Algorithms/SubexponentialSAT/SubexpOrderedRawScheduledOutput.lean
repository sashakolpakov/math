import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledRows
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentCanonicalOutput

namespace OAI.Algorithms

/-! Typed CRT readback for the actual scheduled layout. The remaining
array equalities are precisely the indexed collector's output obligations. -/

namespace SubexponentialSAT.SubexpOrderedRawScheduledOutput

open SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
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
variable {initialized : MainState er (mainExtraStacks cfg)}
variable (hi : SubexpMainNodeInitialization.Result alloc
  (SubexpMainNodeSetup.prepared alloc actual.out) initialized
  (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))
variable (out : SubexpNodeWideLoop.Data)
variable (outReady : SubexpNodeWideLoop.Ready
  (SubexpNodeWorkspace.Ready (SubexpMainMomentData.store alloc initialized)) out)

include hi outReady in
theorem persistent_frame (i : Fin 32) :
    (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out).stacks
      (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
        actual.out.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) :=
  SubexpMainMomentCanonicalOutput.persistent_frame hi out outReady i

include initial hi outReady in
theorem stored (halloc : alloc.ordinaryCount = helperSize cfg)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    Stored cfg boot.setupOutput B
      (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out) :=
  SubexpMainMomentInvariant.stored hi halloc out
    (SubexpMainMomentCanonicalOutput.modulus_frame out outReady)
    (SubexpMainMomentCanonicalOutput.width_frame out outReady)
    (SubexpOrderedRawScheduledLayout.run_stored boot initial ready input actual halloc hB)

noncomputable def readback (crtAlloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (hnodes : out.stacks 288 =
      (List.ofFn (SubexpNodeIndexSemantics.thetaWord (p n)
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))).flatten)
    (hjets : out.stacks 297 =
      (List.ofFn (SubexpNodeCanonicalJet.canonicalJetBytes
        (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual)
        (SubexpMainCanonicalJetReadback.table
          (SubexpOrderedRawScheduledReconstruction.system input)))).flatten) :
    SubexpMainSystemReadback.Readback (SubexpOrderedRawScheduledReconstruction.system input)
      (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual) crtAlloc
      (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out) := by
  apply SubexpMainMomentCanonicalOutput.readback
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl actual.result hi out outReady
    (SubexpOrderedRawScheduledReconstruction.system input)
    (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual)
    crtAlloc ?_ hnodes hjets input.exponent
  · unfold SubexpLayoutConstruction.dimension
    rw [SubexpMainParameterValues.sourceInputs_dimension_word]
  · intro i
    simp only [SubexpOrderedRawScheduledReconstruction.systemLayout,
      SubexpMainPhysicalLayoutFields.node]
    exact SubexpOrderedRawScheduledLayout.layout_node boot initial ready input actual.result i

theorem reconstruct
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B)
    (crtAlloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (hcrtAlloc : crtAlloc.ordinaryCount = helperSize cfg)
    (phases : Phases er (mainExtraStacks cfg))
    (hlayout : phases.layout = SubexpMainLayoutProgram.procedure er hregs alloc)
    (hcrt : phases.crt = SubexpMainCRT.procedure er crtAlloc)
    (start : MainState er (mainExtraStacks cfg)) (hstart : a = transferredData start)
    (momentSteps : ℕ)
    (momentTrace : StructuredCalls.Eval phases.moments.invoke momentSteps actual.out
      (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out))
    (hnodes : out.stacks 288 =
      (List.ofFn (SubexpNodeIndexSemantics.thetaWord (p n)
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))).flatten)
    (hjets : out.stacks 297 =
      (List.ofFn (SubexpNodeCanonicalJet.canonicalJetBytes
        (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual)
        (SubexpMainCanonicalJetReadback.table
          (SubexpOrderedRawScheduledReconstruction.system input)))).flatten) :
    ∃ original : Layout (E := SubexpActualRing.E (p n))
        (SubexpLEFactorSystem.packed (ell_pos (DyadicSchedule.ready_goodInput ready))
          (p_lower (DyadicSchedule.ready_goodInput ready)).le (ExecCNF.formulaSet G)).toPattern
        (parameters cfg n ready),
      ∃ stages : SubexpLeafContract.ReconstructionStages phases G
          (ell_pos (DyadicSchedule.ready_goodInput ready))
          (p_lower (DyadicSchedule.ready_goodInput ready)).le original start,
        stages.prefixSteps ≤ actual.steps + momentSteps +
          (readback boot initial ready input actual hi out outReady crtAlloc hnodes hjets).bound ∧
        Stored cfg boot.setupOutput B stages.afterCRT :=
  SubexpOrderedRawScheduledReconstruction.complete boot initial ready input actual crtAlloc hcrtAlloc
    phases hlayout hcrt start _ hstart momentSteps momentTrace
    (readback boot initial ready input actual hi out outReady crtAlloc hnodes hjets)
    (stored boot initial ready input actual hi out outReady halloc hB)
    (persistent_frame ready input actual hi out outReady)

end SubexponentialSAT.SubexpOrderedRawScheduledOutput

end OAI.Algorithms
