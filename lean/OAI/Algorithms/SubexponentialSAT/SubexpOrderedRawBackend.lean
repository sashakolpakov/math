import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawMomentExecution
import OAI.Algorithms.SubexponentialSAT.SubexpMainFixedProgram

namespace OAI.Algorithms

/-! Actual execution of the fixed layout, moment and CRT phases on one
nonempty sparse leaf. The uniform time estimate is a separate theorem. -/

namespace SubexponentialSAT.SubexpOrderedRawBackend

open SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainInvariant

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable (hsize : 672 ≤ helperSize cfg)
variable {F : SubexpOrderedRawPrefix.Formula n} {a : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready (SubexpMainFixedProgram.allocation cfg hsize)
  a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable (start : MainState er (mainExtraStacks cfg))

structure Run where
  layout : SubexpMainScheduledLayout.Run (SubexpMainFixedProgram.allocation cfg hsize)
    hregs a G input ready
  moments : SubexpOrderedRawMomentExecution.Run boot initial ready input layout
  original : Layout (E := SubexpActualRing.E (p n))
    (SubexpLEFactorSystem.packed (ell_pos (DyadicSchedule.ready_goodInput ready))
      (p_lower (DyadicSchedule.ready_goodInput ready)).le (ExecCNF.formulaSet G)).toPattern
    (SubexpMainScheduledLayout.parameters cfg n ready)
  stages : SubexpLeafContract.ReconstructionStages
    (SubexpMainFixedProgram.phases cfg hsize er hregs) G
    (ell_pos (DyadicSchedule.ready_goodInput ready))
    (p_lower (DyadicSchedule.ready_goodInput ready)).le original start
  prefixBound : stages.prefixSteps ≤ layout.steps + moments.steps +
    (SubexpOrderedRawMomentExecution.Run.readback boot initial ready input layout moments
      (SubexpMainFixedProgram.crtAllocation cfg hsize)).bound
  stored : Stored cfg boot.setupOutput B stages.afterCRT

theorem run_exists (hstart : a = transferredData start)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    Nonempty (Run (hregs := hregs) hsize boot initial ready input start) := by
  obtain ⟨layout⟩ := SubexpMainScheduledLayout.run_exists (hregs := hregs) ready input
  obtain ⟨moments⟩ := SubexpOrderedRawMomentExecution.run_exists boot initial ready input layout
  obtain ⟨original, stages, hcost, hstored⟩ := SubexpOrderedRawScheduledReconstruction.complete
    boot initial ready input layout (SubexpMainFixedProgram.crtAllocation cfg hsize) rfl
    (SubexpMainFixedProgram.phases cfg hsize er hregs) rfl rfl
    start moments.finalState hstart moments.steps moments.execution
    (SubexpOrderedRawMomentExecution.Run.readback boot initial ready input layout moments
      (SubexpMainFixedProgram.crtAllocation cfg hsize))
    (SubexpOrderedRawMomentExecution.Run.stored boot initial ready input layout moments rfl hB)
    moments.persistent_frame
  exact ⟨⟨layout, moments, original, stages, hcost, hstored⟩⟩

/-- No layout, worker, output array or reconstruction execution is assumed
at this entry point. The input is the actual transferred sparse leaf. -/
theorem transferred_run_exists
    (base : MainState er (mainExtraStacks cfg))
    (invariant : Invariant cfg boot.setupOutput B base)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (hne : [] ∉ G) (tail : List Bool)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    let start := leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)
    let initial := stored_transferred_input base invariant.toStored tail
      (ExecQuantitativeSparsify.encodeRawFormula G)
    let input := SubexpOrderedRawLayoutInput.ready_transferred
      (SubexpMainFixedProgram.allocation cfg hsize) rfl boot base invariant
      (DyadicSchedule.ready_goodInput ready) G valid hne tail
    Nonempty (Run (hregs := hregs) hsize boot initial ready input start) := by
  dsimp only
  exact run_exists hsize boot _ ready _ _ rfl hB

end SubexponentialSAT.SubexpOrderedRawBackend

end OAI.Algorithms
